using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Collections.Concurrent;
using System.Threading.Tasks;
using System.Xml;
using PHPAnalysis.Analysis.AST;
using PHPAnalysis.Analysis.PHPDefinitions;
using PHPAnalysis.Components;
using PHPAnalysis.Configuration;
using PHPAnalysis.Data;
using PHPAnalysis.Data.CFG;
using PHPAnalysis.Parsing;
using PHPAnalysis.Parsing.AstTraversing;
using PHPAnalysis.Utils;
using File = PHPAnalysis.Data.File;
using PHPAnalysis.Analysis.CTLLTL;

[assembly: InternalsVisibleTo ("PHPAnalysis.Tests")]
namespace PHPAnalysis
{

	public static class CTLLTLProgram
	{
		//HACK: there must be a better way to handle this ! :O
		public static Config Configuration;

		public static void CTLLTLMain (Arguments args, Config conf)
		{
			Arguments arguments = args;

			if (arguments.Result == null || arguments.Main == null)
			{
				Console.WriteLine("Result dir and Main file must be specified");
				Environment.Exit(1);
			}

			Configuration = conf;
			Config configuration = Configuration;

			Analyze (arguments, configuration);
		}

		private static void Analyze (Arguments arguments, Config configuration)
		{
			Console.WriteLine ("Parsing project at: " + arguments.Target);
			Console.WriteLine ();

			var stopwatch = Stopwatch.StartNew ();

			Console.WriteLine ("Building ASTs..");
			ParseResult parseResult = ParseTarget (arguments, configuration);

			Console.WriteLine (" - AST build for " + parseResult.ParsedFiles.Count + " files (" + parseResult.FilesThatFailedToParse.Count + " failed)..");
			Console.WriteLine ("Traversing ASTs..");

			var filesCollection = new List<File> ();

			foreach (var parsedFile in parseResult.ParsedFiles) {
				ExtractFunctions (parsedFile);
			}

			/*Parallel.ForEach(parseResult.ParsedFiles,parsedFile =>
			{
				ExtractFunctions(parsedFile);
			});*/

			var bag = new ConcurrentBag<File> ();
			Parallel.ForEach (parseResult.ParsedFiles, parsedFile => {
				Console.WriteLine ("File: " + parsedFile.Key);

				var file = BuildFileCFGAndExtractFileInformation (parsedFile);
				bag.Add (file);
			});
			
			filesCollection.AddRange (bag);

			Console.WriteLine ("Creating CTLLTL Model...");
			File mainfile = filesCollection.Find (x => x.Name == arguments.Main);
			IncludeResolver ir = new IncludeResolver (filesCollection);
			var c = new CTLLTL ();
			string p = Path.Combine (arguments.Result, "graph-ctl");
			mainfile.CFG.VisualizeGraph (p, Configuration.GraphSettings);
			c.makeModel ((QuickGraph.BidirectionalGraph<CFGBlock, QuickGraph.TaggedEdge<CFGBlock, EdgeTag>>)mainfile.CFG, ir, Path.Combine (arguments.Result, "model.smv"));
			stopwatch.Stop ();
			Console.WriteLine ("Time spent: " + stopwatch.Elapsed);
		}

		private static void ExtractFunctions (KeyValuePair<string, XmlDocument> parsedFile)
		{
			var traverser = new XmlTraverser ();
			var extractor = new ClassAndFunctionExtractor ();
			traverser.AddVisitor (extractor);
			traverser.Traverse (parsedFile.Value.FirstChild.NextSibling);
			FunctionsHandler.Instance.CustomFunctions.AddRange (extractor.Functions);
			foreach (var @class in extractor.Classes) {
				foreach (var method in @class.Methods) {
					//HACK: This is not a good way to handle this! Should we add a new derived function class called method that includes the class name
					//-||-: and make a special list for them in the function handler, or is this okay?
					method.Name = @class.Name + "->" + method.Name;
					FunctionsHandler.Instance.CustomFunctions.Add (method);
				}
			}
		}

		private static File BuildFileCFGAndExtractFileInformation (KeyValuePair<string, XmlDocument> parsedFile)
		{
			var traverser = new XmlTraverser ();
			var metricAnalyzer = new MetricVisitor ();
			var extractor = new ClassAndFunctionExtractor ();
			var printer = new ASTPrinter (Console.Out);
			var cfgcreator = new SuperCFGCreator ();

			traverser.AddVisitor (extractor);
			traverser.AddVisitor (metricAnalyzer);

			traverser.Traverse (parsedFile.Value.FirstChild.NextSibling);
			cfgcreator.Traverse (parsedFile.Value.FirstChild.NextSibling);

			var ctlPrep = new CFGCTLPreparation ();
			ctlPrep.AddSelfLoops (cfgcreator.Graph);

			File file = new File (parsedFile.Value) {
				CFG = cfgcreator.Graph,
				FullPath = parsedFile.Key,
				Interfaces = extractor.Interfaces.GroupBy (i => i.Name, i => i).ToDictionary (i => i.Key, i => i.ToList ()),
				Classes = extractor.Classes.GroupBy (c => c.Name, c => c).ToDictionary (c => c.Key, c => c.ToList ()),
				Closures = extractor.Closures.ToArray (),
				Functions = extractor.Functions.GroupBy (i => i.Name, i => i).ToDictionary (i => i.Key, i => i.ToList ())
			};
			return file;
		}

		private static ParseResult ParseTarget (Arguments arguments, Config configuration)
		{
			if (Directory.Exists (arguments.Target)) {
				return ParseDirectoryFiles (configuration, arguments);
			}
			if (System.IO.File.Exists (arguments.Target)) {
				return ParseFile (configuration, arguments);
			}
			Console.WriteLine ("Target does not seem to be a valid directory or file.");
			Environment.Exit (1);
			return null;
		}

		private static ParseResult ParseFile (Config configuration, Arguments arguments)
		{
			var fileParser = new FileParser (configuration.PHPSettings.PHPParserPath);
			var result = fileParser.ParsePHPFile (arguments.Target);
			var parseResult = new ParseResult ();
			parseResult.ParsedFiles.Add (arguments.Target, result);
			return parseResult;
		}

		private static ParseResult ParseDirectoryFiles (Config configuration, Arguments arguments)
		{
			var projectParser = new ProjectParser (arguments.Target, configuration.PHPSettings);
			ParseResult parseResult = projectParser.ParseProjectFiles ();
			return parseResult;
		}

		private static ComponentContainer ImportExternalComponents (ComponentConfiguration configuration)
		{
			if (!configuration.IncludeComponents) {
				return new ComponentContainer ();
			}
			try {
				var importer = new ComponentImporter ();
				var components = importer.ImportComponents (configuration.ComponentPath);

				Console.WriteLine ("Components:");
				Console.WriteLine ("  Found " + components.AstVisitors.Count + " visitors.");
				Console.WriteLine ("  Found " + components.BlockAnalyzers.Count + " block analyzers.");
				Console.WriteLine ("  Found " + components.VulnerabilityReporters.Count + " reporters.");

				return components;
			} catch (DirectoryNotFoundException) {
				Console.WriteLine ("EXTERNAL COMPONENTS ERROR: ");
				Console.WriteLine ("Could not find specified component folder (" + configuration.ComponentPath + "). Please make sure to set the correct folder in the config file.");
				Environment.Exit (1);
				return null;
			}
		}

		private static void PrintResults (File file, MetricVisitor metricAnalyzer, TextWriter writer)
		{
			writer.WriteLine ("File: " + file.FullPath);
			writer.WriteLine (" - Total AST nodes: " + metricAnalyzer.TotalNodes);
			writer.WriteLine (" - Echo statements: " + metricAnalyzer.EchoStatements);
			writer.WriteLine (" - Sql query strings: " + metricAnalyzer.PotentialSQLQueries);
			writer.WriteLine (" - Functions: " + file.Functions.Count);
			foreach (var function in file.Functions.Values) {
				writer.WriteLine ("   - " + function);
			}
			writer.WriteLine (" - Classes: " + file.Classes.Count);
			foreach (var classDef in file.Classes.Values.SelectMany(classDefinition => classDefinition)) {
				writer.WriteLine ("   - " + classDef.Name + " " + classDef.StartLine + " " + classDef.EndLine);
				writer.WriteLine ("     - Methods: " + classDef.Methods.Count);
			}
			writer.WriteLine (" - Interfaces: " + file.Interfaces.Count);
			foreach (var interfaceDef in file.Interfaces.Values.SelectMany(interfaceDef => interfaceDef)) {
				writer.WriteLine ("  - " + interfaceDef.Name + " " + interfaceDef.StartLine + " " + interfaceDef.EndLine);
				writer.WriteLine ("    - Methods: " + interfaceDef.Methods.Count);
			}
			writer.WriteLine (" - Closures: " + file.Closures.Length);
			foreach (var closure in file.Closures) {
				writer.WriteLine ("   - " + closure);
			}

			writer.WriteLine ();
		}
	}
}