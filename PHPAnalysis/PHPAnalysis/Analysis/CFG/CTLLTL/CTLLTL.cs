using System;
using QuickGraph;
using PHPAnalysis.Data.CFG;
using System.Threading;
using System.Threading.Tasks;
using QuickGraph.Algorithms;
using System.Linq;
using PHPAnalysis.Utils;
using System.Collections;
using System.Collections.Generic;
using PHPAnalysis.Data;
using PHPAnalysis.Utils.XmlHelpers;
using PHPAnalysis.Analysis.AST;
using PHPAnalysis.Data;
using File = PHPAnalysis.Data.File;
using System.Diagnostics;


namespace PHPAnalysis.Analysis.CTLLTL
{
	public class CTLLTL
	{
		
		private BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> graph;
		private List<CTLLTLNode> nodeList = new List<CTLLTLNode> ();
		private IncludeResolver resolver;
		

		//Simple proof-of-concept list of functions to watch out for
		private readonly string[] _AlertFunctions = {
			//Filters
	//		"add_filter",
	//		"remove_filter",
			
			//Upload
			"move_uploaded_file",

			//XSS
			"htmlentities",
			"htmlspecialchars",
			"preg_match",

			//SQL Injection
			"mysqli_real_escape_string",
			"mysql_real_escape_string"
		};

		public CTLLTL ()
		{
		}

		private HashSet<string> filterList = new HashSet<string> ();

		private void GetBlockName (CTLLTLNode block)
		{
			string nodeName = (nodeList.Count + 1).ToString ();
			if (block.block.IsSpecialBlock || block.block.AstEntryNode == null) {
				
			} else {
				switch (block.block.AstEntryNode.LocalName) {
				case (AstConstants.Nodes.Expr_FuncCall):
				case (AstConstants.Nodes.Expr_MethodCall):
					string methodName = "";
					try{methodName = block.block.AstEntryNode.GetSubNode (AstConstants.Subnode + ":" + AstConstants.Subnodes.Name).FirstChild.GetSubNode (AstConstants.Subnode + ":" + AstConstants.Subnodes.Parts).InnerText;} catch (Exception e){};
					if (methodName == "add_filter") {
						var filterName = block.block.AstEntryNode.GetSubNode (AstConstants.Subnode + ":" + AstConstants.Subnodes.Args)
							.FirstChild.FirstChild
							.GetSubNode (AstConstants.Subnode + ":" + AstConstants.Subnodes.Value).FirstChild.LastChild.InnerText;
						block.methodName = methodName;
						block.filterName = filterName;
						filterList.Add (filterName);
					} else
						block.methodName = methodName;
					nodeName = nodeName + "Call_" + block.methodName;
					break;
				default:
					nodeName = nodeName + block.block.AstEntryNode.LocalName.ToLower ();
					break;
				}
				//Handle the harder cases!
			}
			block.nodeName = nodeName;
		}

		//HashSet<CFGBlock> CnodesVisited = new HashSet<CFGBlock>();
		private CTLLTLNode MakeCNode (CFGBlock block)
		{
			
			var v = Stopwatch.StartNew();
			if (nodeList.Exists (x => x.block == block))
				return null;
			v.Stop();

			var cNode = new CTLLTLNode ();
			cNode.block = block;
			GetBlockName (cNode);
			cNode.nodeName = nodeList.Count + 1 + "";
			nodeList.Add (cNode);
			//CnodesVisited.Add(cNode.block);
			if (cNode.block.AstEntryNode != null && (nodeList.Count % 1000) == 0)
				Console.WriteLine("Added node: " + cNode.block.AstEntryNode.LocalName + " total in list: " + nodeList.Count + " Loop took: " + v.Elapsed);
			return cNode;
		}


		//Really not a pretty way to make this, but it works
		private void WriteToFile (string path)
		{
			using (System.IO.StreamWriter file = new System.IO.StreamWriter (path)) {
				string s = "    ";
				string states = "";
				Console.WriteLine("Writing var declarations...");
				foreach (var v in nodeList)
					states += v.nodeName + ",";
				states = states.Remove (states.Length - 1); //Remove the last ,

				file.WriteLine ("MODULE main");
				file.WriteLine ();
				file.WriteLine ("VAR");
				file.WriteLine (s + "state: {" + states + "};");

				foreach (var v in _AlertFunctions) {
					file.WriteLine (s + v + " : boolean;");
				}

				foreach (var v in filterList) {
					file.WriteLine (s + "af_" + v + ": boolean;");
					file.WriteLine (s + "rf_" + v + ": boolean;");
				}

				Console.WriteLine("Writing Assignments...");
				file.WriteLine ();
				file.WriteLine ("ASSIGN");
				file.WriteLine (s + "init(state) := " + nodeList [0].nodeName + ";");
				foreach (var v in _AlertFunctions) {
					file.WriteLine (s + "init(" + v + ") := FALSE;");
				}

				foreach (var v in filterList) {
					file.WriteLine (s + "init(af_" + v + ") := FALSE;");
					file.WriteLine (s + "init(rf_" + v + ") := FALSE;");
				}

				Console.WriteLine("Writing state if's");
				file.WriteLine ();
				file.WriteLine ("next(state) := case");
				foreach (var v in nodeList) {
					file.WriteLine (s + v.nodeText);
				}

				file.WriteLine (s + "esac;");

				Console.WriteLine("Writing filters and alert functions...");
				WriteSpecialStuff (file);

				Console.WriteLine("Generating Specification..");
				GenSpec (file);
			}
		}

		private void GenSpec (System.IO.StreamWriter file)
		{
			file.WriteLine();
			foreach (var s in _AlertFunctions)
			{
				file.WriteLine("SPEC AG(" + s +" = FALSE);");
			}

			foreach (var filter in filterList)
			{
				file.WriteLine("SPEC AG(EF(af_" + filter + " = TRUE -> rf_" +filter+" = TRUE));");
			}
		}
		private void WriteSpecialStuff (System.IO.StreamWriter file)
		{
			Console.WriteLine("Functions...");
			foreach (string node in _AlertFunctions) {
				List<CTLLTLNode> list = nodeList.FindAll (v => v.methodName == node);
				file.WriteLine ();
				file.WriteLine ("next(" + node + ") := case");
				foreach (var q in list) {
					file.WriteLine ("state" + "=" + q.nodeName + " : TRUE;");
				}
				file.WriteLine ("TRUE : " + node + ";");
				file.WriteLine ("esac;");
			}

			Console.WriteLine("Filters...");
			foreach (string filtername in filterList) {
				List<CTLLTLNode> nlist = nodeList.FindAll (v => v.filterName == filtername && v.methodName == "add_filter");
				file.WriteLine ("next(af_" + filtername + ") := case");  
				foreach (var node in nlist) {
					file.WriteLine ("state =" + node.nodeName + " : TRUE;");
				}
				file.WriteLine ("TRUE : af_" + filtername + ";");
				file.WriteLine ("esac;");

				nlist = nodeList.FindAll (v => v.filterName == filtername && v.methodName == "remove_filter");
				file.WriteLine ("next(rf_" + filtername + ") := case");  
				foreach (var node in nlist) {
					file.WriteLine ("state =" + node.nodeName + " : TRUE;");
				}
				file.WriteLine ("TRUE : rf_" + filtername + ";");
				file.WriteLine ("esac;");
			}
		}

		private void GenerateIf ()
		{
			//This was slow before... now it is significantly quicker
			Parallel.ForEach(nodeList, cNode => {
				var v = Stopwatch.StartNew();
				cNode.nodeText = "(state=" + cNode.nodeName + ") : {";
				foreach (var edge in cNode.graph.OutEdges(cNode.block)) {
					cNode.nodeText += nodeList.Find (x => x.block == edge.Target).nodeName + ",";
				}
				cNode.nodeText = cNode.nodeText.Remove (cNode.nodeText.Length - 1); //Remove last ,
				cNode.nodeText += "};";

				v.Stop();
				int number;
				bool result = Int32.TryParse(cNode.nodeName, out number);
				if (result && (number % 1000) == 0)
					Console.WriteLine("Generated if for node: " + cNode.nodeName + " of " + nodeList.Count + " it took: " + v.Elapsed);
			});
		}


		HashSet<CFGBlock> visited = new HashSet<CFGBlock> ();
		HashSet<File> inFile = new HashSet<File>();
		int BFSRUNS = 1;
		int activebfs = 1;
		private void BFS (CFGBlock root, BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> _graph)
		{
			Console.WriteLine("Total BFS recursions: " + BFSRUNS + " Active BFS: " + activebfs + " nodes currently in graph: " + nodeList.Count);
			BFSRUNS++;
			activebfs++;
			Queue<CFGBlock> queue = new Queue<CFGBlock> ();
			queue.Enqueue (root);
			while (queue.Any ()) {
				var node = queue.Dequeue ();
				if (visited.Contains(node))
					continue;
				visited.Add (node);
				var cNode = MakeCNode (node);
				if (cNode != null)
					cNode.graph = _graph;

				if (node.AstEntryNode != null && node.AstEntryNode.LocalName == AstConstants.Nodes.Expr_Include) {
					File output = null;
					resolver.TryResolveInclude (node.AstEntryNode, out output);
					if (output != null && !inFile.Contains(output)) {
						var _root = output.CFG.Roots ().Single (v => v.IsSpecialBlock);
						inFile.Add(output);
						//Console.WriteLine("Recursive call: " + output.Name);
						BFS (_root, (BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>>)output.CFG);
						//Console.WriteLine("Finished call: " + output.Name);
						//Console.WriteLine("Still " + inFile.Count() + " files left");
						inFile.Remove(output);
					}
				}

				foreach (var edge in _graph.OutEdges(node))
					if (!visited.Contains (edge.Target)) //No loops, please
						queue.Enqueue (edge.Target);
			}
			activebfs--;
		}

		public void makeModel (BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> graph, IncludeResolver resolver, string path)
		{
			this.graph = graph;
			this.resolver = resolver;
			var root = graph.Roots ().Single (v => v.IsSpecialBlock);

			BFS (root, this.graph);

			Console.WriteLine("Finished BFS Traversal, generating if sentences...");
			GenerateIf ();

			Console.WriteLine("Writing to file...");
			WriteToFile (path);
		}
	}
}

