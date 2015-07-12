using QuickGraph;
using PHPAnalysis.Data.CFG;
using System.Linq;

namespace PHPAnalysis
{
	public interface ICFGCTLPreparation
	{
		void AddSelfLoops (BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> graph);
	}

	public sealed class CFGCTLPreparation : ICFGCTLPreparation
	{
		//Preparation for CTL requires all nodes without an outgoing edge to have a loop to self

		public void AddSelfLoops (BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> graph)
		{
			foreach (var vertex in graph.Vertices)
			{
				if (!graph.OutEdges(vertex).Any())
				{
					graph.AddEdge (new TaggedEdge<CFGBlock, EdgeTag> (vertex, vertex, new EdgeTag (EdgeType.Normal)));
				}
			}
		}
	}
}