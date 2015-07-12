using System;
using PHPAnalysis.Data.CFG;
using QuickGraph;

namespace PHPAnalysis
{
	public class CTLLTLNode
	{
		public CFGBlock block { get; set; }

		public string nodeName { get; set; }

		public string nodeText { get; set; }

		public string methodName = null;

		public string filterName = null;

		public BidirectionalGraph<CFGBlock, TaggedEdge<CFGBlock, EdgeTag>> graph;
	}
}

