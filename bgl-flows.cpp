#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

// ALGOLAB BGL Tutorial 2
// Flow example demonstrating
// - interior graph properties for flow algorithms
// - custom edge adder

// Compile and run with one of the following:
// g++ -std=c++11 -O2 flows.cpp -o flows ./flows
// g++ -std=c++11 -O2 -I path/to/boost_1_58_0 flows.cpp -o flows; ./flows

// Includes
// ========
// STL includes
#include <iostream>
#include <vector>
#include <queue>
#include <stack>
#include <algorithm>
#include <cstdio>
#include <string>
// BGL includes
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/prim_minimum_spanning_tree.hpp>
#include <boost/graph/kruskal_min_spanning_tree.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/push_relabel_max_flow.hpp>
#include <boost/graph/edmonds_karp_max_flow.hpp>
#include <boost/graph/cycle_canceling.hpp>
#include <boost/graph/successive_shortest_path_nonnegative_weights.hpp>
#include <boost/graph/find_flow_cost.hpp>
#include <boost/graph/copy.hpp>
// Namespaces
// using namespace std;
using namespace boost;

#define _i std::cin
#define _o std::cout
#define _l std::endl
#define _e std::cerr

void Marathon2();


// Main function to loop over the testcases
int main(int argc, char** argv) {
	std::ios_base::sync_with_stdio(false);	
	if (argc > 1) {
		std::string str("C:\\some-path\\");
		str += std::string(argv[1]) + ".in";
		freopen(str.c_str(), "r", stdin);
	}
	else freopen("C:\\some-path\\test0.in", "r", stdin);
	freopen("C:\\some-path\\out_my.out", "w", stdout);
	freopen("C:\\some-path\\err_my.out", "w", stderr);
	int T;	_i >> T;
	for (; T > 0; --T)	Marathon2();
	return 0;
}

//
// BGL Graph definitions
// =====================
// Graph Type with nested interior edge properties for Flow Algorithms
typedef	boost::adjacency_list_traits<boost::vecS, boost::vecS, boost::directedS> Traits;
typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS, boost::no_property,
	boost::property<boost::edge_capacity_t, long,
	boost::property<boost::edge_residual_capacity_t, long,
	boost::property<boost::edge_reverse_t, Traits::edge_descriptor,
	boost::property<boost::edge_weight_t, long> > > > >	Graph; // for MCMF
															   // Interior Property Maps
typedef	boost::property_map<Graph, boost::edge_capacity_t>::type		EdgeCapacityMap;
typedef boost::property_map<Graph, boost::edge_weight_t>::type			EdgeWeightMap;
typedef	boost::property_map<Graph, boost::edge_residual_capacity_t>::type	ResidualCapacityMap;
typedef	boost::property_map<Graph, boost::edge_reverse_t>::type		ReverseEdgeMap;
typedef	boost::graph_traits<Graph>::vertex_descriptor			Vertex;
typedef	boost::graph_traits<Graph>::vertex_iterator				VertexIt;
typedef	boost::graph_traits<Graph>::edge_descriptor			Edge;
typedef boost::graph_traits<Graph>::out_edge_iterator OutEdgeIt;

// Custom Edge Adder Class, that holds the references
// to the graph, capacity map and reverse edge map
// ===================================================
// For ONLY Min-cost Max flow
class EdgeAdderMCMF {
	Graph &G;
	EdgeCapacityMap	&capacitymap;
	ReverseEdgeMap	&revedgemap;
	EdgeWeightMap &weightmap;

public:
	// to initialize the Object
	EdgeAdderMCMF(Graph & G, EdgeCapacityMap &capacitymap, EdgeWeightMap &weightmap, ReverseEdgeMap &revedgemap) :
		G(G), capacitymap(capacitymap), weightmap(weightmap), revedgemap(revedgemap) {}

	// to use the Function (add an edge)
	void addEdge(int from, int to, long capacity, long weight) {
		Edge e, rev_e;
		bool success;
		boost::tie(e, success) = boost::add_edge(from, to, G);
		boost::tie(rev_e, success) = boost::add_edge(to, from, G);
		capacitymap[e] = capacity;
		weightmap[e] = weight;
		capacitymap[rev_e] = 0; // reverse edge has no capacity!
		weightmap[rev_e] = -weight;
		revedgemap[e] = rev_e;
		revedgemap[rev_e] = e;
	}
};

// Custom Edge Adder Class, that holds the references
// to the graph, capacity map and reverse edge map
// for ONLY Max flow
// ===================================================
class EdgeAdderMF {
	Graph &G;
	EdgeCapacityMap	&capacitymap;
	ReverseEdgeMap	&revedgemap;

public:
	// to initialize the Object
	EdgeAdderMF(Graph & G, EdgeCapacityMap &capacitymap, ReverseEdgeMap &revedgemap) :
		G(G), capacitymap(capacitymap), revedgemap(revedgemap) {}

	// to use the Function (add an edge)
	void addEdge(int from, int to, long capacity) {
		Edge e, rev_e;
		bool success;
		boost::tie(e, success) = boost::add_edge(from, to, G);
		boost::tie(rev_e, success) = boost::add_edge(to, from, G);
		capacitymap[e] = capacity;
		capacitymap[rev_e] = 0; // reverse edge has no capacity!
		revedgemap[e] = rev_e;
		revedgemap[rev_e] = e;
	}
};


bool calcFlowMarathon(Graph &G, Vertex s, Vertex f, long dist, long qflow) {
	int n = boost::num_vertices(G) - 2;
	Vertex src = n, tgt = n + 1;
	EdgeCapacityMap cmap = boost::get(boost::edge_capacity, G);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G);
	ResidualCapacityMap rcmap = boost::get(boost::edge_residual_capacity, G);
	ReverseEdgeMap remap = boost::get(boost::edge_reverse, G);
	EdgeAdderMCMF eaG(G, cmap, wmap, remap);

	Edge e; bool suc;
	boost::tie(e, suc) = boost::edge(src, s, G);
	if (suc) cmap[e] = qflow;
	else eaG.addEdge(src, s, qflow, 0);
	boost::tie(e, suc) = boost::edge(f, tgt, G);
	if (suc) cmap[e] = qflow;
	else eaG.addEdge(f, tgt, qflow, 0);
	long flow = boost::push_relabel_max_flow(G, src, tgt);
	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	long cost = boost::find_flow_cost(G);
	if (cost == dist * qflow) return true;
	return false;
}
void Marathon2() {
	int n, m, s, f;
	_i >> n >> m >> s >> f;
	Graph G(n), Gbase(n);
	EdgeCapacityMap cmap = boost::get(boost::edge_capacity, G);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G), basewmap = boost::get(boost::edge_weight, Gbase);
	ResidualCapacityMap rcmap = boost::get(boost::edge_residual_capacity, G);
	ReverseEdgeMap remap = boost::get(boost::edge_reverse, G);
	EdgeAdderMCMF eaG(G, cmap, wmap, remap);

	for (int j = 0; j < m; j++) {
		int a, b, c, d; _i >> a >> b >> c >> d;
		if (a == b) continue;
		eaG.addEdge(a, b, c, d);
		eaG.addEdge(b, a, c, d);

		Edge e; bool suc;
		boost::tie(e, suc) = boost::add_edge(a, b, Gbase);
		basewmap[e] = d;
		boost::tie(e, suc) = boost::add_edge(b, a, Gbase);
		basewmap[e] = d;
	}
	std::vector<int> predmap(n);
	std::vector<long> distmap(n);
	boost::dijkstra_shortest_paths(Gbase, s,
		predecessor_map(boost::make_iterator_property_map(predmap.begin(), boost::get(boost::vertex_index, Gbase))).
		distance_map(boost::make_iterator_property_map(distmap.begin(), boost::get(boost::vertex_index, Gbase))));
	if (predmap[f] == f) {
		_o << 0 << _l; return;
	}
	long d = distmap[f];
	_e << "d=" << d << _l;
	long maxFlow = boost::push_relabel_max_flow(G, s, f);
	_e << "maxFlow=" << maxFlow << _l;
	boost::successive_shortest_path_nonnegative_weights(G, s, f);
	long maxFlowCost = boost::find_flow_cost(G);
	if (maxFlowCost == maxFlow * d) {
		_e << "MaxFlow Return!" << _l;
		_o << maxFlow << _l; return;
	}

	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);
	int result = 0;
	int stflow = 1, endflow = maxFlow;
	std::vector<bool> isMinCost(maxFlow + 1);
	isMinCost[stflow] = isMinCost[0] = true;
	while (true) {
		if (endflow - stflow <= 1) {
			isMinCost[endflow] = calcFlowMarathon(G, s, f, d, endflow);
			if (isMinCost[endflow]) {
				result = endflow; break;
			}
			else {
				result = stflow; break;
			}
		}
		int midflow = (stflow + endflow) / 2;
		isMinCost[midflow] = calcFlowMarathon(G, s, f, d, midflow);
		if (isMinCost[midflow]) {
			stflow = midflow;
		}
		else {
			endflow = midflow - 1;
		}
	}
	//for (int flow = 1; flow <= maxFlow; flow++) {
	//	Edge e; bool success;
	//	boost::tie(e, success) = edge(src, s, G);
	//	if (success) {
	//		cmap[e] = flow;
	//	}
	//	else {
	//		eaG.addEdge(src, s, flow, 0);
	//	}
	//	boost::tie(e, success) = edge(f, tgt, G);
	//	if (success) cmap[e] = flow;
	//	else eaG.addEdge(f, tgt, flow, 0);
	//	
	//	int nowFlow = boost::push_relabel_max_flow(G, src, tgt);
	//	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	//	int nowCost = boost::find_flow_cost(G);
	//	if (nowCost > d*flow) break;
	//	result = flow;
	//}
	_o << result << _l;
}



// Week 10: avalanche / 100 pts
// 1. calc. distance from a to s
// 2. bipartite graph a->s
// 3. binary search on whether the max matching has a edges
int checkASGraph(int t, std::vector< std::vector<int> > &dist, std::vector<int>& takenout, const std::vector<int>& takenin = std::vector<int>()) {
	int a = dist.size();
	int s = dist[0].size();

	Graph ASGraph(a + s);
	EdgeWeightMap aswmap = boost::get(boost::edge_weight, ASGraph);
	ReverseEdgeMap asrevmap = boost::get(boost::edge_reverse, ASGraph);
	EdgeCapacityMap ascapmap = boost::get(boost::edge_capacity, ASGraph);
	ResidualCapacityMap asrescapmap = boost::get(boost::edge_residual_capacity, ASGraph);
	EdgeAdderMF eaG(ASGraph, ascapmap, asrevmap);
	Vertex src = boost::add_vertex(ASGraph), tgt = boost::add_vertex(ASGraph);

	for (int i = 0; i < a; i++) {
		if (!takenin.empty() && takenin[i] == 1) continue;
		for (int j = 0; j < s; j++) {
			if (dist[i][j] == -1) continue;
			if (dist[i][j] > t) continue;
			eaG.addEdge(i, a + j, 1);
		}
		eaG.addEdge(src, i, 1);
	}
	for (int j = 0; j < s; j++) {
		eaG.addEdge(a + j, tgt, 1);
	}

	int flow = boost::push_relabel_max_flow(ASGraph, src, tgt);

	if (takenout.empty()) takenout = std::vector<int>(a, 0);
	OutEdgeIt ei, eend;
	for (boost::tie(ei, eend) = boost::out_edges(src, ASGraph); ei != eend; ++ei) {
		Vertex u = boost::target(*ei, ASGraph);
		if (asrescapmap[*ei] == 0) {
			takenout[u] = 1;
		}
	}
	return flow;
}
void Avalanche() {
	int n, m, a, s, c, d;
	_i >> n >> m >> a >> s >> c >> d;
	_e << "d=" << d << _l;

	// run Dijkstra on baseGraph
	Graph baseGraph(n);
	EdgeWeightMap basewmap = boost::get(boost::edge_weight, baseGraph);
	for (int j = 0; j < m; j++) {
		char w;
		int x, y, z;
		_i >> w >> x >> y >> z;
		if (w == 'S') {
			Edge e; bool su;
			boost::tie(e, su) = boost::add_edge(x, y, baseGraph);
			basewmap[e] = z;
		}
		else if (w == 'L') {
			Edge e; bool su;
			boost::tie(e, su) = boost::add_edge(x, y, baseGraph);
			basewmap[e] = z;
			boost::tie(e, su) = boost::add_edge(y, x, baseGraph);
			basewmap[e] = z;
		}
	}

	std::vector<Vertex> agents(a), shelters(s);
	std::map< Vertex, std::vector<int> > distmaps;
	for (int i = 0; i < a; i++) _i >> agents[i];
	for (int j = 0; j < s; j++) _i >> shelters[j];

	const int BIG = 1000000000;
	int mindist = BIG, maxdist = 0;
	std::vector< std::vector<int> > ASDist(a);
	for (int i = 0; i < a; i++) {
		ASDist[i] = std::vector<int>(s);
		int ca = agents[i];
		std::map< Vertex, std::vector<int> >::iterator dmit = distmaps.find(ca);
		std::vector<int> distmap;
		if (dmit != distmaps.end()) {
			distmap = dmit->second;
		}
		else {
			std::vector<int> predmap(n);
			distmap = std::vector<int>(n);
			boost::dijkstra_shortest_paths(baseGraph, ca,
				predecessor_map(boost::make_iterator_property_map(predmap.begin(), boost::get(boost::vertex_index, baseGraph))).
				distance_map(boost::make_iterator_property_map(distmap.begin(), boost::get(boost::vertex_index, baseGraph))));

			for (int k = 0; k < n; k++) {
				if (predmap[k] == k && k != ca)
					distmap[k] = -1;
				if (k == ca)
					distmap[k] = 0;
			}
			distmaps.insert(std::make_pair(ca, distmap));
		}

		for (int j = 0; j < s; j++) {
			int cs = shelters[j];
			if (distmap[cs] == -1) {
				ASDist[i][j] = -1;
				continue;
			}
			ASDist[i][j] = distmap[cs];
			mindist = std::min(mindist, ASDist[i][j]);
			maxdist = std::max(maxdist, ASDist[i][j]);
		}
	}

	std::set<int> possiblet;
	std::vector<int> vpt;
	for (int i = 0; i < a; i++)
		for (int j = 0; j < s; j++)
			possiblet.insert(ASDist[i][j]);

	std::set<int>::iterator sit = possiblet.begin();
	for (; sit != possiblet.end(); sit++) {
		vpt.push_back(*sit);
	}
	std::vector<int>::iterator vit = vpt.begin();

	std::vector<int> dummy;
	int flow0 = checkASGraph(vpt[0], ASDist, dummy);
	if (flow0 == a) {
		_o << vpt[0] + d << _l;
		return;
	}
	int st = 0, end = 1;
	int npt = vpt.size();
	while (true) {
		int flowend = checkASGraph(vpt[end], ASDist, dummy);
		if (flowend == a) break;
		st = end;
		end = std::min(end * 2, npt - 1);
	}

	int mid = (st + end) / 2;
	//int st = 0, end = vpt.size() - 1, mid = (st + end) / 2;
	int result = 0;
	while (true) {
		std::vector<int> takenout;
		if (end - st <= 1) {
			int flowst = checkASGraph(vpt[st], ASDist, takenout);
			if (flowst == a) {
				result = vpt[st] + d;
				break;
			}
			int flowend = checkASGraph(vpt[end], ASDist, takenout);
			if (flowend == a) {
				result = vpt[end] + d;
				break;
			}
		}

		int t = vpt[mid];
		int flow = checkASGraph(t, ASDist, takenout);
		if (flow == a) {
			end = mid;
			mid = (st + end) / 2;
		}
		else {
			st = mid + 1;
			mid = (st + end) / 2;
		}
	}
	_o << result << _l;
	//for (; vit != vpt.end(); vit++) {
	//	int t = *vit;
	//	Graph ASGraph;
	//	std::vector<int> takenout;
	//	int flow = checkASGraph(t, ASDist, takenout);
	//	if (flow == a) {
	//		_o << t + d << _l;
	//		return;
	//	}
	//	else if (c == 2) {
	//		std::vector<int> newtakenout;
	//		int flow2 = checkASGraph(t + d, ASDist, newtakenout, takenout);
	//		if (flow2 + flow == a) {
	//			_o << t + d + d << _l;
	//			return;
	//		}
	//	}
	//}

	return;
}


// Week 14, PotW: Fleetrace
void Fleetrace2() {
	typedef	boost::adjacency_list_traits<boost::vecS, boost::vecS, boost::directedS> Traits;
	typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS, boost::no_property,
		boost::property<boost::edge_capacity_t, long,
		boost::property<boost::edge_residual_capacity_t, long,
		boost::property<boost::edge_reverse_t, Traits::edge_descriptor,
		boost::property<boost::edge_weight_t, long> > > > >	Graph; // for MCMF
																   // Interior Property Maps
	typedef	boost::property_map<Graph, boost::edge_capacity_t>::type		EdgeCapacityMap;
	typedef boost::property_map<Graph, boost::edge_weight_t>::type			EdgeWeightMap;
	typedef	boost::property_map<Graph, boost::edge_residual_capacity_t>::type	ResidualCapacityMap;
	typedef	boost::property_map<Graph, boost::edge_reverse_t>::type		ReverseEdgeMap;
	typedef	boost::graph_traits<Graph>::vertex_descriptor			Vertex;
	typedef	boost::graph_traits<Graph>::vertex_iterator				VertexIt;
	typedef	boost::graph_traits<Graph>::edge_descriptor			Edge;
	typedef boost::graph_traits<Graph>::out_edge_iterator OutEdgeIt;

	int b, s, p; _i >> b >> s >> p;

	Graph G(b + s);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	EdgeWeightMap weightmap = boost::get(boost::edge_weight, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdderMCMF eaG(G, capacitymap, weightmap, revedgemap);
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);

	const int MAXC = 50;
	for (int i = 0; i < p; i++) {
		int bi, si, ci;
		_i >> bi >> si >> ci;
		eaG.addEdge(bi, b + si, 1, MAXC - ci);
	}
	for (int i = 0; i < b; i++) {
		eaG.addEdge(src, i, 1, 0);
	}
	for (int j = 0; j < s; j++) {
		eaG.addEdge(src, b + j, 1, MAXC);
		eaG.addEdge(b + j, tgt, 1, 0);
	}

	long flow = boost::push_relabel_max_flow(G, src, tgt);
	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	long cost = boost::find_flow_cost(G);
	long result = MAXC * flow - cost;
	_o << result << _l;
	return;

}
// Week 14: Fleetrace / 60pts
// Max weight bipartite matching -- do we need to implement Hungarian?
// no we don't
// but I can't get 100 pts because of TL.
void copyGraph(Graph & g, Graph & gc) {
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, g);
	EdgeWeightMap weightmap = boost::get(boost::edge_weight, g);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, g);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, g);

	EdgeCapacityMap capacitymap1 = boost::get(boost::edge_capacity, gc);
	EdgeWeightMap weightmap1 = boost::get(boost::edge_weight, gc);
	ReverseEdgeMap revedgemap1 = boost::get(boost::edge_reverse, gc);
	ResidualCapacityMap rescapacitymap1 = boost::get(boost::edge_residual_capacity, gc);
	EdgeAdderMCMF eaG1(gc, capacitymap1, weightmap1, revedgemap1);
	VertexIt vit, vend;
	for (boost::tie(vit, vend) = boost::vertices(g); vit != vend; vit++) {
		OutEdgeIt oi, oie;
		for (boost::tie(oi, oie) = boost::out_edges(*vit, g); oi != oie; oi++) {
			eaG1.addEdge(boost::source(*oi, gc), boost::target(*oi, gc), capacitymap[*oi], weightmap[*oi]);
		}
	}
}
int calcFlowCost(Graph &G, int fl, Vertex src, Vertex tgt, Vertex supersink) {
	//Graph G1;
	//copyGraph(G, G1);
	//EdgeCapacityMap capacitymap1 = boost::get(boost::edge_capacity, G1);
	//EdgeWeightMap weightmap1 = boost::get(boost::edge_weight, G1);
	//ReverseEdgeMap revedgemap1 = boost::get(boost::edge_reverse, G1);
	//ResidualCapacityMap rescapacitymap1 = boost::get(boost::edge_residual_capacity, G1);
	//EdgeAdderMCMF eaG1(G1, capacitymap1, weightmap1, revedgemap1);
	EdgeCapacityMap capmap = boost::get(boost::edge_capacity, G);

	//Vertex supersrc = boost::add_vertex(G1);
	//Vertex supersink = boost::add_vertex(G1);
	Edge e; bool su;
	boost::tie(e, su) = boost::edge(tgt, supersink, G);
	capmap[e] = fl;
	//eaG1.addEdge(tgt, supersink, fl, 0);

	int flow, cost;
	flow = boost::push_relabel_max_flow(G, src, supersink);
	boost::successive_shortest_path_nonnegative_weights(G, src, supersink);
	cost = boost::find_flow_cost(G);
	return cost;
}
void Fleetrace() {
	typedef	boost::adjacency_list_traits<boost::vecS, boost::vecS, boost::directedS> Traits;
	typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS, boost::no_property,
		boost::property<boost::edge_capacity_t, long,
		boost::property<boost::edge_residual_capacity_t, long,
		boost::property<boost::edge_reverse_t, Traits::edge_descriptor,
		boost::property<boost::edge_weight_t, long> > > > >	Graph; // for MCMF
																   // Interior Property Maps
	typedef	boost::property_map<Graph, boost::edge_capacity_t>::type		EdgeCapacityMap;
	typedef boost::property_map<Graph, boost::edge_weight_t>::type			EdgeWeightMap;
	typedef	boost::property_map<Graph, boost::edge_residual_capacity_t>::type	ResidualCapacityMap;
	typedef	boost::property_map<Graph, boost::edge_reverse_t>::type		ReverseEdgeMap;
	typedef	boost::graph_traits<Graph>::vertex_descriptor			Vertex;
	typedef	boost::graph_traits<Graph>::vertex_iterator				VertexIt;
	typedef	boost::graph_traits<Graph>::edge_descriptor			Edge;
	typedef boost::graph_traits<Graph>::out_edge_iterator OutEdgeIt;

	int b, s, p; _i >> b >> s >> p;

	Graph G(b + s);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	EdgeWeightMap weightmap = boost::get(boost::edge_weight, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdderMCMF eaG(G, capacitymap, weightmap, revedgemap);

	std::vector<int> coeffs(p), sumcoeffs(p);
	// add edges: boat->sailor
	const int MAXCOEFF = 50;
	for (int i = 0; i < p; i++) {
		int boat, sailor, coeff;
		_i >> boat >> sailor >> coeff;
		coeffs[i] = coeff;
		eaG.addEdge(boat, b + sailor, 1, MAXCOEFF - coeff);
	}
	std::sort(coeffs.begin(), coeffs.end(), [](const int &i1, const int &i2) {return i1 > i2; });
	sumcoeffs[0] = coeffs[0];
	for (int i = 1; i < p; i++) {
		sumcoeffs[i] = sumcoeffs[i - 1] + coeffs[i];
	}

	// add edges: src->boat, sailor->tgt;
	Vertex src = boost::add_vertex(G);
	Vertex tgt = boost::add_vertex(G);
	Vertex supersink = boost::add_vertex(G);
	for (int i = 0; i < b; i++) {
		eaG.addEdge(src, i, 1, 0);
	}
	for (int j = 0; j < s; j++) {
		eaG.addEdge(b + j, tgt, 1, 0);
	}
	eaG.addEdge(tgt, supersink, 0, 0);

	Graph G1;
	copyGraph(G, G1);

	int maxflow = boost::push_relabel_max_flow(G1, (int)src, (int)tgt);
	int costMaxFlow = calcFlowCost(G, maxflow, src, tgt, supersink);
	int specMaxFlow = maxflow*MAXCOEFF - costMaxFlow;
	int costNextFlow = calcFlowCost(G, maxflow - 1, src, tgt, supersink);
	int specNextFlow = (maxflow - 1)*MAXCOEFF - costNextFlow;

	_e << specMaxFlow << "mn" << specNextFlow << _l;
	if (specMaxFlow > specNextFlow) {
		_o << specMaxFlow << _l;
		return;
	}

	int maxSpect = specNextFlow, maxSpectFlow = maxflow - 1;
	int startFlow = -1, endFlow = -1, midFlow = -1;
	int step = 4;
	// 1st: linear search for an interval
	//for (int r = maxflow; r >= 1; ) {
	//	int cost = calcFlowCost(G, r, src, tgt);
	//	int spec = r * MAXCOEFF - cost;
	//	_e << "flow=" << r << ", spec=" << spec << _l;
	//	if (maxSpect <= spec) {
	//		maxSpect = spec;
	//		maxSpectFlow = r;
	//	}
	//	else {
	//		startFlow = std::min(r + 3 * step / 2, maxflow);
	//		endFlow = r;
	//		midFlow = (startFlow + endFlow) / 2;
	//		_e << "start" << startFlow << " end" << endFlow << _l;
	//		break;
	//	}
	//	step *= 2;
	//	r -= r > step ? step : 1;
	//}

	startFlow = maxSpectFlow;
	for (endFlow = 0; endFlow < maxflow; endFlow++) {
		if (sumcoeffs[endFlow] >= maxSpect) break;
	}
	endFlow++;

	midFlow = (startFlow + endFlow + 1) / 2;
	// 2nd: binary search on selected interval
	if (startFlow < 0) {
		_o << maxSpect << _l;
		return;
	}
	maxSpect = 0;
	std::vector<int> specs(startFlow - endFlow + 1);
	int base = endFlow;
	if (!specs[startFlow - base]) {
		//specs[startFlow - base] = startFlow*MAXCOEFF - calcFlowCost(G, startFlow, src, tgt, supersink);
		specs[startFlow - base] = maxSpect;
	}
	if (!specs[endFlow - base]) {
		specs[endFlow - base] = endFlow*MAXCOEFF - calcFlowCost(G, endFlow, src, tgt, supersink);
	}

	while (true) {
		if (startFlow - endFlow <= 2) {
			if (!specs[startFlow - base])
				specs[startFlow - base] = startFlow*MAXCOEFF - calcFlowCost(G, startFlow, src, tgt, supersink);
			if (!specs[endFlow - base])
				specs[endFlow - base] = endFlow*MAXCOEFF - calcFlowCost(G, endFlow, src, tgt, supersink);
			if (!specs[midFlow - base])
				specs[midFlow - base] = midFlow*MAXCOEFF - calcFlowCost(G, midFlow, src, tgt, supersink);
			maxSpect = std::max(specs[startFlow - base], std::max(specs[endFlow - base], specs[midFlow - base]));
			break;
		}

		if (!specs[midFlow - base]) {
			int midCost = calcFlowCost(G, midFlow, src, tgt, supersink);
			int midSpec = midFlow * MAXCOEFF - midCost;
			specs[midFlow - base] = midSpec;
		}
		if (specs[midFlow - base] > specs[endFlow - base] && specs[midFlow - base] < specs[startFlow - base]) {
			endFlow = midFlow + 1;
			midFlow = (startFlow + endFlow) / 2;
			continue;
		}
		else if (specs[midFlow - base] < specs[endFlow - base] && specs[midFlow - base] > specs[startFlow - base]) {
			startFlow = midFlow - 1;
			midFlow = (startFlow + endFlow) / 2;
			continue;
		}

		bool flag = false;
		for (int r = midFlow - 1; r >= endFlow; r--) {
			if (!specs[r - base]) {
				int cost = calcFlowCost(G, r, src, tgt, supersink);
				int spec = r * MAXCOEFF - cost;
				specs[r - base] = spec;
			}
			int spec = specs[r - base];
			if (spec < specs[midFlow - base]) {
				endFlow = midFlow;
				midFlow = (startFlow + endFlow + 1) / 2;
				flag = true;
				break;
			}
			else if (spec > specs[midFlow - base]) {
				startFlow = r;
				midFlow = (startFlow + endFlow + 1) / 2;
				flag = true;
				break;
			}
		}
		if (!flag) {
			endFlow = midFlow;
			midFlow = (startFlow + endFlow + 1) / 2;
		}

		_e << "pos: " << startFlow << " " << midFlow << " " << endFlow << _l;
	}

	//for (int r = startFlow; r >= endFlow; r--) {
	//	int cost = calcFlowCost(G, r, src, tgt);
	//	int spec = r * MAXCOEFF - cost;
	//	_e << "flow=" << r << ", spec=" << spec << _l;
	//	if (maxSpect <= spec) {
	//		maxSpect = spec;
	//		maxSpectFlow = r;
	//	}
	//	else {
	//		break;
	//	}
	//}

	_o << maxSpect << _l;
	_e << maxSpectFlow << " " << maxflow << _l << _l;
	return;

}


// Week 12: Casino Royale
// MCMF?
// Damn it I thought too much about DP.
// Easy version of Car Sharing
void CasinoRoyale() {
	int n, m, l; _i >> n >> m >> l;

	Graph G(n);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G);
	ReverseEdgeMap revmap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescmap = boost::get(boost::edge_residual_capacity, G);
	EdgeCapacityMap cmap = boost::get(boost::edge_capacity, G);
	EdgeAdderMCMF eaG(G, cmap, wmap, revmap);
	Vertex src = boost::add_vertex(G);

	const int MAXQ = 128;
	eaG.addEdge(src, 0, l, 0);
	for (int i = 0; i < n - 1; i++) {
		eaG.addEdge(i, i + 1, l, MAXQ);
	}

	for (int j = 0; j < m; j++) {
		int x, y, q;
		_i >> x >> y >> q;
		eaG.addEdge(x, y, 1, (y - x)*MAXQ - q);
	}

	long flow = boost::push_relabel_max_flow(G, src, n - 1);
	boost::successive_shortest_path_nonnegative_weights(G, src, n - 1);
	long cost = boost::find_flow_cost(G);
	long sumq = flow * MAXQ * (n - 1) - cost;
	_o << sumq << _l;
	return;
}


// Week 13: Bob's Burden
// Split vertices and 3 Dijkstras
inline Vertex getVertex(int i, int j, int k) {
	return (Vertex)(i*(i + 1) / 2 + j);
}
inline bool inRange(int i, int j, int k) {
	return(i >= 0 && i < k && j >= 0 && j < k && i >= j);
}
void BobsBurden() {
	int k; _i >> k;
	std::vector< std::vector<int> > val(k);
	for (int i = 0; i < k; i++) val[i] = std::vector<int>(k);
	// k*(k+1)/2 balls
	int n = k*(k + 1) / 2;
	Graph G(n * 2); // split nodes: other_out -> v_in -> v_out -> other_in
	int nv = boost::num_vertices(G);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G);

	for (int i = 0; i < k; i++) {
		for (int j = 0; j <= i; j++) {
			int vv; _i >> vv;
			val[i][j] = vv;
			Vertex node = getVertex(i, j, k);
			Edge e; bool suc;
			boost::tie(e, suc) = boost::add_edge(node, n + node, G);
			wmap[e] = val[i][j];
		}
	}

	for (int i = 0; i < k; i++) {
		for (int j = 0; j <= i; j++) {
			Vertex v = getVertex(i, j, k);
			if (inRange(i - 1, j - 1, k)) {
				Vertex u = getVertex(i - 1, j - 1, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
			if (inRange(i, j - 1, k)) {
				Vertex u = getVertex(i, j - 1, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
			if (inRange(i - 1, j, k)) {
				Vertex u = getVertex(i - 1, j, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
			if (inRange(i, j + 1, k)) {
				Vertex u = getVertex(i, j + 1, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
			if (inRange(i + 1, j + 1, k)) {
				Vertex u = getVertex(i + 1, j + 1, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
			if (inRange(i + 1, j, k)) {
				Vertex u = getVertex(i + 1, j, k);
				Edge e; bool suc;
				boost::tie(e, suc) = boost::add_edge(n + v, u, G);
				wmap[e] = 0;
			}
		}
	}

	std::vector<Vertex> p11(nv), pk1(nv), pkk(nv);
	std::vector<long> d11(nv), dk1(nv), dkk(nv);

	//boost::connected_components(G, &d11[0]);
	//for (int r = 0; r < nv; r++) {
	//	_e << d11[r] << " ";
	//}_e << _l;

	boost::dijkstra_shortest_paths(G, getVertex(0, 0, k),
		predecessor_map(boost::make_iterator_property_map(p11.begin(), boost::get(boost::vertex_index, G))).
		distance_map(boost::make_iterator_property_map(d11.begin(), boost::get(boost::vertex_index, G))));

	boost::dijkstra_shortest_paths(G, getVertex(k - 1, 0, k),
		predecessor_map(boost::make_iterator_property_map(pk1.begin(), boost::get(boost::vertex_index, G))).
		distance_map(boost::make_iterator_property_map(dk1.begin(), boost::get(boost::vertex_index, G))));

	boost::dijkstra_shortest_paths(G, getVertex(k - 1, k - 1, k),
		predecessor_map(boost::make_iterator_property_map(pkk.begin(), boost::get(boost::vertex_index, G))).
		distance_map(boost::make_iterator_property_map(dkk.begin(), boost::get(boost::vertex_index, G))));

	long minw = 1000000000;
	for (int i = 0; i < k; i++) {
		for (int j = 0; j <= i; j++) {
			Vertex v = getVertex(i, j, k);
			long dist11 = d11[v + n], distk1 = dk1[v], distkk = dkk[v];
			//_e << i << "," << j <<": "<< dist11 << " " << distk1 << " " << distkk << _l;
			long sumw = dist11 + distk1 + distkk;
			if (minw > sumw) {
				minw = sumw;
			}
		}
	}

	_o << minw << _l;
	return;
}


// Week 4: Ant Challenge
// Multiple MST + Dijkstra
void AntChallenge() {
	typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
		boost::no_property, boost::property < boost::edge_weight_t, long > > UGraph;
	typedef boost::property_map < UGraph, boost::edge_weight_t >::type UWeightMap;
	typedef boost::graph_traits < UGraph >::edge_descriptor UEdge;
	typedef boost::graph_traits < UGraph >::edge_iterator UEdgeIt;
	typedef boost::graph_traits < UGraph >::out_edge_iterator UOutEdgeIt;
	typedef boost::graph_traits < UGraph >::vertex_descriptor UVertex;

	int n, e, s, a, b;
	_i >> n >> e >> s >> a >> b;

	// Construct the mst for each species
	std::vector<UGraph> graphs(s), msts(s);

	std::vector<UWeightMap> wmaps(s);
	std::vector<UVertex> hives(s);
	for (int k = 0; k < s; k++) {
		graphs[k] = UGraph(n);
		msts[k] = UGraph(n);
		wmaps[k] = boost::get(boost::edge_weight, graphs[k]);
	}
	for (int j = 0; j < e; j++) {
		int t1, t2; _i >> t1 >> t2;
		for (int k = 0; k < s; k++) {
			int w; _i >> w;
			UEdge e; bool suc;
			boost::tie(e, suc) = boost::add_edge(t1, t2, graphs[k]);
			wmaps[k][e] = w;
		}
	}

	UGraph finalGraph(n);
	UWeightMap finalWmap = boost::get(boost::edge_weight, finalGraph);
	for (int k = 0; k < s; k++) {
		// find MST
		_i >> hives[k];
		std::vector<UVertex> p(n);
		boost::prim_minimum_spanning_tree(graphs[k], &p[0]);

		// construct finalGraph = minimum of each MST
		for (int i = 0; i < n; i++) {
			if (p[i] == i)continue;
			UEdge e, efin; bool suc, sfin;
			boost::tie(e, suc) = boost::edge(p[i], i, graphs[k]);
			boost::tie(efin, sfin) = boost::edge(p[i], i, finalGraph);
			if (sfin) {
				if (finalWmap[efin] > wmaps[k][e]) {
					finalWmap[efin] = wmaps[k][e];
				}
			}
			else {
				boost::tie(efin, sfin) = boost::add_edge(p[i], i, finalGraph);
				finalWmap[efin] = wmaps[k][e];
			}
		}
	}

	std::vector<UVertex> p(n);
	std::vector<long> d(n);
	boost::dijkstra_shortest_paths(finalGraph, a,
		predecessor_map(boost::make_iterator_property_map(p.begin(), boost::get(boost::vertex_index, finalGraph))).
		distance_map(boost::make_iterator_property_map(d.begin(), boost::get(boost::vertex_index, finalGraph))));

	_o << d[b] << _l;
	return;

}


// Week 5: Tracking / 100 pts
// Force Dijkstra to pass k times on certain edges
// Beware of the direction of edges!
void Tracking() {
	typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
		boost::no_property, boost::property < boost::edge_weight_t, long > > UGraph;
	typedef boost::property_map < UGraph, boost::edge_weight_t >::type UWeightMap;
	typedef boost::graph_traits < UGraph >::edge_descriptor UEdge;
	typedef boost::graph_traits < UGraph >::edge_iterator UEdgeIt;
	typedef boost::graph_traits < UGraph >::out_edge_iterator UOutEdgeIt;
	typedef boost::graph_traits < UGraph >::vertex_descriptor UVertex;
	struct MyEdge {
		int a; int b; int c;
		MyEdge(int a = 0, int b = 0, int c = 0) : a(a), b(b), c(c) {}
	};

	int n, m, k, x, y;
	_i >> n >> m >> k >> x >> y;

	UGraph G(n*(k + 1));
	int nv = boost::num_vertices(G);
	y += n*k;
	UWeightMap wmap = boost::get(boost::edge_weight, G);
	std::vector<MyEdge> riveredges;
	for (int i = 0; i < m; i++) {
		int a, b, c, d;
		_i >> a >> b >> c >> d;
		if (d == 1) {
			riveredges.push_back(MyEdge(a, b, c));
		}
		for (int l = 0; l <= k; l++) {
			Vertex va = l*n + a;
			Vertex vb = l*n + b;
			UEdge e; bool success;
			boost::tie(e, success) = boost::add_edge(va, vb, G);
			wmap[e] = c;
		}
	}
	int mr = riveredges.size();
	for (int i = 0; i < mr; i++) {
		MyEdge me = riveredges[i];
		for (int l = 0; l < k; l++) {
			Vertex va = l*n + me.a;
			Vertex vb = (l + 1)*n + me.b;
			UEdge e; bool success;
			boost::tie(e, success) = boost::add_edge(va, vb, G);
			wmap[e] = me.c;
			Vertex var = va + n;
			Vertex vbr = vb - n;
			boost::tie(e, success) = boost::add_edge(var, vbr, G);
			wmap[e] = me.c;
		}
	}

	std::vector<UVertex> p(nv);
	std::vector<long> d(nv);
	boost::dijkstra_shortest_paths(G, x,
		predecessor_map(boost::make_iterator_property_map(p.begin(), boost::get(boost::vertex_index, G))).
		distance_map(boost::make_iterator_property_map(d.begin(), boost::get(boost::vertex_index, G))));

	_o << d[y] << _l;
	return;

}


// Week 10: Return of the Jedi / 40->40->40->100 pts
// Second MST
typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
	boost::no_property, boost::property < boost::edge_weight_t, long > > UGraph;
typedef boost::property_map < UGraph, boost::edge_weight_t >::type UWeightMap;
typedef boost::graph_traits < UGraph >::edge_descriptor UEdge;
typedef boost::graph_traits < UGraph >::edge_iterator UEdgeIt;
typedef boost::graph_traits < UGraph >::out_edge_iterator UOutEdgeIt;
typedef boost::graph_traits < UGraph >::vertex_descriptor UVertex;
struct MyEdge {
	int s;
	int t;
	long w;
	MyEdge(int s = 0, int t = 0, long w = 0) :s(s), t(t), w(w) {}
};
bool CompareMyEdgeWST(const MyEdge & e1, const MyEdge & e2) {
	if (e1.w < e2.w) return true;
	if (e1.w > e2.w) return false;
	if (e1.s < e2.s) return true;
	if (e1.s > e2.s) return false;
	if (e1.t < e2.t) return true;
	return false;
}
long calcMSTWeight(UGraph & G, std::vector<UVertex> &p) {
	int n = p.size();
	UWeightMap wmap = boost::get(boost::edge_weight, G);
	long mstWeight = 0;
	for (int i = 0; i < n; i++) {
		if (p[i] != i) {
			UEdge e; bool success;
			boost::tie(e, success) = boost::edge(p[i], i, G);
			if (!success) {
				boost::tie(e, success) = boost::edge(i, p[i], G);
			}
			mstWeight += wmap[e];
		}
	}
	return mstWeight;
}
void ReturnOfTheJedi() {
	typedef std::pair<int, int> E;

	int n, tat; _i >> n >> tat;
	UGraph G(n);
	UWeightMap wmap = boost::get(boost::edge_weight, G);
	//std::vector<MyEdge> myedges;
	std::vector< std::vector<int> > weights(n);
	for (int i = 0; i < n; i++) {
		weights[i] = std::vector<int>(n);
	}
	for (int i = 0; i < n - 1; i++) {
		for (int j = i + 1; j < n; j++) {
			long cost;
			_i >> cost;
			UEdge e; bool success;
			boost::tie(e, success) = boost::add_edge(i, j, G);
			wmap[e] = cost;
			//myedges.push_back(MyEdge(i, j, cost));
			weights[i][j] = weights[j][i] = cost;
		}
	}
	//std::sort(myedges.begin(), myedges.end(), CompareMyEdgeWST);

	std::vector<UVertex> p(n);
	prim_minimum_spanning_tree(G, &p[0]);
	// calc weight sum
	long mstWeight = calcMSTWeight(G, p);

	const long BIG = ((long)1 << 30);
	long minSecond = BIG;
	_e << minSecond << _l;

	// construct MST
	UGraph MST(n);
	for (int i = 0; i < n; i++) {
		if (p[i] != i) {
			boost::add_edge(p[i], i, MST);
		}
	}

	//int minSecond = 100000000;
	for (int i = 0; i < n; i++) {
		// find maximum weight edge for every v
		std::queue<Vertex> vq;
		vq.push(i);
		std::vector<long> maxw(n);
		std::vector<bool> isvisited(n);
		maxw[i] = 0;
		isvisited[i] = true;
		while (!vq.empty()) {
			Vertex u = vq.front();
			vq.pop();
			UOutEdgeIt eit, eend;
			for (boost::tie(eit, eend) = boost::out_edges(u, MST); eit != eend; ++eit) {
				Vertex v = boost::target(*eit, MST);
				if (isvisited[v]) continue;
				//UEdge e; bool success;
				//boost::tie(e, success) = boost::edge(u, v, G);
				long we = weights[u][v];
				maxw[v] = std::max(maxw[u], we);
				vq.push(v);
				isvisited[v] = true;
			}
		}
		int minAdd = 100000000;
		for (int j = i + 1; j < n; j++) {
			if (p[i] == j || p[j] == i) continue; // in MST
												  //UEdge e; bool success;
												  //boost::tie(e, success) = boost::edge(i, j, G);
			long we = weights[i][j];
			int add = we - maxw[j];
			if (add < minAdd) {
				minAdd = add;
			}
		}
		if (minAdd < minSecond)
			minSecond = minAdd;
	}
	minSecond += mstWeight;

	// another 40 pts...
	//for (int i = 0; i < n; i++) {
	//	if (p[i] != i) {
	//		UEdge e; bool success;
	//		boost::tie(e, success) = boost::edge(p[i], i, G);
	//		if (!success) {
	//			boost::tie(e, success) = boost::edge(i, p[i], G);
	//		}
	//		
	//		UGraph G1(n);
	//		for (int j = 0; j < n; j++) {
	//			if (p[j] != j && j != i) {
	//				boost::add_edge(p[j], j, G1);
	//			}
	//		}
	//		std::vector<int> components(n);
	//		boost::connected_components(G1, &components[0]);

	//		int cs = std::min((int)p[i], i), ct = std::max((int)p[i], i);
	//		MyEdge curme(cs, ct, wmap[e]);
	//		_e << "check: " << cs << "->" << ct << "=";
	//		_e << wmap[e] << _l;
	//		std::vector<MyEdge>::iterator meit = std::upper_bound(myedges.begin(), myedges.end(), curme, CompareMyEdgeWST);
	//		for (; meit != myedges.end(); ++meit) {
	//			_e << meit->s << "->" << meit->t << "=" << meit->w << _l;

	//			if (components[meit->s] != components[meit->t]) {
	//				long w = meit->w;
	//				if (minSecond > (w - wmap[e])) {
	//					minSecond = (w - wmap[e]);
	//				}
	//				break;
	//			}
	//		}
	//		if (minSecond == 0) break;
	//	}
	//}
	//minSecond += mstWeight;
	//

	// 40 pts
	//for (int i = 0; i < n; i++) {
	//	if (p[i] != i) {
	//		UEdge e; bool success;
	//		boost::tie(e, success) = boost::edge(p[i], i, G);
	//		long wtmp = wmap[e];
	//		wmap[e] = BIG;
	//		std::vector<UVertex> pnow(n);
	//		prim_minimum_spanning_tree(G, &pnow[0]);
	//		long mstWnow = calcMSTWeight(G, pnow);
	//		if (minSecond > mstWnow) {
	//			minSecond = mstWnow;
	//		}
	//		wmap[e] = wtmp;
	//		_e << minSecond << _l;
	//	}
	//}
	_o << minSecond << _l;
	return;
}


// Week 11: Carsharing / 100pts
// MCMF? how to convert to non-negative costs?
// took me a while to figure out non-negative costs
// prove that it is indeed Max Flow (no need to search)
void Carsharing() {
	int N, S; _i >> N >> S;

	Graph G(S);
	EdgeCapacityMap capmap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revmap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapmap = boost::get(boost::edge_residual_capacity, G);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G);
	EdgeAdderMCMF eaG(G, capmap, wmap, revmap);
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);

	std::vector< std::map<int, Vertex> > times(S);
	const int MAXP = 100, BIG = 10000000, FINAL = 100000;
	for (int i = 0; i < S; i++) {
		int l; _i >> l;
		eaG.addEdge(src, i, l, 0);
		times[i].insert(std::make_pair(0, i));
		Vertex last = boost::add_vertex(G);
		eaG.addEdge(last, tgt, BIG, 0);
		times[i].insert(std::make_pair(FINAL, last));
	}
	for (int i = 0; i < N; i++) {
		int s, t, d, a, p;
		_i >> s >> t >> d >> a >> p;
		s--;
		t--;
		std::map<int, Vertex>::iterator mits, mitt;
		mits = times[s].find(d);
		mitt = times[t].find(a);
		Vertex depart, arrival;
		if (mits == times[s].end()) {
			depart = boost::add_vertex(G);
			times[s].insert(std::make_pair(d, depart));
		}
		else depart = mits->second;
		if (mitt == times[t].end()) {
			arrival = boost::add_vertex(G);
			times[t].insert(std::make_pair(a, arrival));
		}
		else arrival = mitt->second;

		eaG.addEdge(depart, arrival, 1, MAXP*(a - d) - p);
	}

	// add edges along every rental station
	for (int i = 0; i < S; i++) {
		std::map<int, Vertex>::iterator mit1, mit2;
		mit1 = times[i].begin();
		//Vertex first = mit1->second;
		//eaG.addEdge(i, first, BIG, MAXP);
		mit2 = times[i].begin(); ++mit2;
		for (; mit2 != times[i].end(); ++mit1, ++mit2) {
			Vertex prev = mit1->second;
			Vertex curr = mit2->second;
			eaG.addEdge(prev, curr, BIG, MAXP*(mit2->first - mit1->first));
		}
		//mit1 = times[i].end(); --mit1;
		//Vertex last = mit1->second;
		//eaG.addEdge(last, tgt, BIG, MAXP);
	}

	long flow = boost::push_relabel_max_flow(G, src, tgt);
	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	//boost::cycle_canceling(G);
	long cost = boost::find_flow_cost(G);
	long profit = flow * MAXP * FINAL - cost;
	//int profit = -cost;
	_o << profit << _l;
	return;

}


// Week 9: Real Estate Market / 100pts
// MCMF
void RealEstate() {
	int N, M, S;
	_i >> N >> M >> S;

	Graph G(N + M + S);
	EdgeCapacityMap capmap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revmap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapmap = boost::get(boost::edge_residual_capacity, G);
	EdgeWeightMap wmap = boost::get(boost::edge_weight, G);
	EdgeAdderMCMF eaG(G, capmap, wmap, revmap);
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);
	Vertex supersrc = boost::add_vertex(G), supertgt = boost::add_vertex(G);

	for (int k = 0; k < S; k++) {
		int l; _i >> l;
		eaG.addEdge(N + M + k, tgt, l, 0);
	}
	for (int j = 0; j < M; j++) {
		int s; _i >> s;
		eaG.addEdge(N + j, N + M + s - 1, 1, 0);
	}
	int bid[100][100] = {};
	const int MAXBID = 100;
	for (int i = 0; i < N; i++) {
		for (int j = 0; j < M; j++) {
			_i >> bid[i][j];
			eaG.addEdge(i, N + j, 1, MAXBID - bid[i][j]);
		}
		eaG.addEdge(src, i, 1, 0);
	}

	int flow = boost::push_relabel_max_flow(G, src, tgt);
	int bestflow = flow;
	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	int cost = boost::find_flow_cost(G);
	int revenue = flow * MAXBID - cost, bestrevenue = revenue;
	_e << _l << "N=" << N << ",S=" << S << " \tmaxflow=" << flow << " \trev=" << revenue << _l;

	//eaG.addEdge(supersrc, src, flow, 0);
	//for (int f = 1; f < flow; f++) {
	//	Edge e;
	//	bool success;
	//	boost::tie(e, success) = boost::edge(supersrc, src, G);
	//	if (success) {
	//		capmap[e] = 0;
	//	}
	//	eaG.addEdge(supersrc, src, f, 0);
	//	int cflow = boost::push_relabel_max_flow(G, supersrc, tgt);
	//	boost::successive_shortest_path_nonnegative_weights(G, supersrc, tgt);
	//	int ccost = boost::find_flow_cost(G);
	//	int crevenue = f * MAXBID - ccost;
	//	if (crevenue > bestrevenue) {
	//		bestrevenue = crevenue;
	//		bestflow = f;
	//	}
	//	_e << "flow=" << f << " \trev=" << crevenue << _l;
	//}
	_o << bestflow << " " << bestrevenue << _l;
	return;
}


// Week 13: Phantom Menace / 100pts
// Min Vertex Cut --> Min Edge Cut
// Split vertices into two: in--1-->out
// Who says I cannot do a problem in 20min!
void PhantomMenace() {
	int n, m, s, d;
	_i >> n >> m >> s >> d;
	Graph G(n * 2);
	EdgeCapacityMap capmap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revmap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapmap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdderMF eaG(G, capmap, revmap);
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);

	// split nodes
	for (int i = 0; i < n; i++) {
		eaG.addEdge(i, i + n, 1);
	}
	int BIG = 10000000;
	for (int j = 0; j < m; j++) {
		int x, y; _i >> x >> y;
		eaG.addEdge(x + n, y, BIG);
	}
	for (int i = 0; i < s; i++) {
		int start; _i >> start;
		eaG.addEdge(src, start, BIG);
	}
	for (int i = 0; i < d; i++) {
		int dest; _i >> dest;
		eaG.addEdge(dest + n, tgt, BIG);
	}

	long flow = boost::push_relabel_max_flow(G, src, tgt);
	_o << flow << _l;
	return;

}


// Week 10, PotW: Surveillance Photos / 100pts
// Different flow entity
// Add vertices to the graph
void SurveillancePhotos() {
	int n, m, k, l; _i >> n >> m >> k >> l;
	std::vector<int> stations(n, 0), photos(n, 0);
	int maxPhotos = 0;
	for (int i = 0; i < k; i++) {
		int pos; _i >> pos;
		stations[pos]++;
	}
	for (int j = 0; j < l; j++) {
		int pos; _i >> pos;
		photos[pos]++;
	}
	for (int i = 0; i < n; i++) {
		if (stations[i] > 0 && photos[i] > 0) {
			int selfPhotos = std::min(stations[i], photos[i]);
			maxPhotos += selfPhotos;
			stations[i] -= selfPhotos;
			photos[i] -= selfPhotos;
		}
	}

	Graph G(2 * n); // 0~n-1: original graph, n~2n-1: added vertices
	EdgeCapacityMap Gcap = boost::get(boost::edge_capacity, G);
	ResidualCapacityMap Grescap = boost::get(boost::edge_residual_capacity, G);
	ReverseEdgeMap Grev = boost::get(boost::edge_reverse, G);
	EdgeAdderMF eaG(G, Gcap, Grev);
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);

	// construct original graph
	for (int j = 0; j < m; j++) {
		int x, y; _i >> x >> y;
		eaG.addEdge(x, y, 1);
	}

	// find P that is reachable by each S
	// add edges to form a graph: src-->station--man-->photo--manw/photo-->station-->tgt
	// BFS
	for (int i = 0; i < n; i++) {
		if (stations[i] > 0) {
			eaG.addEdge(src, i + n, stations[i]);
			eaG.addEdge(i, tgt, stations[i]);
			std::queue<Vertex> vq;
			vq.push(i);
			std::vector<bool> visited(2 * n + 2); // though the only worry is visiting _tgt_...
			while (!vq.empty()) {
				Vertex u = vq.front();
				vq.pop();
				OutEdgeIt ei, eend;
				for (boost::tie(ei, eend) = boost::out_edges(u, G); ei != eend; ei++) {
					if (Gcap[*ei] == 0) continue;
					Vertex v = boost::target(*ei, G);
					if (visited[v]) continue;
					visited[v] = true;
					vq.push(v);
				}
			}
			for (int j = 0; j < n; j++) {
				if (visited[j] && photos[j]) {
					eaG.addEdge(i + n, j + n, 10000000);
				}
			}
		}
		else if (photos[i] > 0) {
			eaG.addEdge(i + n, i, photos[i]);
		}
	}
	long flow = boost::push_relabel_max_flow(G, src, tgt);
	maxPhotos += flow;
	_o << maxPhotos << _l;
	return;
}


// Week 9: Satellites / 100pts
// Bipartite Vertex cover, output the cover
void Satellites() {
	int g, s, l; _i >> g >> s >> l;
	Graph G(g + s);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdderMF eaG(G, capacitymap, revedgemap);

	for (int i = 0; i < l; i++) {
		int gg, ss; _i >> gg >> ss;
		eaG.addEdge(gg, g + ss, 1);
	}
	Vertex src = boost::add_vertex(G);
	Vertex tgt = boost::add_vertex(G);
	for (int i = 0; i < g; i++) {
		eaG.addEdge(src, i, 1);
	}
	for (int i = 0; i < s; i++) {
		eaG.addEdge(i + g, tgt, 1);
	}

	int flow = boost::push_relabel_max_flow(G, src, tgt);

	std::queue<Vertex> vq;
	std::vector<bool> visited(g + s + 2, false);
	vq.push(src);
	visited[src] = true;
	while (!vq.empty()) {
		Vertex u = vq.front();
		vq.pop();
		OutEdgeIt eit, eend;
		for (boost::tie(eit, eend) = boost::out_edges(u, G); eit != eend; eit++) {
			if (rescapacitymap[*eit] == 0) continue;
			Vertex v = boost::target(*eit, G);
			if (visited[v]) continue;
			vq.push(v);
			visited[v] = true;
		}
	}
	std::vector<int> coverS, coverG;
	for (int i = 0; i < g; i++) {
		if (!visited[i]) {
			coverG.push_back(i);
		}
	}
	for (int i = g; i < g + s; i++) {
		if (visited[i]) {
			coverS.push_back(i - g);
		}
	}
	int ncs = coverS.size(), ncg = coverG.size();
	_o << coverG.size() << " " << coverS.size() << _l;
	if (ncs + ncg > 0) {
		for (int i = 0; i < ncg; i++) {
			_o << coverG[i] << " ";
		}
		for (int j = 0; j < ncs; j++) {
			_o << coverS[j] << " ";
		}
		_o << _l;
	}
}



// Week 9: Algocoon / 100pts
// Min Cut with indetermined src/tgt
void Algocoon() {
	int n, m; _i >> n >> m;

	Graph G(n);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdderMF eaG(G, capacitymap, revedgemap);

	for (int i = 0; i < m; i++) {
		int a, b, c;
		_i >> a >> b >> c;
		eaG.addEdge(a, b, c);
	}
	Vertex src = boost::add_vertex(G), tgt = boost::add_vertex(G);
	const long BIG = 100000000;
	eaG.addEdge(src, 0, BIG);
	//eaG.addEdge(n - 1, tgt, BIG);

	long minCutCost = BIG;
	int minCutTgt = 0, minCutSrc = 0;
	for (int i = 1; i < n; i++) {
		eaG.addEdge(i, tgt, BIG);
		long flow = boost::push_relabel_max_flow(G, src, tgt);
		if (flow < minCutCost) {
			minCutCost = flow;
			minCutTgt = i;
		}
		// remove the edge added
		Edge e; bool success;
		boost::tie(e, success) = boost::edge(i, tgt, G);
		if (success) {
			capacitymap[e] = 0;
		}
	}

	// 0 as target
	Edge e; bool success;
	boost::tie(e, success) = boost::edge(src, 0, G);
	capacitymap[e] = 0;
	eaG.addEdge(0, tgt, BIG);
	for (int i = 1; i < n; i++) {
		eaG.addEdge(src, i, BIG);
		long flow = boost::push_relabel_max_flow(G, src, tgt);
		if (flow < minCutCost) {
			minCutCost = flow;
			minCutTgt = 0;
			minCutSrc = i;
		}
		// remove the edge added
		Edge e; bool success;
		boost::tie(e, success) = boost::edge(src, i, G);
		if (success) {
			capacitymap[e] = 0;
		}
	}
	boost::tie(e, success) = boost::edge(0, tgt, G);
	capacitymap[e] = 0;
	_e << minCutCost << "s:" << minCutSrc << " t:" << minCutTgt << _l;
	_o << minCutCost << _l;

	// search for the list of vertices reachable
	// reachable = residual capacity > 0
	eaG.addEdge(src, minCutSrc, BIG);
	eaG.addEdge(tgt, minCutTgt, BIG);
	long flow = boost::push_relabel_max_flow(G, src, minCutTgt);
	std::queue<Vertex> vq;
	std::vector<bool> visited(n + 2);
	std::vector<Vertex> visibles;
	vq.push(src);
	visited[src] = true;
	while (!vq.empty()) {
		Vertex u = vq.front(); vq.pop();
		if (u < n) {
			visibles.push_back(u);
		}
		OutEdgeIt ei, eend;
		for (boost::tie(ei, eend) = boost::out_edges(u, G); ei != eend; ei++) {
			//_e << *ei << ": " << capacitymap[*ei] << ", " << rescapacitymap[*ei] << _l;
			if (rescapacitymap[*ei] == 0) continue;
			//_e << *ei << ": " << capacitymap[*ei] << ", " << rescapacitymap[*ei] << _l;
			Vertex v = boost::target(*ei, G);
			if (visited[v]) continue;
			vq.push(v);
			visited[v] = true;
		}
	}

	_o << visibles.size();
	int nv = visibles.size();
	while (!visibles.empty()) {
		_o << " " << visibles[nv - 1];
		nv--;
		visibles.pop_back();
	}
	_o << _l;

	return;

}


// Week 9: Canteen / 100pts
// MCMF, need to convert to non-negative costs
void Canteen() {
	typedef	boost::adjacency_list_traits<boost::vecS, boost::vecS, boost::directedS> Traits;
	typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::directedS, boost::no_property,
		boost::property<boost::edge_capacity_t, long,
		boost::property<boost::edge_residual_capacity_t, long,
		boost::property<boost::edge_reverse_t, Traits::edge_descriptor,
		boost::property<boost::edge_weight_t, long> > > > >	Graph; // for MCMF
	typedef	boost::property_map<Graph, boost::edge_capacity_t>::type		EdgeCapacityMap;
	typedef boost::property_map<Graph, boost::edge_weight_t>::type			EdgeWeightMap;
	typedef	boost::property_map<Graph, boost::edge_residual_capacity_t>::type	ResidualCapacityMap;
	typedef	boost::property_map<Graph, boost::edge_reverse_t>::type		ReverseEdgeMap;
	typedef	boost::graph_traits<Graph>::vertex_descriptor			Vertex;
	typedef	boost::graph_traits<Graph>::vertex_iterator				VertexIt;
	typedef	boost::graph_traits<Graph>::edge_descriptor			Edge;
	typedef boost::graph_traits<Graph>::out_edge_iterator OutEdgeIt;


	int n; _i >> n;
	Graph G(n);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	EdgeWeightMap weightmap = boost::get(boost::edge_weight, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	EdgeAdderMCMF eaG(G, capacitymap, weightmap, revedgemap);

	Vertex src = boost::add_vertex(G);
	Vertex tgt = boost::add_vertex(G);


	int BIAS = 40;
	int nStudents = 0;
	for (int i = 0; i < n; i++) {
		int a, c;
		_i >> a >> c;
		eaG.addEdge(src, i, a, c);
	}
	// only bias the negative weights at the t-edges!
	for (int i = 0; i < n; i++) {
		int s, p; _i >> s >> p;
		nStudents += s;
		eaG.addEdge(i, tgt, s, BIAS - p);
	}
	for (int i = 0; i < n - 1; i++) {
		int v, e; _i >> v >> e;
		eaG.addEdge(i, i + 1, v, e);
	}

	long flow = boost::push_relabel_max_flow(G, src, tgt);
	boost::successive_shortest_path_nonnegative_weights(G, src, tgt);
	//boost::cycle_canceling(G);
	long cost = boost::find_flow_cost(G);

	if (flow >= nStudents) _o << "possible ";
	else _o << "impossible ";
	_e << flow << " " << cost << " " << BIAS*flow - cost << _l;
	_o << flow << " " << BIAS*flow - cost << _l;
	return;
}



typedef EdgeAdderMF EdgeAdder;
// Week 14: Cantonal courier
// bipartite max independent set with weight
// sum of weights in MaxIS = totalWeights - weights in MinVC
void CantonalCourier() {
	typedef long long lint;

	int Z, J;
	_i >> Z >> J;
	std::vector<int> c(Z);
	std::vector<int> p(J);

	for (int i = 0; i < Z; i++) {
		_i >> c[i];
	}
	int sump = 0;
	for (int j = 0; j < J; j++) {
		_i >> p[j];
		sump += p[j];
	}

	Graph G(J + Z);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdder eaG(G, capacitymap, revedgemap);

	// add edges: job->zone
	const int BIG = 10000000;
	for (int j = 0; j < J; j++) {
		int N; _i >> N;
		int zone = 0;
		for (int k = 0; k < N; k++) {
			_i >> zone;
			eaG.addEdge(j, J + zone, BIG);
		}
	}
	// s->job and zone->t
	Vertex s = boost::add_vertex(G);
	Vertex t = boost::add_vertex(G);
	for (int j = 0; j < J; j++) {
		eaG.addEdge(s, j, p[j]);
	}
	for (int i = 0; i < Z; i++) {
		eaG.addEdge(J + i, t, c[i]);
	}

	lint flow = boost::push_relabel_max_flow(G, s, t);
	_o << sump - flow << _l; // calculate what we want and get this
	return;
}


// Week 12: placing knights
inline bool inBoard(int i, int j, int n) {
	return i >= 0 && i < n && j >= 0 && j < n;
}
void PlacingKnights() {
	int n; _i >> n;
	int board[65][65] = {};
	int v_board[65][65] = {};
	int total_places = 0;
	int blacks = 0;
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			_i >> board[i][j];
			if (board[i][j]) {
				blacks += ((i + j) % 2 == 0);
				v_board[i][j] = total_places++;
			}
		}
	}

	// check connection--heuristics?
	bool all2conn = true;
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (!board[i][j]) continue;
			int conn = 0;
			if (inBoard(i - 2, j - 1, n) && board[i - 2][j - 1]) conn++;
			if (inBoard(i - 2, j + 1, n) && board[i - 2][j + 1]) conn++;
			if (inBoard(i + 2, j - 1, n) && board[i + 2][j - 1]) conn++;
			if (inBoard(i + 2, j + 1, n) && board[i + 2][j + 1]) conn++;
			if (inBoard(i - 1, j - 2, n) && board[i - 1][j - 2]) conn++;
			if (inBoard(i - 1, j + 2, n) && board[i - 1][j + 2]) conn++;
			if (inBoard(i + 1, j - 2, n) && board[i + 1][j - 2]) conn++;
			if (inBoard(i + 1, j + 2, n) && board[i + 1][j + 2]) conn++;
			if (conn < 2) {
				all2conn = false;
				break;
			}
		}
	}
	if (all2conn) {
		_e << "all2conn!" << _l;
		_o << std::max(total_places - blacks, blacks) << _l;
		return;
	}

	Graph G(total_places);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdder eaG(G, capacitymap, revedgemap);
	for (int i = 0; i < n; i++) {
		for (int j = i % 2; j < n; j += 2) {
			// add edges of the bipartite graph
			if (!board[i][j]) continue;
			if (inBoard(i - 2, j - 1, n) && board[i - 2][j - 1]) eaG.addEdge(v_board[i][j], v_board[i - 2][j - 1], 1);
			if (inBoard(i - 2, j + 1, n) && board[i - 2][j + 1]) eaG.addEdge(v_board[i][j], v_board[i - 2][j + 1], 1);
			if (inBoard(i + 2, j - 1, n) && board[i + 2][j - 1]) eaG.addEdge(v_board[i][j], v_board[i + 2][j - 1], 1);
			if (inBoard(i + 2, j + 1, n) && board[i + 2][j + 1]) eaG.addEdge(v_board[i][j], v_board[i + 2][j + 1], 1);
			if (inBoard(i - 1, j - 2, n) && board[i - 1][j - 2]) eaG.addEdge(v_board[i][j], v_board[i - 1][j - 2], 1);
			if (inBoard(i - 1, j + 2, n) && board[i - 1][j + 2]) eaG.addEdge(v_board[i][j], v_board[i - 1][j + 2], 1);
			if (inBoard(i + 1, j - 2, n) && board[i + 1][j - 2]) eaG.addEdge(v_board[i][j], v_board[i + 1][j - 2], 1);
			if (inBoard(i + 1, j + 2, n) && board[i + 1][j + 2]) eaG.addEdge(v_board[i][j], v_board[i + 1][j + 2], 1);
		}
	}

	// add edges from the source and towards the target
	Vertex s = boost::add_vertex(G);
	Vertex t = boost::add_vertex(G);
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (!board[i][j]) continue;
			if ((i + j) % 2 == 0) eaG.addEdge(s, v_board[i][j], 1);
			else eaG.addEdge(v_board[i][j], t, 1);
		}
	}

	long flow = boost::push_relabel_max_flow(G, s, t);
	_e << "flow=" << flow << _l;

	// find vertices reachable from s in Residual Graph
	std::queue<Vertex> vq;
	std::vector<bool> visited(total_places + 2);
	for (int i = 0; i < total_places + 2; i++) visited[i] = false;
	vq.push(s);
	while (!vq.empty()) {
		Vertex u = vq.front();
		visited[u] = true;
		OutEdgeIt ei, eend;
		for (boost::tie(ei, eend) = boost::out_edges(u, G); ei != eend; ei++) {
			if (rescapacitymap[*ei] == 0) continue; // residual capacity=0 --> inreachable from s in residual graph
			Vertex v = boost::target(*ei, G);
			if (visited[v]) continue;
			else vq.push(v);
		}
		vq.pop();
	}

	// count the size of maximum independent set
	int black_s = 0, black_t = 0;
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			if (!board[i][j]) continue;
			Vertex u = v_board[i][j];
			if ((i + j) % 2 == 0 && visited[u]) black_s++;
			else if ((i + j) % 2 == 1 && !visited[u]) black_s++;
			else if ((i + j) % 2 == 1 && visited[u]) black_t++;
			else if ((i + j) % 2 == 0 && !visited[u]) black_t++;
		}
	}
	_e << "b_s=" << black_s << ",b_t=" << black_t << _l;
	_o << std::max(black_s, black_t) << _l;
	return;
}


// Functions
// =========
// Function for an individual testcase
void testcases() {
	// Create Graph and Maps
	Graph G(4);
	EdgeCapacityMap capacitymap = boost::get(boost::edge_capacity, G);
	ReverseEdgeMap revedgemap = boost::get(boost::edge_reverse, G);
	ResidualCapacityMap rescapacitymap = boost::get(boost::edge_residual_capacity, G);
	EdgeAdder eaG(G, capacitymap, revedgemap);

	// Add edges
	eaG.addEdge(0, 1, 1); // from, to, capacity
	eaG.addEdge(0, 3, 1);
	eaG.addEdge(2, 1, 1);
	eaG.addEdge(2, 3, 1);

	// Add source and sink
	// Careful: The names 'source' and 'target' are already used for BGL's
	// functions to get the two endpoints of an edge, use 'src' and 'sink'
	// in case you remove the namespace (which we don't recommend).
	Vertex source = boost::add_vertex(G);
	Vertex target = boost::add_vertex(G);
	eaG.addEdge(source, 0, 2);
	eaG.addEdge(source, 2, 1);
	eaG.addEdge(1, target, 2);
	eaG.addEdge(3, target, 1);

	// Calculate flow
	// If not called otherwise, the flow algorithm uses the interior properties
	// - edge_capacity, edge_reverse (read access),
	// - edge_residual_capacity (read and write access).
	long flow1 = boost::push_relabel_max_flow(G, source, target);
	long flow2 = boost::edmonds_karp_max_flow(G, source, target);
	std::cout << flow1 << " == " << flow2 << std::endl;
}