#include <CGAL/Exact_predicates_exact_constructions_kernel.h>
//#include <CGAL/Exact_predicates_exact_constructions_kernel_with_sqrt.h>
#include <CGAL/Exact_predicates_inexact_constructions_kernel.h>
#include <CGAL/Projection_traits_xy_3.h>
#include <CGAL/Delaunay_triangulation_2.h>
#include <CGAL/Triangulation_vertex_base_with_info_2.h>
#include <CGAL/Triangulation_face_base_with_info_2.h>
#include <CGAL/Triangulation_vertex_base_with_id_2.h>
#include <CGAL/Min_circle_2.h>
#include <CGAL/Min_circle_2_traits_2.h>
#include <CGAL/basic.h>
#include <CGAL/QP_models.h>
#include <CGAL/QP_functions.h>
#include <CGAL/Gmpz.h>
#include "UnionFind.h"

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/bipartite.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/kruskal_min_spanning_tree.hpp>

#include <iostream>
#include <cassert>
#include <vector>
#include <queue>
#include <stack>
#include <cmath>
#include <valarray>

// LP/QP
typedef CGAL::Gmpq ET;
// program and solution types
typedef CGAL::Quadratic_program<ET> Program;
typedef CGAL::Quadratic_program_solution<ET> Solution;

// General CGAL
typedef CGAL::Exact_predicates_exact_constructions_kernel EK;
//typedef CGAL::Exact_predicates_exact_constructions_kernel_with_sqrt KR;
typedef CGAL::Exact_predicates_inexact_constructions_kernel IK;
//typedef CGAL::Min_circle_2_traits_2<KR> Traits;
//typedef CGAL::Min_circle_2<Traits> Min_circle;

// Change when use different kernels!
typedef long long lint;
typedef IK::Point_2 Pt;
typedef IK::Point_3 Pt3;
typedef IK::Ray_2 Ray;
typedef IK::Vector_2 Vec;
typedef IK::Segment_2 Seg;

// Triangulation
typedef int ind_t; // not a good one...

//typedef CGAL::Triangulation_vertex_base_with_info_2<ind_t, IK>	Vb;
//typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
//typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
//typedef Delaunay::Finite_faces_iterator		Face_iterator;
//typedef Delaunay::Finite_edges_iterator		Edge_iterator;
//typedef Delaunay::Vertex_handle		Vertex_handle;
//typedef Delaunay::Point		DPt;

// Boost
typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
	boost::no_property, boost::property < boost::edge_weight_t, lint > > Graph;
typedef boost::property_map < Graph, boost::edge_weight_t >::type WeightMap;
typedef boost::graph_traits < Graph >::edge_descriptor Edge;
typedef boost::graph_traits < Graph >::edge_iterator EdgeIt;
typedef boost::graph_traits < Graph >::out_edge_iterator OutEdgeIt;
typedef boost::graph_traits < Graph >::vertex_descriptor Vertex;
//typedef std::pair<int, int> E;


#define _o std::cout
#define _l std::endl
#define _i std::cin
#define _e std::cerr

double floor_to_double(const CGAL::Quotient<ET>& x)
{
	double a = std::floor(CGAL::to_double(x));
	while (a > x) a -= 1;
	while (a + 1 <= x) a += 1;
	return a;
}

double ceil_to_double(const CGAL::Quotient<ET>& x)
{
	double a = std::ceil(CGAL::to_double(x));
	while (a < x) a += 1;
	while (a - 1 >= x) a -= 1;
	return a;
}


struct MyRay {
	Ray r;
	int idx;
	MyRay(Ray r=Ray(), int i=0):r(r),idx(i){}
	MyRay(Pt src, Pt next, int i) {
		r = Ray(src, next);
		idx = i;
	}
};
bool CompareRayByY0(const MyRay& r1, const MyRay& r2) {
	return r1.r.source().y() > r2.r.source().y();
}
int whoWins(const std::vector<MyRay>& rays, int oldone, int newone) {
	Vec vo = rays[oldone].r.to_vector();
	Vec vn = rays[newone].r.to_vector();
	if (vo.y() >= 0 && vn.y() >= 0) {
		return oldone;
	}
	if (vo.y() < 0 && vn.y() < 0) {
		return newone;
	}
	if (vo.y() >= 0 && vn.y() < 0) {
		return (vo.y() * vn.x() + vo.x() * vn.y() > 0) ? newone : oldone;
	}
	if (vo.y() < 0 && vn.y() >= 0) {
		return (vo.y() * vn.x() + vo.x() * vn.y() > 0) ? oldone : newone;
	}
	return -1;
}
int rayChallenge(Ray& rold, Ray& rnew) {
	// rold.y0 > rnew.y0
	// return 0 if old one wins
	// return 1 if new one wins
	Vec vo = rold.to_vector();
	Vec vn = rnew.to_vector();
	if (vo.y() >= 0 && vn.y() >= 0) {
		return 0;
	}
	if (vo.y() < 0 && vn.y() < 0) {
		return 1;
	}
	if (vo.y() >= 0 && vn.y() < 0) {
		Seg so(rold.source(), rold.source() + vo);
		Seg sn(rnew.source(), Pt(rnew.source().x() + vn.x(), rnew.source().y() - vn.y()));
		CGAL::Comparison_result cr = CGAL::compare_slopes(so, sn);
		//_e << " _" << cr << "_ ";
		return (cr == CGAL::LARGER ? 1 : 0);
		//return (vo.y() * vn.x() + vo.x() * vn.y() > 0) ? 1 : 0;
	}
	if (vo.y() < 0 && vn.y() >= 0) {
		Seg so(rold.source(), Pt(rold.source().x() + vo.x(), rold.source().y() - vo.y()));
		Seg sn(rnew.source(), rnew.source() + vn);
		CGAL::Comparison_result cr = CGAL::compare_slopes(sn, so);
		//_e << " _" << cr << "_ ";
		return (cr == CGAL::LARGER ? 0 : 1);
	}
	return 0;
}
void Motorcycles() {
	int n; _i >> n;
	_e << n << _l;
	std::vector<MyRay> rays(n);
	for (int i = 0; i < n; i++) {
		lint y0, x1, y1;
		_i >> y0 >> x1 >> y1;
		rays[i] = MyRay(Pt(0, y0), Pt(x1, y1), i);
	}
	std::sort(rays.begin(), rays.end(), CompareRayByY0);

	std::stack<MyRay> st_rays;
	st_rays.push(rays[0]);
	for (int i = 1; i < n; i++) {
		MyRay ray = rays[i];
		while (!st_rays.empty()) {
			MyRay topray = st_rays.top();
			if (!CGAL::do_intersect(ray.r, topray.r)) {
				st_rays.push(ray);
				//_e << ray.idx << " in stack\n";
				break;
			}
			else {
				//_e << topray.idx << ":" << topray.r.to_vector() << "---" << ray.idx << ":" << ray.r.to_vector();
				int who = rayChallenge(topray.r, ray.r);
				//_e << " \twinner:" << ((who==0)?topray.idx:ray.idx) << _l;
				if (who == 0) break;
				else {
					//_e << topray.idx << " out of stack\n";
					st_rays.pop();
				}
			}
		}
		if (st_rays.empty()) {
			st_rays.push(ray);
			//_e << ray.idx << " in empty stack\n";
		}
	}
	//_e << _l;
	std::vector<int> alives;
	while (!st_rays.empty()) {
		alives.push_back(st_rays.top().idx);
		st_rays.pop();
	}
	std::sort(alives.begin(), alives.end());
	std::vector<int>::iterator ait = alives.begin();
	for (; ait != alives.end(); ++ait) {
		_o << *ait << " ";
	}
	_o << _l;
	return;
}

void testUnionFind();

int main(int argc, char** argv) {
	std::ios_base::sync_with_stdio(false);
	if (argc > 1) {
		std::string str("C:\\M.K.S.H\\ETH\\AlgoLab\\week6\\potw\\motorcycles\\");
		str += std::string(argv[1]) + ".in";
		freopen(str.c_str(), "r", stdin);
	}
	else freopen("C:\\M.K.S.H\\ETH\\AlgoLab\\week6\\potw\\motorcycles\\test1.in", "r", stdin);
	freopen("C:\\M.K.S.H\\ETH\\AlgoLab\\week6\\potw\\motorcycles\\out_my.out", "w", stdout);
	freopen("C:\\M.K.S.H\\ETH\\AlgoLab\\week6\\potw\\motorcycles\\err_my.out", "w", stderr);
	int t;
	_i >> t;
	while (t--) {
		Motorcycles();
	}
	return 0;
}

void testUnionFind() {
	UnionFind uf(9);
	uf.unionSets(1, 3);
	uf.unionSets(1, 9);
	uf.unionSets(5, 6);
	uf.unionSets(8, 9);
	uf.unionSets(7, 8);
	uf.unionSets(5, 8);
	_e << uf.toString() << _l;
	return;
}

// Week 8: Germs / 100 pts
// Nearest neighbor
void Germs(int n) {
	typedef CGAL::Triangulation_vertex_base_with_info_2<int, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Finite_vertices_iterator	Vertex_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point				DPt;
	typedef Delaunay::Vertex_circulator Vertex_circulator;

	int l, b, r, t;
	_i >> l >> b >> r >> t;

	std::vector< std::pair<Pt, int> > pts(n);
	std::vector<lint> mind2(n);
	for (int i = 0; i < n; i++) {
		int x, y;
		_i >> x >> y;
		lint dl = std::abs(x - l);
		lint dr = std::abs(x - r);
		lint db = std::abs(y - b);
		lint dt = std::abs(y - t);
		lint md = std::min(std::min(dl, dr), std::min(db, dt));
		mind2[i] = md*md * 4;
		pts[i] = std::make_pair(Pt(x, y), i);
	}
	lint fd2, md2, ld2;
	if (n > 1) {
		Delaunay D;
		D.insert(pts.begin(), pts.end());

		Vertex_iterator vit = D.finite_vertices_begin(), vend = D.finite_vertices_end();
		for (; vit != vend; ++vit) {
			int uind = vit->info();
			Pt up = vit->point();
			lint md2 = mind2[uind];
			Vertex_circulator vc(D.incident_vertices(vit)), done(vc);
			do {
				if (D.is_infinite(vc)) continue;
				Pt vp = vc->point();
				lint d2 = CGAL::squared_distance(vp, up);
				md2 = std::min(d2, md2);
			} while (++vc != done);
			mind2[uind] = md2;
		}
		std::sort(mind2.begin(), mind2.end());
	}

	fd2 = mind2[0], md2 = mind2[n / 2], ld2 = mind2[n - 1];
	double tf = std::sqrt((std::sqrt(fd2) - 1) / 2);
	double tm = std::sqrt((std::sqrt(md2) - 1) / 2);
	double tl = std::sqrt((std::sqrt(ld2) - 1) / 2);
	int tfi = std::ceil(tf);
	int tmi = std::ceil(tm);
	int tli = std::ceil(tl);
	_o << tfi << " " << tmi << " " << tli << _l;
	return;

}



// Week 8: H1N1 / incorrect 100pts?
// Find the maximum width of the path from outside to the vertex
void H1N1(int n) {
	// Boost
	typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
		boost::no_property, boost::property < boost::edge_weight_t, long > > Graph;
	typedef boost::property_map < Graph, boost::edge_weight_t >::type WeightMap;
	typedef boost::graph_traits < Graph >::edge_descriptor Edge;
	typedef boost::graph_traits < Graph >::edge_iterator EdgeIt;
	typedef boost::graph_traits < Graph >::out_edge_iterator OutEdgeIt;
	typedef boost::graph_traits < Graph >::vertex_descriptor Vertex;
	// CGAL
	typedef CGAL::Triangulation_vertex_base_2<IK>	Vb;
	typedef CGAL::Triangulation_face_base_with_info_2<int, IK>	Fb;
	typedef CGAL::Triangulation_data_structure_2<Vb, Fb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Face_handle				Face_handle;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Edge_circulator			Edge_circulator;
	typedef Delaunay::Finite_vertices_iterator	Vertex_iterator;
	typedef Delaunay::Vertex_handle				Vertex_handle;
	typedef Delaunay::Point						DPt;
	typedef Delaunay::Vertex_circulator			Vertex_circulator;

	int m;

	std::vector<Pt> infected(n);
	for (int i = 0; i < n; i++) {
		int x, y;
		_i >> x >> y;
		infected[i] = Pt(x, y);
	}
	Delaunay D;
	D.insert(infected.begin(), infected.end());

	Graph G(1); // only infinite face
	WeightMap wmap = boost::get(boost::edge_weight, G); // weight = width^2 = r^2*4
	int newind = 1; // gradually add faces

	Face_iterator fit = D.finite_faces_begin(), fend = D.finite_faces_end();
	for (; fit != fend; ++fit) {
		fit->info() = 0; // or it could be anything
	}

	fit = D.finite_faces_begin(), fend = D.finite_faces_end();
	for (; fit != fend; ++fit) {
		Vertex u;
		if (!fit->info()) {
			u = boost::add_vertex(G);
			fit->info() = newind++;
		}
		else u = fit->info();
		// circulate its 3 neighbors to add edges to the graph
		for (int nb = 0; nb < 3; nb++) {
			Face_handle fh = fit->neighbor(nb);
			if (D.is_infinite(fh)) {
				// infinite face: add edge to vertex 0
				Vertex v = 0;
				Edge e; bool su;
				Vertex_handle vh1 = fit->vertex(fit->cw(nb)), vh2 = fit->vertex(fit->ccw(nb));
				lint d2 = CGAL::squared_distance(vh1->point(), vh2->point());
				boost::tie(e, su) = boost::add_edge(u, v, G);
				wmap[e] = d2;
			}
			else {
				//  if the face hasn't been visited, add a new vertex and fill fh->info()
				Vertex v;
				if (!fh->info()) {
					fh->info() = newind++;
					v = boost::add_vertex(G);
				}
				else v = fh->info();

				// continue if the edge already exists
				Edge e; bool su;
				boost::tie(e, su) = boost::edge(u, v, G);
				if (su) continue;

				Vertex_handle vh1 = fit->vertex(fit->cw(nb)), vh2 = fit->vertex(fit->ccw(nb));
				lint d2 = CGAL::squared_distance(vh1->point(), vh2->point());
				boost::tie(e, su) = boost::add_edge(u, v, G);
				wmap[e] = d2;
			}
		}
	}

	const lint BIG = 10000000000000000;
	typedef std::pair<lint, Vertex> DistV;
	int nv = boost::num_vertices(G);
	std::vector<DistV> vdist(nv);
	for (int i = 0; i < nv; i++) vdist[i] = std::make_pair(-1, i);

	std::vector<bool> selected(nv, false); // whether the width of a vertex has been optimized
	std::vector<lint> distmap(nv, -1); // the maximum width towards each vertex
	OutEdgeIt eit, eend;
	for (boost::tie(eit, eend) = boost::out_edges(0, G); eit != eend; eit++) {
		Vertex v = boost::target(*eit, G);
		vdist[v].first = std::max(vdist[v].first, (lint)wmap[*eit]);
		distmap[v] = std::max(distmap[v], (lint)wmap[*eit]);
	}
	vdist[0].first = 0;


	_e << "BFS " << _l;
	// BFS for max min edge
	std::priority_queue < DistV > pq(vdist.begin(), vdist.end());
	selected[0] = true;
	distmap[0] = BIG;
	while (!pq.empty()) {
		DistV dv = pq.top();
		pq.pop();
		lint d = dv.first;
		Vertex u = dv.second;
		if (selected[u]) continue; // see the pq.push() below, one vertex could be pushed multiple times
		OutEdgeIt eit, eend;
		for (boost::tie(eit, eend) = boost::out_edges(u, G); eit != eend; eit++)
		{
			Vertex v = boost::target(*eit, G);
			if (!selected[v]) {
				// the updating rule: d[v] = max(d[v], min(w[e], d[u]))
				lint curw = std::max((long)distmap[v], std::min(wmap[*eit], (long)distmap[u]));
				distmap[v] = curw;
				pq.push(std::make_pair(distmap[v], v));
			}
		}
		selected[u] = true;
	}

	_i >> m;
	for (int j = 0; j < m; j++) {
		int x, y; lint r2;
		_i >> x >> y >> r2;
		Pt person(x, y);
		Vertex_handle vh = D.nearest_vertex(person);
		if (CGAL::squared_distance(person, vh->point()) < r2) {
			_o << "n"; continue;
		}
		Face_handle fh = D.locate(person);
		if (D.is_infinite(fh)) {
			_o << "y"; continue;
		}
		Vertex u = fh->info();
		if (r2 * 4 > distmap[u]) _o << "n";
		else _o << "y";
	}
	_o << _l;
}



// Week 8: Graypes / 50->50->50->100
// Delaunay, find shortest edge
// Use Vertex_iterator to iterate through the vertices -> O(1)
// rather than nearest_vertex() -> O(log n)
// Tho I didn't they would kill an O(nlogn) algo..
// Don't play with constant when there is a method to improve asymptotic
void Graypes(int n) {
	typedef CGAL::Triangulation_vertex_base_with_info_2<int, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Finite_vertices_iterator	Vertex_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point				DPt;
	typedef Delaunay::Vertex_circulator Vertex_circulator;


	std::vector< std::pair<Pt, int> > apes(n);
	for (int i = 0; i < n; i++) {
		int x, y;
		_i >> x >> y;
		apes[i] = std::make_pair(Pt(x, y), i);
	}
	//std::random_shuffle(apes.begin(), apes.end());

	Delaunay D;
	D.insert(apes.begin(), apes.end());

	const lint BIG = 10000000000000000;
	//std::vector<int> runto(n, -1);
	//std::vector<lint> d2runto(n, BIG);
	lint totalmind2 = BIG;

	Vertex_iterator vit = D.finite_vertices_begin(), vend = D.finite_vertices_end();
	for (; vit != vend; ++vit) {
		Pt p = vit->point();

		Vertex_circulator vc = D.incident_vertices(vit), done(vc);
		do {
			if (D.is_infinite(vc))continue;
			Pt q = vc->point();
			lint d2pq = CGAL::squared_distance(p, q);
			totalmind2 = std::min(totalmind2, d2pq);
		} while (++vc != done);
	}

	/* O(nlogn) because of nearest_vertex()
	for (int i = 0; i < n; i++) {
	//lint mind2 = d2runto[i];
	//int prunto = runto[i];
	lint mind2 = BIG;
	Pt p = apes[i].first;
	int pind = apes[i].second;
	Vertex_handle vh = D.nearest_vertex(p);
	Vertex_circulator vc = D.incident_vertices(vh), done(vc);
	do {
	if (D.is_infinite(vc)) continue;
	Pt q = vc->point();
	int qind = vc->info();
	if (qind < pind) continue;
	lint d2pq = CGAL::squared_distance(p, q);
	if (d2pq < mind2) {
	mind2 = d2pq;
	//prunto = qind;
	}
	//else if (d2pq == mind2) {
	//	Pt prevbest = apes[prunto].first;
	//	if (q.x() < prevbest.x() || (q.x() == prevbest.x() && q.y() < prevbest.y())) {
	//		prunto = qind;
	//	}
	//}
	} while (++vc != done);
	//if (prunto != runto[i]) {
	//	runto[i] = prunto;
	//	d2runto[i] = mind2;
	//	if (mind2 < d2runto[prunto]) {
	//		runto[prunto] = i;
	//		d2runto[prunto] = mind2;
	//	}
	//	else if (mind2 == d2runto[prunto]) {
	//		Pt p2 = apes[runto[prunto]].first;
	//		if (p.x() < p2.x() || (p.x() == p2.x() && p.y() < p2.y())) {
	//			runto[prunto] = i;
	//		}
	//	}
	//}
	totalmind2 = std::min(totalmind2, mind2);
	}
	*/

	lint time = std::ceil(50 * std::sqrt((double)(totalmind2)));
	_o << time << _l;
	return;
}



// Week 11 PotW: Sith / 25->50->100pts
// Delaunay + find connected components
// Update connected components: Union Find
int calcBiggestComponent(const std::vector<int>& comp, int ncomp) {
	int n = comp.size();
	std::vector<int> counter(ncomp);
	for (int i = 0; i < n; i++) {
		counter[comp[i]]++;
	}
	int largest = 0;
	for (int j = 0; j < ncomp; j++) {
		largest = std::max(largest, counter[j]);
	}
	return largest;
}
void Comp2Par(const std::vector<int>& comp, int ncomp, std::vector<int>& par) {
	int n = comp.size();
	std::vector<int> first(ncomp, -1);
	for (int i = 0; i < n; i++) {
		if (first[comp[i]] == -1)
			first[comp[i]] = i;
		par[i] = first[comp[i]];
	}
}
void Sith() {
	typedef CGAL::Triangulation_vertex_base_with_info_2<int, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Finite_vertices_iterator	Vertex_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point				DPt;
	typedef Delaunay::Vertex_circulator Vertex_circulator;

	typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
		boost::no_property, boost::property < boost::edge_weight_t, double > > Graph;
	typedef boost::property_map < Graph, boost::edge_weight_t >::type WeightMap;
	typedef boost::graph_traits < Graph >::edge_descriptor Edge;
	typedef boost::graph_traits < Graph >::vertex_descriptor Vertex;

	int n, r;
	_i >> n >> r;
	_e << "testcase: " << n << " " << r << _l;
	lint r2 = (lint)r*r;
	std::vector< std::pair<Pt, int> > p(n);
	// invert the input
	// so I choose planets [0, k) rather than [k, end)
	for (int i = 0; i < n; i++) {
		int x, y;
		_i >> x >> y;
		p[n - 1 - i] = std::make_pair(Pt(x, y), n - 1 - i);
	}

	Delaunay D;
	int nv = n / 2;
	D.insert(p.begin(), p.begin() + nv);
	Graph G(nv);
	for (int i = 0; i < nv; i++) {
		Vertex_handle vh = D.nearest_vertex(p[i].first);
		Pt pt = vh->point();
		int ipt = vh->info();
		Vertex_circulator vc = D.incident_vertices(vh), done(vc);
		do {
			if (D.is_infinite(vc)) continue;
			Pt pin = vc->point();
			int ipin = vc->info();
			if (ipin < ipt) continue; // i --> j, add edge when i < j
			lint d2 = CGAL::squared_distance(pt, pin);
			if (d2 <= r2) {
				boost::add_edge(ipt, ipin, G);
			}
		} while (++vc != done);
	}

	std::vector<int> comp(nv), par(nv);
	int ncomp = boost::connected_components(G, &comp[0]);
	int biggestComp = calcBiggestComponent(comp, ncomp);
	Comp2Par(comp, ncomp, par);
	UnionFind uf(par);

	for (int last = nv; last < n; last++) {
		int largestPossible = n - last - 1;
		if (biggestComp >= largestPossible) break;
		Vertex vlast = boost::add_vertex(G);
		Pt plast = p[last].first; // p[last].second == last
		D.insert(p.begin() + last, p.begin() + last + 1);
		int ipt = last;
		Vertex_handle vh = D.nearest_vertex(plast);
		Vertex_circulator vc = D.incident_vertices(vh), done(vc);
		uf.append();
		do {
			if (D.is_infinite(vc)) continue;
			Pt pin = vc->point();
			int ipin = vc->info();
			lint d2 = CGAL::squared_distance(plast, pin);
			if (d2 <= r2) {
				boost::add_edge(ipt, ipin, G);
				uf.unionSets(ipt, ipin);
			}
		} while (++vc != done);

		//std::vector<int> ccomp(last+1);
		//int nccomp = boost::connected_components(G, &ccomp[0]);
		//int largest = calcBiggestComponent(ccomp, nccomp);
		int largest = uf.getMaxSize();
		largest = std::min(largest, largestPossible);
		biggestComp = std::max(biggestComp, largest);
	}
	_e << "result: " << biggestComp << _l;
	_o << biggestComp << _l;
	return;

}



// Week 12: Radiation / 60->80->100
// LP + bin_search?? 2^300??
// LP (with Gmpz not Gmpq) + exp_search+bin_search
// they are exact number types and don't worry about 2^300
struct PolyTerm {
	int xd;
	int yd;
	int zd;
	int idx;
	PolyTerm(int x = 0, int y = 0, int z = 0, int idx = 0) :xd(x), yd(y), zd(z), idx(idx) {}
};
void calcPolyTerm(int deg, std::vector<PolyTerm> &terms) {
	//int balls = deg + 2;
	terms.clear();
	int idx = 0;
	int d = deg;
	for (int d = 0; d <= deg; d++) {
		int balls = d + 2;
		for (int i = 0; i < balls - 1; i++) {
			for (int j = i + 1; j < balls; j++) {
				PolyTerm pt(i, j - i - 1, d + 1 - j, idx);
				terms.push_back(pt);
				idx++;
			}
		}
	}
	return;
}
typedef CGAL::Gmpz ETZ;
typedef CGAL::Quadratic_program<ETZ> ProgramZ;
typedef CGAL::Quadratic_program_solution<ETZ> SolutionZ;
ETZ findPoly(int deg, std::vector<Pt3> &hcell, std::vector<Pt3> &tcell, std::vector< std::vector<ETZ> >& hpowers, std::vector< std::vector<ETZ> >& tpowers) {

	ProgramZ lp(CGAL::SMALLER, false, 0, false, 0);
	std::vector<PolyTerm> terms;
	calcPolyTerm(deg, terms);

	int h = hcell.size(), t = tcell.size();
	int nterms = terms.size();
	const int delta = nterms;
	for (int j = 0; j < nterms; j++) {
		//lp.set_c(j, 1);
		int xind = terms[j].xd, yind = 31 + terms[j].yd, zind = 62 + terms[j].zd;
		for (int i = 0; i < h; i++) {
			ETZ xyz = hpowers[i][xind] * hpowers[i][yind] * hpowers[i][zind];
			lp.set_a(j, i, xyz);
		}
		for (int i = 0; i < t; i++) {
			ETZ xyz = tpowers[i][xind] * tpowers[i][yind] * tpowers[i][zind];
			lp.set_a(j, h + i, -xyz);
		}
	}
	lp.set_c(delta, -1);
	//lp.set_l(delta, true, 0);
	lp.set_u(delta, true, 1);
	for (int i = 0; i < h; i++) {
		lp.set_b(i, 0);
		lp.set_a(delta, i, 0);
	}
	for (int i = 0; i < t; i++) {
		lp.set_a(delta, h + i, 1);
		lp.set_b(h + i, 0);
	}

	SolutionZ s = CGAL::solve_linear_program(lp, ETZ());
	//if (s.is_optimal() && s.objective_value() < 0)
	//	return true;
	//return false;
	ETZ result = s.objective_value().numerator() / s.objective_value().denominator();
	return result;
}
void calcPowers(std::vector<Pt3> & cell, std::vector< std::vector<ETZ> >& powers) {
	int n = cell.size();
	_e << "powers!" << _l;
	for (int i = 0; i < n; i++) {
		powers[i] = std::vector<ETZ>(93);
		ETZ xp(1), yp(1), zp(1);
		int cx = (int)cell[i].x();
		int cy = (int)cell[i].y();
		int cz = (int)cell[i].z();
		for (int d = 0; d <= 30; d++) {
			powers[i][d] = xp;
			powers[i][31 + d] = yp;
			powers[i][62 + d] = zp;
			if (d == 30) break;
			xp *= cx;
			yp *= cy;
			zp *= cz;
			//_e << xp << " " << yp << " " << zp << _l;
		}
	}
}
void Radiation() {
	int h, t; _i >> h >> t;
	std::vector<Pt3> hcell(h), tcell(t);
	for (int i = 0; i < h; i++) {
		int x, y, z; _i >> x >> y >> z;
		hcell[i] = Pt3(x, y, z);
		//_e << hcell[i] << _l;
	}
	for (int j = 0; j < t; j++) {
		int x, y, z; _i >> x >> y >> z;
		tcell[j] = Pt3(x, y, z);
		//_e << tcell[j] << _l;
	}
	if (h == 0 || t == 0) {
		_o << 0 << _l;
		return;
	}

	std::vector< std::vector<ETZ> > hpowers(h), tpowers(t);
	calcPowers(hcell, hpowers);
	calcPowers(tcell, tpowers);
	_e << "calcpowers!" << _l;

	//std::vector<bool> canFinds(31, false);
	std::vector<ETZ> res(31, 0);
	int st = 0, ed = 1;
	int low, up, mid;
	while (true) {
		_e << "d=" << ed << _l;
		//canFinds[ed] = canFindPoly(ed, hcell, tcell, hpowers, tpowers);
		res[ed] = findPoly(ed, hcell, tcell, hpowers, tpowers);
		if (res[ed] < 0) {
			low = st;
			up = ed;
			mid = (low + up) / 2;
			break;
		}
		else {
			if (ed == 30) {
				_o << "Impossible!\n";
				return;
			}
			st = ed;
			ed = std::min(30, ed * 2);
		}
	}

	// binary search
	while (true) {
		_e << "d=" << mid << _l;
		if (up - low <= 1) {
			if (res[low]<0 || findPoly(low, hcell, tcell, hpowers, tpowers)<0) {
				_o << low << _l;
				return;
			}
			else if (res[up]<0 || findPoly(up, hcell, tcell, hpowers, tpowers)<0) {
				_o << up << _l;
				return;
			}
		}

		res[mid] = findPoly(mid, hcell, tcell, hpowers, tpowers);
		if (res[mid]<0) {
			up = mid;
			mid = (low + up) / 2;
		}
		else {
			low = mid + 1;
			mid = (low + up) / 2;
		}
	}

	_e << _l;
	_o << "Impossible!" << _l;
	return;

}



// Week 13: Clues / 100pts
// Delaunay + is_bipartite + connected_components
void Clues() {
	typedef CGAL::Triangulation_vertex_base_with_info_2<int, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Finite_vertices_iterator	Vertex_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point				DPt;
	typedef Delaunay::Vertex_circulator Vertex_circulator;

	typedef boost::adjacency_list < boost::vecS, boost::vecS, boost::undirectedS,
		boost::no_property, boost::property < boost::edge_weight_t, double > > Graph;
	typedef boost::property_map < Graph, boost::edge_weight_t >::type WeightMap;
	typedef boost::graph_traits < Graph >::edge_descriptor Edge;
	typedef boost::graph_traits < Graph >::vertex_descriptor Vertex;


	int n, m, r;
	_i >> n >> m >> r;
	lint r2 = (lint)r*r;
	std::vector< std::pair<Pt, int> > stations(n);
	std::vector< std::pair<Pt, Pt> > clues(m);
	for (int i = 0; i < n; i++) {
		int x, y; _i >> x >> y;
		stations[i] = std::make_pair(Pt(x, y), i);
	}
	for (int j = 0; j < m; j++) {
		int xa, ya, xb, yb; _i >> xa >> ya >> xb >> yb;
		clues[j] = std::make_pair(Pt(xa, ya), Pt(xb, yb));
	}

	Graph G(n);
	std::vector<int> components(n);

	Delaunay D;
	D.insert(stations.begin(), stations.end());
	Vertex_iterator vit;
	bool violated = false;
	for (vit = D.finite_vertices_begin(); vit != D.finite_vertices_end(); ++vit) {
		Vertex_circulator vc = D.incident_vertices(vit), done(vc);
		int idx = vit->info();
		std::vector< std::pair<Pt, int> > candidates;
		candidates.push_back(std::make_pair(vit->point(), vit->info()));
		do {
			if (!D.is_infinite(vc)) {
				int vcidx = vc->info();
				//if (vcidx < idx) continue;
				if (CGAL::squared_distance(vc->point(), vit->point()) > r2) continue;
				//boost::add_edge(idx, vcidx, G);
				candidates.push_back(std::make_pair(vc->point(), vcidx));
			}
		} while (++vc != done);
		int ncand = candidates.size();
		for (int i = 1; i < ncand; i++) {
			Pt pi = candidates[i].first;
			for (int j = i + 1; j < ncand; j++) {
				Pt pj = candidates[j].first;
				if (CGAL::squared_distance(pi, pj) <= r2) {
					violated = true;
					break;
				}
			}
		}
		if (violated) break;
		for (int j = 1; j < ncand; j++) {
			int idxj = candidates[j].second;
			boost::add_edge(idx, idxj, G);
		}
	}

	if (violated) {
		for (int j = 0; j < m; j++) {
			_o << "n";
		}
		_o << _l;
		_e << "violated" << _l;
		return;
	}

	bool isBipartite = boost::is_bipartite(G);
	if (!isBipartite) {
		for (int j = 0; j < m; j++) {
			_o << "n";
		}
		_o << _l;
		_e << "n" << _l;
		return;
	}

	boost::connected_components(G, &components[0]);
	for (int i = 0; i < n; i++) {
		_e << components[i] << " ";
	}_e << _l;
	for (int j = 0; j < m; j++) {
		Pt a = clues[j].first, b = clues[j].second;
		if (CGAL::squared_distance(a, b) <= r2) {
			_o << "y";
			continue;
		}
		Vertex_handle vha = D.nearest_vertex(a);
		Vertex_handle vhb = D.nearest_vertex(b);
		// not reachable to any station
		if (CGAL::squared_distance(vha->point(), a) > r2
			|| CGAL::squared_distance(vhb->point(), b) > r2) {
			_o << "n";
			continue;
		}
		// not in the same component
		int idxa = vha->info(), idxb = vhb->info();
		if (components[idxa] == components[idxb]) {
			_o << "y";
			//_e << vha->point() << "|" << vhb->point() << _l;
			//_e << components[idxa] << " " << components[idxb] << _l;
		}
		else _o << "n";
	}
	_o << _l;
	return;

}



// Week 13: Goldfinger / 100 pts
// LP + Delaunay + bin_search
typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
typedef Delaunay::Finite_faces_iterator		Face_iterator;
typedef Delaunay::Finite_edges_iterator		Edge_iterator;
typedef Delaunay::Vertex_handle		Vertex_handle;
typedef Delaunay::Point		DPt;
bool isSolvable(int a, std::vector<Pt> &psensor, std::vector<int> &esensor,
		std::vector<Pt> &pmpe, std::vector<lint> &r2mpe, int Imax, std::vector< std::vector<lint> >& d2) {
	int n = psensor.size();
	int m = pmpe.size();
	bool isRestricted = r2mpe[0] > 0;

	Program lp(CGAL::LARGER, true, 0, false);
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < a; j++) {
			//lint d2 = CGAL::squared_distance(pmpe[j], psensor[i]);
			if (!isRestricted || d2[i][j] < r2mpe[j])
				lp.set_a(j, i, (ET)1 / d2[i][j]);
		}
		lp.set_b(i, esensor[i]);
	}
	for (int j = 0; j < a; j++) {
		lp.set_a(j, n, -1);
		lp.set_c(j, 1);
	}
	lp.set_b(n, -Imax);

	Solution s = CGAL::solve_linear_program(lp, ET());
	if (s.is_optimal()) {
		//_o << a << _l;
		return true;
	}
	else {
		return false;
	}

}
void Goldfinger() {
	int n, m, h, Imax;
	_i >> n >> m >> h >> Imax;
	std::vector<Pt> psensor(n);
	std::vector<Pt> pmpe(m);
	std::vector<Pt> phench(h);
	std::vector<int> esensor(n);
	lint BIG = (1 << 55);
	std::vector<lint> r2mpe(m, -1);
	std::vector< std::vector<lint> > d2(n);

	for (int i = 0; i < n; i++) {
		int x, y, e; _i >> x >> y >> e;
		psensor[i] = Pt(x, y);
		esensor[i] = e;
	}
	for (int j = 0; j < m; j++) {
		int x, y; _i >> x >> y;
		pmpe[j] = Pt(x, y);
	}
	for (int k = 0; k < h; k++) {
		int x, y; _i >> x >> y;
		phench[k] = Pt(x, y);
	}


	Delaunay D;
	D.insert(phench.begin(), phench.end());
	if (h > 0) {
		for (int j = 0; j < m; j++) {
			Vertex_handle vh = D.nearest_vertex(pmpe[j]);
			r2mpe[j] = CGAL::squared_distance(vh->point(), pmpe[j]);
		}
	}

	for (int i = 0; i < n; i++) {
		d2[i] = std::vector<lint>(m);
		for (int j = 0; j < m; j++) {
			d2[i][j] = CGAL::squared_distance(psensor[i], pmpe[j]);
		}
	}

	if (isSolvable(1, psensor, esensor, pmpe, r2mpe, Imax, d2)) {
		_o << 1 << _l;
		return;
	}

	
	// exp. search for an interval
	std::vector<int> solvables(m + 1, 0); // 0 = not touched, 1 = solvable, -1 = unsolvable
										  //solvables[m] = 1; 
	solvables[1] = -1;
	int st = 1, end = 2;
	while (end <= m) {
		_e << "end=" << end << _l;
		if (solvables[end] == 1 || isSolvable(end, psensor, esensor, pmpe, r2mpe, Imax, d2)) {
			solvables[end] = 1;
			break;
		}
		else {
			solvables[end] = -1;
			if (end == m) break;
			st = end;
			end = std::min(end * 2, m);
		}
	}
	if (solvables[m] == -1) {
		_o << "impossible" << _l;
		return;
	}

	// binary search for the best
	int low = st, up = end, a = (low + up) / 2;
	while (true) {
		_e << "a=" << a << _l;
		if (up - low <= 1) {
			if (solvables[low] == 1 || isSolvable(low, psensor, esensor, pmpe, r2mpe, Imax, d2)) {
				_o << low << _l;
				return;
			}
			if (solvables[up] == 1 || isSolvable(up, psensor, esensor, pmpe, r2mpe, Imax, d2)) {
				_o << up << _l;
				return;
			}
			break; // impossible
		}

		bool solvable = isSolvable(a, psensor, esensor, pmpe, r2mpe, Imax, d2);
		if (solvable) {
			solvables[a] = 1;
			up = a;
			a = (low + up) / 2;
		}
		else {
			solvables[a] = -1;
			low = a;
			a = (low + up) / 2;
		}

	}

	_o << "impossible" << _l;
	return;

}



// Week 3: First Hit / 99->100
// For 5555 pts total!
// OMG really?? random shuffle??
double floor_to_double_EK(const EK::FT& x)
{
	double a = std::floor(CGAL::to_double(x));
	while (a > x) a -= 1;
	while (a + 1 <= x) a += 1;
	return a;
}
void FirstHit(int n) {

	lint x, y, a, b, r, s, t, u;
	std::cin >> x >> y >> a >> b;
	IK::Point_2 p1(x, y), p2(a, b);
	IK::Ray_2 ray(p1, p2);
	EK::Point_2 ep1((double)x, (double)y), ep2((double)a, (double)b);
	EK::Ray_2 eray(ep1, ep2);
	EK::Segment_2 eseg;

	bool ishit = false;
	EK::FT minsqd = 5e100;
	EK::Point_2 minits(0, 0), curits(0, 0);

	std::vector<EK::Segment_2> esegs(n);
	for (int i = 0; i < n; i++) {
		_i >> r >> s >> t >> u;
		EK::Point_2 eq1((double)r, (double)s), eq2((double)t, (double)u);
		EK::Segment_2 esegq(eq1, eq2);
		esegs[i] = esegq;
	}
	std::random_shuffle(esegs.begin(), esegs.end());

	for (int i = 0; i < n; i++) {
		EK::Segment_2 esegq = esegs[i];
		EK::Point_2 eq1 = esegq.start(), eq2 = esegq.end();
		if (ishit) {
			if (CGAL::do_intersect(eseg, esegq)) {
				auto result = CGAL::intersection(eseg, esegq);

				if (const EK::Segment_2* sp = boost::get<EK::Segment_2>(&*result)) {
					_e << "segment" << _l;
					EK::FT sqd1 = CGAL::squared_distance(ep1, eq1);
					EK::FT sqd2 = CGAL::squared_distance(ep1, eq2);
					if (sqd1 < sqd2) {
						minits = eq1;
					}
					else {
						minits = eq2;
					}
				}
				else if (const EK::Point_2* pp = boost::get<EK::Point_2>(&*result)) {
					_e << "point" << _l;
					minits = *pp;
				}
				eseg = EK::Segment_2(ep1, minits);
			}
		}
		else {
			if (CGAL::do_intersect(eray, esegq)) {
				auto result = CGAL::intersection(eray, esegq);
				if (const EK::Segment_2* sp = boost::get<EK::Segment_2>(&*result)) {
					_e << "segment0" << _l;
					EK::FT sqd1 = CGAL::squared_distance(ep1, eq1);
					EK::FT sqd2 = CGAL::squared_distance(ep1, eq2);
					if (sqd1 < sqd2) {
						minits = eq1;
					}
					else if (sqd2 < sqd1) {
						minits = eq2;
					}
				}
				else if (const EK::Point_2* pp = boost::get<EK::Point_2>(&*result)) {
					minits = *pp;
				}
				eseg = EK::Segment_2(ep1, minits);
				ishit = true;
			}
		}
	}

	if (!ishit) {
		std::cout << "no" << std::endl;
		return;
	}
	std::cout << (lint)floor_to_double_EK(minits.x()) << " " << (lint)floor_to_double_EK(minits.y()) << std::endl;

	return;
}



// Week 13, PotW: World Cup / 100 pts
// LP + Triangulation
typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
typedef Delaunay::Finite_faces_iterator		Face_iterator;
typedef Delaunay::Finite_edges_iterator		Edge_iterator;
typedef Delaunay::Vertex_handle		Vertex_handle;
typedef Delaunay::Point		DPt;
struct Warehouse {
	Pt p;
	int s;
	int a;
	Warehouse(int x = 0, int y = 0, int s = -1, int ac = -1) :s(s), a(ac) {
		p = Pt(x, y);
	}
};
struct Stadium {
	Pt p;
	int d;
	int u;
	Stadium(int x = 0, int y = 0, int d = -1, int u = -1) :d(d), u(u) {
		p = Pt(x, y);
	}
};
struct Contour {
	Pt p;
	int r;
	Contour(int x = 0, int y = 0, int r = 0) : r(r) {
		p = Pt(x, y);
	}
};
void WorldCup() {
	int n, m, c; _i >> n >> m >> c;
	std::vector<Warehouse> whs(n);
	std::vector<Stadium> sts(m);
	std::vector<Contour> cts; // not initialized -- need to choose!

	std::vector<Pt> whst;
	for (int i = 0; i < n; i++) {
		int x, y, s, a; _i >> x >> y >> s >> a;
		whs[i] = Warehouse(x, y, s, a);
		whst.push_back(Pt(x, y));
	}
	for (int j = 0; j < m; j++) {
		int x, y, d, u; _i >> x >> y >> d >> u;
		sts[j] = Stadium(x, y, d, u);
		whst.push_back(Pt(x, y));
	}
	int r[200][20] = {}, t[200][20] = {};
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			_i >> r[i][j];
		}
	}

	Delaunay D;
	D.insert(whst.begin(), whst.end());

	for (int k = 0; k < c; k++) {
		lint x, y, rad;
		_i >> x >> y >> rad;
		Pt p(x, y);
		Vertex_handle vh = D.nearest_vertex(p);
		double d2 = CGAL::squared_distance(p, vh->point());
		if (d2 < rad*rad) {
			cts.push_back(Contour(x, y, rad));
		}
	}

	int uc = cts.size(); // used c
	for (int k = 0; k < uc; k++) {
		lint r2 = cts[k].r * cts[k].r;
		for (int i = 0; i < n; i++) {
			if (CGAL::squared_distance(whs[i].p, cts[k].p) < r2)
				for (int j = 0; j < m; j++)
					t[i][j] += (CGAL::squared_distance(sts[j].p, cts[k].p) > r2);
			else
				for (int j = 0; j < m; j++)
					t[i][j] += (CGAL::squared_distance(sts[j].p, cts[k].p) < r2);
		}
	}

	// form LP, n*m variables, n+m*2 constraints
	Program lp(CGAL::SMALLER, true, 0, false, 0);
	for (int i = 0; i < n; i++) {
		lp.set_b(i, whs[i].s);
		for (int j = 0; j < m; j++) {
			lp.set_a(i*m + j, i, 1);
		}
	}
	for (int j = 0; j < m; j++) {
		lp.set_b(n + j, -sts[j].d);
		lp.set_b(n + 2 * m + j, sts[j].d);
		lp.set_b(n + m + j, sts[j].u * 100);
		for (int i = 0; i < n; i++) {
			lp.set_a(i*m + j, n + j, -1);
			lp.set_a(i*m + j, n + 2 * m + j, 1);
			lp.set_a(i*m + j, n + m + j, whs[i].a);
		}
	}
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			int idx = i*m + j;
			lp.set_c(idx, -100 * r[i][j] + t[i][j]);
		}
	}

	Solution s = CGAL::solve_linear_program(lp, ET());

	if (s.is_optimal()) {
		ET result = s.objective_value().numerator() / (100 * s.objective_value().denominator());
		lint llr = floor_to_double(-result);
		_o << llr << _l;
	}
	else {
		_o << "RIOT!" << _l;
	}
	return;
}



// Week 10: Light the Stage
// Delaunay Triangulation + binary search
typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
typedef Delaunay::Finite_faces_iterator		Face_iterator;
typedef Delaunay::Finite_edges_iterator		Edge_iterator;
typedef Delaunay::Vertex_handle		Vertex_handle;
typedef Delaunay::Point		DPt;
struct Participant {
	Pt p;
	lint r;
	Participant(int x = 0, int y = 0, lint r = 0) :p(Pt(x, y)), r(r) {}
	Participant(Pt p, lint r = 0) :p(p), r(r) {}
};
void binarySearchLeftover(std::vector<Participant> &ps, std::vector<Pt> &lights, int h, std::vector<int> &leftover) {
	int m = ps.size(), n = lights.size();
	Delaunay D;
	D.clear();
	int start = 1, end = n - 1, mid = (start + end) / 2;
	std::vector<bool> aliveAfterMid(m, true);
	std::vector<int> tmpLeftOver;
	while (true) {
		if (end - start <= 1) break;
		D.clear();
		tmpLeftOver.clear();
		bool alive = false;
		D.insert(lights.begin(), lights.begin() + mid);
		for (int i = 0; i < m; i++) {
			Vertex_handle vh = D.nearest_vertex(ps[i].p);
			lint d2 = CGAL::squared_distance(vh->point(), ps[i].p);
			if (d2 >= (ps[i].r + h)*(ps[i].r + h)) {
				// existing one living participant: update the interval
				start = mid;
				mid = (start + end) / 2;
				alive = true;
				break;
			}
		}
		if (!alive) {
			end = mid - 1;
			mid = (start + end) / 2;
		}
	}
	_e << "mid: " << mid << _l;
	D.clear();
	D.insert(lights.begin(), lights.begin() + mid);

	if (mid < end) {
		std::vector<int> endleftover;
		D.clear();
		D.insert(lights.begin(), lights.begin() + end);
		for (int i = 0; i < m; i++) {
			Vertex_handle vh = D.nearest_vertex(ps[i].p);
			lint d2 = CGAL::squared_distance(vh->point(), ps[i].p);
			if (d2 >= (ps[i].r + h)*(ps[i].r + h)) {
				// existing one living participant: update the interval
				endleftover.push_back(i);
			}
		}
		if (!endleftover.empty()) {
			leftover.clear();
			leftover.insert(leftover.begin(), endleftover.begin(), endleftover.end());
		}
	}
	return;
}
void LightTheStage() {
	int m, n, h; _i >> m >> n;
	_e << m << " " << n << _l;
	std::vector<Participant> ps(m);
	for (int i = 0; i < m; i++) {
		int x, y, r;
		_i >> x >> y >> r;
		ps[i] = Participant(x, y, r);
	}
	_i >> h;
	std::vector<Pt> lights(n);
	for (int j = 0; j < n; j++) {
		int x, y; _i >> x >> y;
		lights[j] = Pt(x, y);
	}

	Delaunay D;
	D.insert(lights.begin(), lights.end());

	std::vector<int> leftover;
	for (int i = 0; i < m; i++) {
		Vertex_handle vh = D.nearest_vertex(ps[i].p);
		lint d2 = CGAL::squared_distance(vh->point(), ps[i].p);
		if (d2 >= (ps[i].r + h)*(ps[i].r + h)) {
			leftover.push_back(i);
		}
	}
	if (!leftover.empty()) {
		int l = leftover.size();
		for (int i = 0; i < l; i++) {
			_o << leftover[i] << " ";
		}
	}
	else {
		binarySearchLeftover(ps, lights, h, leftover);
		int l = leftover.size();
		for (int i = 0; i < l; i++) {
			_o << leftover[i] << " ";
		}
	}
	_o << _l;
	return;
}



// week 8: Bistro (nearest_vertex)
void Bistro(int n) {
	typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point		DPt;


	//int n, m; _i >> n;
	std::vector<Pt> existing(n);
	for (int i = 0; i < n; i++) {
		int x, y;
		_i >> x >> y;
		existing[i] = Pt(x, y);
	}
	int m; _i >> m;
	std::vector<Pt> possible(m);
	for (int j = 0; j < m; j++) {
		int x, y;
		_i >> x >> y;
		possible[j] = Pt(x, y);
	}

	Delaunay D;
	D.insert(existing.begin(), existing.end());

	for (int j = 0; j < m; j++) {
		Vertex_handle vh = D.nearest_vertex(possible[j]);
		lint d2 = CGAL::squared_distance(vh->point(), possible[j]);
		_o << d2 << _l;
	}

	return;
}



// Week 11: Strikes Back
// Delaunay triangulation for r
// LP for e
void StrikesBack() {
	typedef CGAL::Delaunay_triangulation_2<IK>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point		DPt;

	struct Asteroid {
		Pt pos;
		int d;
		Asteroid(Pt p = Pt(), int d = 0) : pos(p), d(d) {}
	};

	int a, s, b;
	_i >> a >> s >> b;
	int emax;
	_i >> emax;

	std::vector<Asteroid> asters(a);
	std::vector<Pt> shotpos(s); // model r and e outside.
	std::vector<Pt> bounties(b);

	for (int i = 0; i < a; i++) {
		int x, y, d;
		_i >> x >> y >> d;
		asters[i] = Asteroid(Pt(x, y), d);
	}
	for (int i = 0; i < s; i++) {
		int x, y;
		_i >> x >> y;
		shotpos[i] = Pt(x, y);
	}
	for (int i = 0; i < b; i++) {
		int x, y;
		_i >> x >> y;
		bounties[i] = DPt(x, y);
	}

	// triangulate bounties
	Delaunay D;
	D.insert(bounties.begin(), bounties.end());

	_e << "delaunay" << _l;

	std::vector<lint> shotradsq(s);
	if (b > 0) {
		for (int i = 0; i < s; i++) {
			DPt dpt(shotpos[i]);
			Vertex_handle vh = D.nearest_vertex(shotpos[i]);
			shotradsq[i] = CGAL::squared_distance(shotpos[i], vh->point());
			if (shotradsq[i] < 1) {
				shotradsq[i] = 1;
			}
		}
		_e << "shotradsq" << _l;
	}

	// set up LP to solve for min\Sum_i e_i
	Program lp(CGAL::LARGER, true, 0, true, emax); // Ax >= b

	for (int i = 0; i < a; i++) {
		lp.set_b(i, asters[i].d);
		for (int j = 0; j < s; j++) {
			lint sqdistij = CGAL::squared_distance(asters[i].pos, shotpos[j]);
			if (b == 0 || sqdistij <= shotradsq[j]) {
				// in shot range
				lp.set_a(j, i, ET(1) / sqdistij); // will it work?
			}
		}
	}
	for (int j = 0; j < s; j++) {
		lp.set_c(j, 1);
	}

	_e << "lpsetup" << _l;

	// solve the program, using ET as the exact type
	Solution solution = CGAL::solve_linear_program(lp, ET());
	assert(solution.solves_linear_program(lp));
	if (solution.is_infeasible()) {
		_o << "n" << _l;
		return;
	}
	else {
		ET eoptimal = solution.objective_value().numerator() / solution.objective_value().denominator();
		if (eoptimal <= emax) {
			_o << "y" << _l;
		}
		else {
			_o << "n" << _l;
		}
	}
	return;

}



// Week 12 PotW: Golden Eye / 100pts
// Euclidean (Kruskal) MST + Union Find for connectivity
// Cautions(I am not good today...):
// 1. check connectivity before adding any edges
// 2. it could be that the distance from queries to its nearest_vertex dominates the distance
// 3. beware of the order of setting a variable and using its value......
// 4. set everything to _lint_....
lint minLevelSet(Graph& G, std::vector<Edge>& mst, std::vector<int>& s, std::vector<int> &t, std::vector<lint> &maxd2, lint maxp) {
	int n = boost::num_vertices(G);
	int m = s.size();
	WeightMap wmap = boost::get(boost::edge_weight, G);

	UnionFind uf(n);
	lint start = 0;
	std::vector<bool> isconnected(m, false);
	bool allconn = true;
	for (int j = 0; j < m; j++) {
		start = std::max(start, maxd2[j]);
		isconnected[j] = uf.inSameSet(s[j], t[j]);
		if (!isconnected[j]) allconn = false;
	}
	if (allconn || start > maxp) {
		return start;
	}

	std::vector<Edge>::iterator eit = mst.begin();

	for (; eit != mst.end(); eit++) {
		if (wmap[*eit] > maxp) return -1;
		int u = boost::source(*eit, G);
		int v = boost::target(*eit, G);
		uf.unionSets(u, v);
		if (eit == mst.end() - 1 || wmap[*(eit + 1)] >= start) {
			bool allconnected = true;
			for (int j = 0; j < m; j++) {
				if (isconnected[j]) continue;
				if (uf.inSameSet(s[j], t[j]))
					isconnected[j] = true;
				if (!isconnected[j])
					allconnected = false; // isconnected[j] could have been altered!
			}
			if (allconnected)
				return std::max(start, (lint)wmap[*eit]);
		}
	}
	return -1; // never happen
}
void GoldenEye2() {
	typedef CGAL::Triangulation_vertex_base_with_info_2<ind_t, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point		DPt;

	lint n, m, p;
	_i >> n >> m >> p;
	std::vector< std::pair<DPt, int> > jams(n);
	std::vector<Pt> ss(m);
	std::vector<Pt> ts(m);

	Graph G(n); // undirected graph
	WeightMap weight = boost::get(boost::edge_weight, G);

	int x, y;
	for (int i = 0; i < n; i++) {
		_i >> x >> y;
		jams[i] = std::make_pair(DPt(x, y), i);
	}
	for (int j = 0; j < m; j++) {
		int x0, y0, x1, y1;
		_i >> x0 >> y0 >> x1 >> y1;
		ss[j] = Pt(x0, y0);
		ts[j] = Pt(x1, y1);
	}

	Delaunay D;
	D.insert(jams.begin(), jams.end());

	// Euclid MST
	for (Edge_iterator ei = D.finite_edges_begin(); ei != D.finite_edges_end(); ++ei) {
		Vertex_handle v1 = ei->first->vertex((ei->second + 1) % 3);
		Vertex_handle v2 = ei->first->vertex((ei->second + 2) % 3);
		int i1 = v1->info();
		int i2 = v2->info();
		lint dist = CGAL::squared_distance(v1->point(), v2->point());
		//_e << i1 << " " << i2 << ":" << dist << _l;
		bool success; Edge e;
		boost::tie(e, success) = boost::add_edge(i1, i2, G);
		if (success) weight[e] = dist;
	}

	std::vector<Edge> spanning_tree;
	boost::kruskal_minimum_spanning_tree(G, std::back_inserter(spanning_tree));

	std::vector<lint> ds(m), dt(m), maxpow(m);
	std::vector<Vertex_handle> vs(m), vt(m);
	std::vector<int> visited(m);
	std::vector<bool> pset(m, true);
	for (int j = 0; j < m; j++) {
		Pt s = ss[j], t = ts[j];
		vs[j] = D.nearest_vertex(s), vt[j] = D.nearest_vertex(t);
		ds[j] = CGAL::squared_distance(vs[j]->point(), s);
		dt[j] = CGAL::squared_distance(vt[j]->point(), t);
		maxpow[j] = 4 * std::max(ds[j], dt[j]);
		visited[j] = 0;
		if (maxpow[j] > p) pset[j] = false;
	}

	// check power level p
	Graph MSTP(n);
	std::vector<Edge>::iterator eit;
	lint maxwinmst = weight[spanning_tree[spanning_tree.size() - 1]]; // max weight in the MST
	for (eit = spanning_tree.begin(); eit != spanning_tree.end(); ++eit) {
		if (weight[*eit] > p) break;
		Vertex u = boost::source(*eit, G);
		Vertex v = boost::target(*eit, G);
		boost::add_edge(u, v, MSTP);
	}

	std::vector<int> components(n);
	boost::connected_components(MSTP, &components[0]);
	std::vector<int> p_s, p_t, all_s, all_t;
	std::vector<lint> p_maxd2, all_maxd2;
	for (int j = 0; j < m; j++) {
		if (!pset[j]) continue;
		int sidx = vs[j]->info(), tidx = vt[j]->info();
		if (components[sidx] != components[tidx]) {
			pset[j] = false;
		}
		if (pset[j]) {
			p_s.push_back(sidx);
			p_t.push_back(tidx);
			p_maxd2.push_back(maxpow[j]);
		}
	}
	for (int j = 0; j < m; j++) {
		all_s.push_back(vs[j]->info());
		all_t.push_back(vt[j]->info());
		all_maxd2.push_back(maxpow[j]);
	}

	lint b = minLevelSet(G, spanning_tree, p_s, p_t, p_maxd2, p);
	lint a = minLevelSet(G, spanning_tree, all_s, all_t, all_maxd2, maxwinmst);

	for (int j = 0; j < m; j++) {
		if (pset[j]) _o << "y";
		else _o << "n";
	}
	_o << _l;
	_o << a << _l;
	_o << b << _l;
}
// Week 12 PotW: Golden Eye / 75pts
// called uf.inSameSet() too many times
void GoldenEye() {

	typedef CGAL::Triangulation_vertex_base_with_info_2<ind_t, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point		DPt;

	lint n, m, p;
	_i >> n >> m >> p;
	std::vector< std::pair<DPt, int> > jams(n);
	std::vector<Pt> ss(m);
	std::vector<Pt> ts(m);

	Graph G(n);
	WeightMap weight = boost::get(boost::edge_weight, G);

	int x, y;
	for (int i = 0; i < n; i++) {
		_i >> x >> y;
		jams[i] = std::make_pair(DPt(x, y), i);
	}
	for (int j = 0; j < m; j++) {
		int x0, y0, x1, y1;
		_i >> x0 >> y0 >> x1 >> y1;
		ss[j] = Pt(x0, y0);
		ts[j] = Pt(x1, y1);
	}

	Delaunay D;
	D.insert(jams.begin(), jams.end());

	// Euclid MST
	for (Edge_iterator ei = D.finite_edges_begin(); ei != D.finite_edges_end(); ++ei) {
		Vertex_handle v1 = ei->first->vertex((ei->second + 1) % 3);
		Vertex_handle v2 = ei->first->vertex((ei->second + 2) % 3);
		int i1 = v1->info();
		int i2 = v2->info();
		double dist = CGAL::squared_distance(v1->point(), v2->point());
		//_e << i1 << " " << i2 << ":" << dist << _l;
		bool success; Edge e;
		boost::tie(e, success) = boost::add_edge(i1, i2, G);
		if (success) weight[e] = dist;
	}

	std::vector<Edge> spanning_tree;
	boost::kruskal_minimum_spanning_tree(G, std::back_inserter(spanning_tree));

	double a = 0, b = -1;
	std::vector<double> ds(m), dt(m), maxpow(m);
	std::vector<Vertex_handle> vs(m), vt(m);
	std::vector<int> visited(m);
	for (int j = 0; j < m; j++) {
		Pt s = ss[j], t = ts[j];
		vs[j] = D.nearest_vertex(s), vt[j] = D.nearest_vertex(t);
		ds[j] = CGAL::squared_distance(vs[j]->point(), s);
		dt[j] = CGAL::squared_distance(vt[j]->point(), t);
		maxpow[j] = 4 * std::max(ds[j], dt[j]);
		visited[j] = 0;
	}

	
	UnionFind uf(n);
	std::vector<Edge>::iterator ei;
	double w = 0, wlastchanged = 0;
	bool changed = false;
	for (int j = 0; j < m; j++) {
		if (uf.inSameSet(vs[j]->info(), vt[j]->info())) {
			// effectively vs[j]->info() == vt[j]->info()
			visited[j] = 1;
			changed = true;
		}
	}

	// Gradually add edges of the MST
	for (ei = spanning_tree.begin(); ei != spanning_tree.end(); ++ei) {
		Vertex v1 = boost::source(*ei, G), v2 = boost::target(*ei, G);
		uf.unionSets(v1, v2);
		w = weight[*ei];
		// if (w > p && b < 0) b = wlastchanged;
		changed = false;
		bool allvisited = true;
		for (int j = 0; j < m; j++) {
			if (!visited[j]) allvisited = false;
			if (!visited[j] && uf.inSameSet(vs[j]->info(), vt[j]->info())) {
				visited[j] = 1;
				changed = true;
				maxpow[j] = std::max(w, maxpow[j]);
			}
		}
		if (changed) wlastchanged = w;
		if (allvisited) break;
	}
	//if (w > p && b < 0) b = wlastchanged;
	if (b < 0) b = 0;

	for (int j = 0; j < m; j++) {
		a = std::max(a, maxpow[j]);
		//if (!visited[j]) _e << vs[j]->info() << "?" << vt[j]->info() << _l;
		//_e << maxpow[j] << " ";
		if (maxpow[j] > p) visited[j] = 2;
		else {
			if (b < maxpow[j]) b = maxpow[j];
		}
	}
	_e << _l;

	for (int j = 0; j < m; j++) {
		_o << (visited[j] == 1 ? "y" : "n");
	}
	_o << _l;
	_o << (lint)std::ceil(a) << _l;
	_o << (lint)std::ceil(b) << _l;
	return;

}



// typedef CGAL:Gmpz ET;
void Inball(int n, int d) {
	Program lp(CGAL::SMALLER, false, 0, false, 0);
	int c[10] = {};
	for (int i = 0; i < d; i++) c[i] = i;
	const int r = d;

	int a = 0, b = 0;
	for (int i = 0; i < n; i++) {
		double norm = 0;
		for (int j = 0; j < d; j++) {
			_i >> a;
			lp.set_a(c[j], i, a);
			norm += a*a;
		}
		lp.set_a(r, i, std::round(std::sqrt(norm)));
		_i >> b;
		lp.set_b(i, b);
	}
	lp.set_l(r, true, 0);
	lp.set_c(r, -1);

	// solve the program, using ET as the exact type
	Solution s = CGAL::solve_linear_program(lp, ET());
	assert(s.solves_linear_program(lp));

	if (s.is_optimal()) {
		CGAL::Quadratic_program_solution<ET>::Variable_value_iterator
			opt = s.variable_values_begin();
		CGAL::Quotient<ET> rad = *(opt + d);
		_o << (int)floor_to_double(rad) << _l;
	}
	else if (s.is_unbounded()) {
		_o << "inf" << _l;
	}
	else if (s.is_infeasible()) {
		_o << "none" << _l;
	}
	return;
}



void Lestrade() {

	typedef CGAL::Triangulation_vertex_base_with_info_2<ind_t, IK>	Vb;
	typedef CGAL::Triangulation_data_structure_2<Vb>	Tds;
	typedef CGAL::Delaunay_triangulation_2<IK, Tds>		Delaunay;
	typedef Delaunay::Finite_faces_iterator		Face_iterator;
	typedef Delaunay::Finite_edges_iterator		Edge_iterator;
	typedef Delaunay::Vertex_handle		Vertex_handle;
	typedef Delaunay::Point		DPt;

	struct Gangster {
		int u;
		int v;
		int w;
		int ag;
		Gangster(int uu = 0, int vv = 0, int ww = 0, int a = -1) : u(uu), v(vv), w(ww), ag(a) {}
	};

	int Z, U, V, W;
	int A, G;
	_i >> Z >> U >> V >> W >> A >> G;

	std::vector<std::pair<DPt, ind_t> > pts(G);
	std::vector<Gangster> gang(G);
	for (ind_t i = 0; i < G; i++) {
		int x, y, u, v, w;
		_i >> x >> y >> u >> v >> w;
		DPt pg(x, y);
		pts[i] = std::make_pair(pg, i);
		gang[i] = Gangster(u, v, w);
	}
	Delaunay T;
	T.insert(pts.begin(), pts.end());
	//_e << gang.size() << _l;

	std::vector<int> ha(A);
	std::vector<int> spect(A);
	for (ind_t i = 0; i < A; i++) {
		int x, y, h;
		_i >> x >> y >> h;
		ha[i] = h;
		DPt pa(x, y);
		Vertex_handle vh = T.nearest_vertex(pa);
		ind_t gind = vh->info();
		ind_t aind = gang[gind].ag;
		//_e << "gind" << gind << "; aind" << aind << _l;

		if (aind < 0 || (aind >= 0 && ha[aind] > h)) {
			// the gangster has not been inspected by others
			// or he has been inspected by another more expensive agent
			// --> I will do that instead!
			spect[i] = gind;
			gang[gind].ag = i;
			if (aind >= 0) {
				spect[aind] = -1;
			}
		}
		else {
			spect[i] = -1;
		}
	}
	//_e << ha.size() << _l;

	std::vector<int> hawo;
	std::vector<Gangster> gangspected;
	for (int i = 0; i < A; i++) {
		if (spect[i] >= 0) {
			hawo.push_back(ha[i]);
			gangspected.push_back(gang[spect[i]]);
		}
	}
	int nworking = hawo.size();

	/// set up the LP problem
	Program lp(CGAL::LARGER, true, 0, true, 24.f);
	for (ind_t j = 0; j < nworking; j++) {
		int z = hawo[j];
		Gangster gs = gangspected[j];
		//_e << z << " " << gs.u << " " << gs.v << " " << gs.w << _l;
		lp.set_c(j, -gs.u);
		lp.set_a(j, 0, -z);
		lp.set_a(j, 1, gs.v);
		lp.set_a(j, 2, gs.w);
	}
	lp.set_b(0, -Z);
	lp.set_b(1, V);
	lp.set_b(2, W);

	// solve the program, using ET as the exact type
	Solution s = CGAL::solve_linear_program(lp, ET());
	assert(s.solves_linear_program(lp));

	if (s.is_optimal()) {
		ET optim = s.objective_value().numerator() / s.objective_value().denominator();
		//_e << "optim:" << optim.to_double() << _l;
		if (optim > -U)
			_o << "H" << _l;
		else
			_o << "L" << _l;
	}
	else if (s.is_unbounded()) {
		_o << "L" << _l;
	}
	else if (s.is_infeasible()) {
		_o << "H" << _l;
	}
}