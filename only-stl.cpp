
#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include<iostream>
#include<iomanip>
#include<cstdio>
#include<vector>
#include<queue>
#include<set>
#include<deque>
#include<stack>
#include<map>
#include<unordered_map>
#include<algorithm>
#include<string>

using namespace std;
#define _o std::cout
#define _l std::endl
#define _i std::cin
#define _e std::cerr

typedef long long lint;

void AttackoftheClones2();

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
	int t;
	cin >> t;
	for (int i = 1; i <= t; i++) {
		AttackoftheClones2();
	}
}

void DefensiveLine();
void Punch();
void HighSchoolTeams();
void BonusLevel();
void CasinoRoyale();
void BeachBars();
void LightAtTheMuseum();
void Courbusier();
void Planks();
void DeckOfCards();
void NewTiles();


struct Jd {
	int a;
	int b;
	int l;
	bool cm;
	Jd(int a = 0, int b = 0, int l = 0) :a(a), b(b), l(l) { cm = (a > b); }
};
bool CompareJediByB(const Jd& j1, const Jd& j2) {
	if (j1.b != j2.b) return j1.b < j2.b;
	return j1.l < j2.l;
}
bool isJediOverlap(const Jd& j1, const Jd& j2) {
	if (j1.cm && j2.cm) return true;
	if (j1.cm && !j2.cm) return j1.a <= j2.b || j1.b >= j2.a;
	if (!j1.cm && j2.cm) return j1.a <= j2.b || j1.b >= j2.a;
	return j1.b >= j2.a && j1.a <= j2.b;
}
bool FullyCovered(const Jd& j1, const Jd& j2) {
	if (j1.cm && j2.cm) return j1.a >= j2.a && j1.b <= j2.b;
	if (j1.cm && !j2.cm) return false;
	if (!j1.cm && j2.cm) return j1.a >= j2.a || j1.b <= j2.b;
	if (!j1.cm && !j2.cm) return j1.a >= j2.a && j1.b <= j2.b;
}
void GetClearJedis(std::vector<Jd>& jedis) {
	int n = jedis.size();
	int ci = 0;
	std::vector<Jd> cljedis;
	cljedis.push_back(jedis[0]);
	for (int i = 1; i < n; i++) {
		if (FullyCovered(jedis[ci], jedis[i])) continue;
		cljedis.push_back(jedis[i]);
		ci = i;
	}
	jedis.clear();
	jedis.insert(jedis.begin(), cljedis.begin(), cljedis.end());
}
void AttackoftheClones2() {
	int n, m; _i >> n >> m;
	std::vector<Jd> jedis(n);
	for (int i = 0; i < n; i++) {
		int a, b;
		_i >> a >> b;
		int l = (a <= b) ? (b - a + 1) : (b - a + 1 + m);
		jedis[i] = Jd(a, b, l);
	}
	_e << "n=" << n << _l;
	std::sort(jedis.begin(), jedis.end(), CompareJediByB);
	GetClearJedis(jedis);
	n = jedis.size();
	_e << "new n=" << n << _l;

	//std::map<int, int> time_cover;
	std::vector<int> covers(n);
	int mincovidx = 0, mincov = m + 1;
	for (int i = 0; i < n; i++) {
		//int startb = jedis[i].b;
		int starta = jedis[i].a;
		auto jit = std::lower_bound(jedis.begin(), jedis.end(), Jd(starta, starta, 0), CompareJediByB);
		int endidx = (jit == jedis.end() ? 0 : (std::distance(jedis.begin(), jit)));
		//_e << "i=" << i << " a=" << starta << " endidx" << endidx << _l;
		covers[i] = i - endidx + 1;
		if (covers[i] <= 0) covers[i] += n;
		if (covers[i] < mincov) {
			mincov = covers[i];
			mincovidx = endidx;
		}
	}
	//mincovidx = (mincovidx + 1) % n;
	//_e << "idx" << mincovidx << " ncov" << mincov << _l;
	int maxJedis = 0;
	for (int ii = 0; ii < mincov; ii++) {
		// greedy
		int nJedis = 1, firstJediIdx = (mincovidx + ii) % n, lastJediIdx = firstJediIdx;
		for (int j = 1; j < n; j++) {
			int newIdx = (j + mincovidx + ii) % n;
			//_e << "last:" << jedis[lastJediIdx].a << "--" << jedis[lastJediIdx].b << "; cur:" << jedis[newIdx].a << "--" << jedis[newIdx].b << _l;
			if (isJediOverlap(jedis[lastJediIdx], jedis[newIdx])) continue;
			if (isJediOverlap(jedis[firstJediIdx], jedis[newIdx])) break;

			nJedis++;
			lastJediIdx = newIdx;
			//_e << "not overlap " << nJedis << _l;
		}
		maxJedis = std::max(maxJedis, nJedis);
	}
	_o << maxJedis << _l;
	return;
}


// Week 12: New Tiles / 100 points
// exponential DP...
bool checkIllegal0(int config, std::vector<int> &boardline) {
	int w = boardline.size();
	for (int i = 0; i < w; i++) {
		if (!((1 << i) & config) && boardline[i] == 0) {
			return true;
		}
	}
	return false;
}
int correctIllegal0(int config, std::vector<int> &boardline) {
	int w = boardline.size();
	int ret = config;
	for (int i = 0; i < w; i++) {
		if (!((1 << i) & config) && boardline[i] == 0) {
			ret ^= (1 << i);
		}
	}
	return ret;
}
int correctIllegal1(int config, std::vector<int> &boardline) {
	int w = boardline.size();
	int ret = config;
	for (int i = 0; i < w; i++) {
		if (((1 << i) & config) && boardline[i] == 0) {
			ret ^= (1 << i);
		}
	}
	return ret;
}
int maxAddTiles(int curr, int w) {
	int shifter = 3;
	int end = 1 << w;
	int maxadd = 0;
	while (shifter < end) {
		if ((shifter&curr) == shifter) {
			maxadd++;
			shifter <<= 2;
			continue;
		}
		shifter <<= 1;
	}
	return maxadd;
}
int addTiles(int prev, int curr, int w) {
	int shifter = 3;
	int end = 1 << w;
	int res = 0;
	while (shifter < end) {
		if ((!(shifter&prev)) && ((shifter&curr) == shifter)) {
			res++;
			shifter <<= 2;
			continue;
		}
		shifter <<= 1;
	}
	return res;
}
int nOnes2(int c, int w) {
	int s = 0;
	for (int i = 0; i < w; i++) {
		s += (((1 << i) & c) > 0);
	}
	return s;
}
string binaryString(int c, int w) {
	string str;
	for (int i = 0; i < w; i++)
		if ((1 << i)&c)
			str.push_back('1');
		else str.push_back('0');
		return str;
}
void NewTiles() {
	int h, w; _i >> h >> w;
	int boardarr[100][17] = {};
	for (int i = 0; i < h; i++) {
		for (int j = 0; j < w; j++) {
			_i >> boardarr[i][j];
		}
	}
	if (h <= 2 || w <= 2) {
		_o << 0 << _l;
		return;
	}

	std::vector< std::vector<int> > board(h - 2);
	for (int i = 0; i < h; i++) {
		if (i < h - 2) board[i] = std::vector<int>(w - 2);
		for (int j = 0; j < w; j++) {
			if (i > 0 && j > 0 && i < h - 1 && j < w - 1) {
				board[i - 1][j - 1] = boardarr[i][j];
			}
		}
	}
	h -= 2;
	w -= 2;
	int nconfig = 1 << w;
	int allone = nconfig - 1;
	// config: 100010110, 1=cannot be used by next row, 0=can be used by next row
	// search among configs in the prev row
	// f[i][config] = max_pconfig{f[i-1][pconfig] + #new tiles can be put in places where pconfig==0 and config==1}
	// f[i][config] = -1 --> config contains illegal 0 that cannot put tiles on
	std::vector< std::vector<int> > f(h);
	for (int i = 0; i < h; i++) {
		f[i] = std::vector<int>(nconfig);
	}
	std::vector<int> maxAdds(nconfig);
	for (int c = 0; c < nconfig; c++) {
		f[0][c] = 0;
		if (checkIllegal0(c, board[0])) f[0][c] = -1;
		maxAdds[c] = maxAddTiles(c, w);
	}
	for (int row = 1; row < h; row++) {
		for (int c = 0; c < nconfig; c++) {
			if (checkIllegal0(c, board[row])) {
				f[row][c] = -1;
				continue;
			}
			f[row][c] = 0;
			int correct = correctIllegal1(c, board[row]);
			// actually, no need to go through the previous row.
			// their information is contained in the configs in this row 
			// that has been computed before.
			// The idea of flipping only one '1'!!
			// that is harder to think of but ought to be thought of. 
			for (int bit = 0; bit < w; bit++) {
				if ((1 << bit) & c) {
					f[row][c] = std::max(f[row][c], f[row][c ^ (1 << bit)]);
				}
			}
			int maxadd = maxAddTiles(correct, w);
			do {
				int cprev = (~correct) & (allone);
				cprev = correctIllegal0(cprev, board[row - 1]);
				int added = addTiles(cprev, c, w);
				int withprev = f[row - 1][cprev] + added;
				f[row][c] = std::max(withprev, f[row][c]);
			} while (false);
			//for (int cprev = 0; cprev < nconfig; cprev++) {
			//	if (f[row - 1][cprev] == -1) continue;
			//	if ((((cprev^correct) & cprev) ^ correct) != allone) continue;
			//	//if (f[row - 1][cprev] + maxadd < f[row][c]) continue;
			//	//int added = addTiles(cprev, correct, w);
			//	cprev = correctIllegal0(cprev, board[row - 1]);
			//	int invcprev = (~cprev) & allone;
			//	int added = std::min(maxadd, maxAdds[invcprev]);
			//	//_e << binaryString(invcprev, w) << ": " << added << _l;
			//	int withprev = f[row - 1][cprev] + added;
			//	f[row][c] = std::max(f[row][c], withprev);
			//}
		}
		//_e << _l;
	}
	//_e << _l;

	//int ret = 0;
	//for (int c = 0; c < nconfig; c++) {
	//	ret = std::max(ret, f[h - 1][c]);
	//}
	_o << f[h - 1][nconfig - 1] << _l;
	return;
}


// Week 2 PotW: Deck of Cards / 100 points
// Sliding window
void DeckOfCards() {
	int n, k; _i >> n >> k;
	std::vector<int> v(n);
	for (int i = 0; i < n; i++) {
		_i >> v[i];
	}

	int bests = 0, beste = 0, cs = 0, ce = 1;
	int curval = 0, bestval = v[0];
	for (ce = 1; ce <= n; ce++) {
		curval += v[ce - 1];
		int cdist = std::abs(curval - k);
		int bdist = std::abs(bestval - k);
		if (cdist < bdist) {
			//_e << cs << "->" << ce - 1 << " " << curval << _l;
			bestval = curval;
			beste = ce;
			bests = cs;
		}
		if (curval > k) {
			cs++;
			for (; cs <= ce; ++cs) {
				curval -= v[cs - 1];
				cdist = std::abs(curval - k);
				bdist = std::abs(bestval - k);
				if (cdist < bdist) {
					//_e << cs << "->" << ce - 1 << " " << curval << _l;
					bestval = curval;
					beste = ce;
					bests = cs;
				}
				if (curval < k) break;
				if (curval == k) {
					_o << cs << " " << ce - 1 << _l;
					return;
				}
			}
		}
		else if (curval == k) {
			_o << cs << " " << ce - 1 << _l;
			return;
		}
		if (ce == n) {
			//_e << "bestval=" << bestval << _l << _l;
			_o << bests << " " << beste - 1 << _l;
			return;
		}
	}
	return;
}


// Week 13: Planks / 100 points
// Split and list, 4^n/4! options
// careful of the order!
struct OrderedPlanks {
	std::vector<int> a;
	OrderedPlanks(int m = 0) {
		a = std::vector<int>(4, m);
	}
	OrderedPlanks(int v1, int v2, int v3, int v4) {
		a = std::vector<int>({ v1, v2, v3, v4 });
		update();
	}
	OrderedPlanks(std::vector<int> v) {
		a.insert(a.begin(), v.begin(), v.end());
		update();
	}
	void update() {
		// order a
		std::sort(a.begin(), a.end());
	}
	int &operator[](int idx) {
		return a[idx];
	}
	int operator[](int idx) const {
		return a[idx];
	}
};
bool operator==(const OrderedPlanks &op1, const OrderedPlanks & op2) {
	for (int i = 0; i < 4; i++) {
		if (op1[i] > op2[i] || op1[i] < op2[i]) return false;
	}
	return true;
}
bool operator<(const OrderedPlanks &op1, const OrderedPlanks &op2) {
	// lexicographic ordering
	for (int i = 0; i < 4; i++) {
		if (op1[i] < op2[i]) return true;
		else if (op1[i] > op2[i]) return false;
	}
	return false;
}
OrderedPlanks operator+(OrderedPlanks &op1, OrderedPlanks &op2) {
	OrderedPlanks ret;
	for (int i = 0; i < 4; i++) {
		ret[i] = op1[i] + op2[i];
	}
	ret.update();
	return ret;
}
OrderedPlanks operator-(OrderedPlanks &op1, OrderedPlanks &op2) {
	OrderedPlanks ret;
	for (int i = 0; i < 4; i++) {
		ret[i] = op1[i] - op2[i];
	}
	ret.update();
	return ret;
}
typedef std::map<OrderedPlanks, int> PlankMap;
int maskSum(const std::vector<int> &l, int &mask) {
	int n = l.size();
	int ret = 0;
	for (int i = 0; i < n; i++)
		if (mask&(1 << i))
			ret += l[i];
	return ret;
}
void constructPlankMap(std::vector<int> &l, int &target, PlankMap &map) {
	int n = l.size();
	int maxnum = 1 << n;
	int mask = maxnum - 1;
	int total = maskSum(l, mask);
	int s1, s2, s3, s4; // s1 <= s2 <= s3 <= s4;
	for (s1 = 0; s1 < maxnum; s1++) {
		int v1 = maskSum(l, s1);
		if (v1 > target) continue;
		for (s2 = s1; s2 < maxnum; s2++) {
			if (s2&s1) continue;
			int v2 = maskSum(l, s2);
			if (v2 > target) continue;
			for (s3 = s2; s3 < maxnum; s3++) {
				if (s3&(s2 | s1)) continue;
				s4 = mask & ~(s1 | s2 | s3);
				if (s4 < s3) continue;
				int v3 = maskSum(l, s3);
				int v4 = total - v1 - v2 - v3;
				if (v3 > target || v4 > target) continue;
				// finally!
				OrderedPlanks op(v1, v2, v3, v4);
				map[op]++;
				//_e << "(" << v1 << "," << v2 << "," << v3 << "," << v4 << ")" << _l;
			}
		}
	}
}
int permNum(OrderedPlanks op, int target) {
	int perm = 1;
	for (int i = 0; i < 4; i++) {
		if (op[i] == target || op[i] == 0) op[i] = -(i + 1);
	}
	int v0 = op[0], v1 = op[1], v2 = op[2], v3 = op[3];
	if (v0 == v1 && v1 == v2 && v2 == v3) perm = 24;
	else if (v0 == v1 && v1 == v2) perm = 6;
	else if (v0 == v1 && v1 == v3) perm = 6;
	else if (v0 == v2 && v2 == v3) perm = 6;
	else if (v1 == v2 && v2 == v3) perm = 6;
	else if (v0 == v1) perm = (v2 == v3) ? 4 : 2;
	else if (v0 == v2) perm = (v1 == v3) ? 4 : 2;
	else if (v0 == v3) perm = (v1 == v2) ? 4 : 2;
	else if (v1 == v2) perm = (v0 == v3) ? 4 : 2;
	else if (v1 == v3) perm = (v0 == v2) ? 4 : 2;
	else if (v2 == v3) perm = (v0 == v1) ? 4 : 2;
	return perm;
}
void Planks() {
	int n; _i >> n;
	std::vector<int> l(n);
	int suml = 0, maxl = 0;
	for (int i = 0; i < n; i++) {
		_i >> l[i];
		suml += l[i];
		maxl = std::max(l[i], maxl);
	}
	if (suml % 4 || (n == 4 && suml != maxl * 4)) {
		_o << 0 << _l;
		return;
	}

	int target = suml / 4;
	std::vector<int> l1, l2;
	for (int i = 0; i < n; i++) {
		if (i < n / 2) l1.push_back(l[i]);
		else l2.push_back(l[i]);
	}
	int n1 = l1.size(), n2 = l2.size();

	PlankMap map1, map2;
	constructPlankMap(l1, target, map1);
	constructPlankMap(l2, target, map2);

	// merge maps for final result
	OrderedPlanks ptarget(target);
	long result = 0;
	PlankMap::iterator pit = map1.begin();
	for (; pit != map1.end(); pit++) {
		OrderedPlanks op = pit->first;
		OrderedPlanks need = ptarget - op;
		PlankMap::iterator pit2 = map2.find(need);
		if (pit2 != map2.end()) {
			//_e << "o(" << op[0] << "," << op[1] << "," << op[2] << "," << op[3] << "):\t" << pit->second << _l;
			//_e << "n(" << need[0] << "," << need[1] << "," << need[2] << "," << need[3] << "):\t" << pit2->second << _l;
			result += pit->second * pit2->second * permNum(need, target);
		}
	}
	_o << result << _l;
	return;
}


// Week 13: Corbusier / 100 points
// DP, f[j][t] = max #disks used to reach t%k using first j disks
void Courbusier() {
	int n, t, k; _i >> n >> t >> k;
	std::vector<int> h(n);
	for (int i = 0; i < n; i++) {
		_i >> h[i];
		h[i] %= k;
	}
	std::vector< std::vector<int> > f(n + 1);
	for (int i = 0; i <= n; i++) {
		f[i] = std::vector<int>(k, -1);
		f[i][0] = 0;
	}

	for (int i = 1; i <= n; i++) {
		int ch = h[i - 1];
		for (int r = 0; r < k; r++) {
			if (f[i - 1][r] >= 0) {
				f[i][r] = f[i - 1][r];
			}
		}
		for (int r = 0; r < k; r++) {
			int tgt = (ch + r) % k;
			if (f[i - 1][r] >= 0) {
				f[i][tgt] = std::max(f[i][tgt], f[i - 1][r] + 1);
			}
		}
	}

	_o << (f[n][t]>0 ? "yes" : "no") << _l;
	return;
}


// Week 5: Light at the Museum / 100 points
// Split and List
struct LightPattern {
	std::vector<int> b;
	LightPattern(std::vector<int> &b1 = std::vector<int>()) {
		b.insert(b.begin(), b1.begin(), b1.end());
	}
	LightPattern(int M) {
		b = std::vector<int>(M, 0);
	}
	int &operator[](int i) {
		return b[i];
	}
};
LightPattern operator-(const LightPattern & l1, const LightPattern & l2) {
	int n = l1.b.size();
	LightPattern ret(n);
	for (int i = 0; i < n; i++) {
		ret[i] = l1.b[i] - l2.b[i];
	}
	return ret;
}
LightPattern operator+(const LightPattern & l1, const LightPattern & l2) {
	int n = l1.b.size();
	LightPattern ret(n);
	for (int i = 0; i < n; i++) {
		ret[i] = l1.b[i] + l2.b[i];
	}
	return ret;
}
bool operator<(const LightPattern &l1, const LightPattern &l2) {
	int m = l1.b.size();
	for (int i = 0; i < m; i++) {
		if (l1.b[i] < l2.b[i]) return true;
		else if (l1.b[i] > l2.b[i]) return false;
	}
	return false;
}
bool operator==(const LightPattern &l1, const LightPattern &l2) {
	int m = l1.b.size();
	for (int i = 0; i < m; i++) {
		if (l1.b[i] < l2.b[i]) return false;
		else if (l1.b[i] > l2.b[i]) return false;
	}
	return true;
}
typedef std::map<LightPattern, int> LightMap;
// create a map: LightPattern -> int, indicating the minimum #switches required to achieve LightPattern
void findLightMap(const std::vector<LightPattern> & on, const std::vector<LightPattern> & off, LightMap &map, LightPattern & target) {
	int n = on.size();
	int m = on[0].b.size();
	for (int pat = 0; pat < (1 << n); pat++) {
		LightPattern lp(m);
		int sw = 0;
		for (int i = 0; i < n; i++) {
			if (pat & (1 << i)) // initial state
				lp = lp + on[i];
			else { // switched
				lp = lp + off[i];
				sw++;
			}
		}
		bool usable = true;
		for (int j = 0; j < m; j++) {
			if (lp[j] > target[j]) {
				// some room exceeds the target's requirement
				usable = false; break;
			}
		}
		if (usable) {
			LightMap::iterator it = map.find(lp);
			if (it != map.end()) {
				map[lp] = std::min(map[lp], sw);
			}
			else map.insert(std::make_pair(lp, sw));
		}
	}
}
void LightAtTheMuseum() {
	int N, M; _i >> N >> M;
	std::vector<int> B(M);
	for (int i = 0; i < M; i++) {
		_i >> B[i];
	}
	LightPattern target(B);
	std::vector<LightPattern> on(N), off(N);
	for (int j = 0; j < N; j++) {
		on[j] = LightPattern(M);
		off[j] = LightPattern(M);
		for (int i = 0; i < M; i++) {
			_i >> on[j][i] >> off[j][i];
		}
	}

	if (N == 1) {
		bool onpossible = true, offpossible = true;
		for (int i = 0; i < M; i++) {
			if (B[i] != on[0][i]) onpossible = false;
			if (B[i] != off[0][i]) offpossible = false;
		}
		if (onpossible || offpossible) {
			_o << 1 << _l;
		}
		else _o << "impossible" << _l;
		return;
	}

	int n1 = N / 2, n2 = N - n1;
	std::vector<LightPattern> on1, on2, off1, off2;
	on1.insert(on1.begin(), on.begin(), on.begin() + n1);
	on2.insert(on2.begin(), on.begin() + n1, on.end());
	off1.insert(off1.begin(), off.begin(), off.begin() + n1);
	off2.insert(off2.begin(), off.begin() + n1, off.end());
	LightMap map1, map2;

	findLightMap(on1, off1, map1, target);
	findLightMap(on2, off2, map2, target);

	// Merge light maps
	const int BIG = 1000000;
	int minsw = BIG;
	LightMap::iterator mit1;
	for (mit1 = map1.begin(); mit1 != map1.end(); mit1++) {
		LightPattern need = target - mit1->first;
		if (need == target) {
			if (mit1->second < minsw)
				minsw = mit1->second;
			continue;
		}
		LightMap::iterator mit2 = map2.find(need);
		if (mit2 != map2.end()) {
			int sw = mit1->second + mit2->second;
			if (sw < minsw) {
				minsw = sw;
			}
		}
	}
	if (minsw == BIG) {
		_o << "impossible" << _l;
	}
	else _o << minsw << _l;
	return;
}



// Week 12: Beach Bars / 100 points
// Sliding window along the axis, find the interval with most points
// O(range), range = [-1e6, 1e6]
struct Bar {
	int p; // position
	int minx; // minimum x within range
	int maxx; // maximum x within range
	int nx; // #x_i within range
	Bar(int p = 0, int mi = 100000000, int ma = -1, int n = 0) :p(p), minx(mi), maxx(ma), nx(n) {}
};
void BeachBars() {
	int n; _i >> n;
	std::vector<int> position(n);
	int maxpos = 0, minpos = 100000000;
	for (int i = 0; i < n; i++) {
		int p; _i >> p;
		maxpos = std::max(maxpos, p);
		minpos = std::min(minpos, p);
		position[i] = p;
	}
	int range = maxpos - minpos;
	std::vector<bool> istaken(range + 1);
	for (int i = 0; i < n; i++) {
		istaken[position[i] - minpos] = true; // no coincident positions
	}
	int l = 100; // [-100, 100]

	Bar prevbar, bestbar;
	// first bar
	prevbar.p = 0;
	for (int p = 0; p <= std::min(range, l); p++) {
		if (istaken[p]) {
			prevbar.nx++;
			prevbar.maxx = std::max(prevbar.maxx, p);
			prevbar.minx = std::min(prevbar.minx, p);
		}
	}

	std::vector<Bar> goodbars; // equally best bars
	goodbars.push_back(prevbar);
	bestbar = prevbar;
	for (int p = 1; p <= range; p++) {
		Bar curbar(prevbar);
		curbar.p = p;

		int start = p - l, end = p + l;
		if (start > 0) {
			if (istaken[start - 1]) {
				curbar.nx--;
				int x;
				for (x = start; x <= end && x <= range; x++) {
					if (istaken[x]) break;
				}
				if (x <= end) {
					// #x=0
					curbar.minx = x;
				}
			}
		}
		if (end <= range) {
			if (istaken[end]) {
				curbar.nx++;
				curbar.maxx = end;
			}
		}

		// need to take care of states involving bar.nx==0
		if (prevbar.nx == 0 && curbar.nx > 0) {
			// curbar.nx == 1
			curbar.minx = curbar.maxx;
		}
		else if (prevbar.nx > 0 && curbar.nx == 0) {
			// prevbar.nx == 1
			curbar.minx = 100000000;
			curbar.maxx = -1;
		}

		int curmaxd = std::max(std::abs(curbar.maxx - curbar.p), std::abs(curbar.minx - curbar.p));
		int bestmaxd = std::max(std::abs(bestbar.maxx - bestbar.p), std::abs(bestbar.minx - bestbar.p));
		if (curbar.nx > bestbar.nx || (curbar.nx == bestbar.nx && curmaxd < bestmaxd)) {
			goodbars.clear();
			goodbars.push_back(curbar);
			bestbar = curbar;
		}
		else if (curbar.nx == bestbar.nx && curmaxd == bestmaxd) {
			goodbars.push_back(curbar);
		}
		prevbar = curbar;
	}

	int ngoodbars = goodbars.size();
	int maxd = std::max(std::abs(bestbar.p - bestbar.maxx), std::abs(bestbar.p - bestbar.minx));
	_o << bestbar.nx << " " << maxd << _l;
	for (int i = 0; i < ngoodbars; i++) {
		_o << goodbars[i].p + minpos << " ";
	}
	_o << _l;
	return;
}


// Week 12: Casino Royale / 0 points....
// Dynamic programming for multi-task scheduling with multiple machines
// O(m*l)
struct Mission {
	int s; // start
	int t; // terminate
	int l; // length = t - s
	int q; // value
	Mission(int s = 0, int t = 0, int q = -1) : s(s), t(t), q(q) { l = t - s; }
};
bool compareMissionByT(const Mission & m1, const Mission & m2) {
	if (m1.t == m2.t) return m1.s < m2.s;
	return m1.t < m2.t;
}
bool compareMissionByS(const Mission & m1, const Mission & m2) {
	if (m1.s == m2.s) return m1.t < m2.t;
	return m1.s < m2.s;
}
void CasinoRoyale() {
	int n, m, l; _i >> n >> m >> l;
	_e << "testcase: " << n << " " << m << " " << l << _l;
	std::vector<Mission> mis(m);
	int mins = 1111111;
	for (int i = 0; i < m; i++) {
		int s, t, q; _i >> s >> t >> q;
		mis[i] = Mission(s, t, q);
		mins = std::min(mins, s);
	}
	for (int i = 0; i < m; i++) {
		mis[i].s -= mins;
		mis[i].t -= mins;
	}
	_e << "mins=" << mins << _l;
	n -= mins;

	std::sort(mis.begin(), mis.end(), compareMissionByT);

	std::vector<bool> used(m, false);
	std::vector<int> f(n, 0); // maximum value sum achievable until t
	std::vector<int> lastidx(n, 0); // index of the last task used by f(t)
	std::vector<int> prev(n, 0), next(n, n - 1);

	int total = 0;
	for (int r = 0; r < l; r++) {
		std::fill(f.begin(), f.end(), 0);
		std::fill(lastidx.begin(), lastidx.end(), -1);
		int largestT = 0; // the largest t used in this round
						  // fill _f_ by going through _mis_
		for (int i = 0; i < m; i++) {
			if (used[i]) continue;
			//_e << i << " ";
			int s = mis[i].s, t = mis[i].t;
			if (n == 50 && m == 250 && l == 100) _e << s << "->" << t << " q=" << mis[i].q << " fs=" << f[s] << " ft=" << f[t] << _l;
			if (f[s] + mis[i].q > f[t] || (f[s] + mis[i].q == f[t] && (mis[lastidx[t]].l < mis[i].l))) {
				f[t] = f[s] + mis[i].q;
				lastidx[t] = i;
				largestT = std::max(largestT, t);
				// update prev[t, next[t]] and next[prev[t], t]
				//int pr = prev[t], ne = next[t];
				//std::fill(next.begin() + pr, next.begin() + t+1, t);
				//std::fill(prev.begin() + t, prev.begin() + ne+1, t);
				for (int t1 = t + 1; t1 < n; t1++) {
					if (f[t1] < f[t]) {
						f[t1] = f[t];
						lastidx[t1] = lastidx[t];
					}
					else break;
				}
			}
		}
		//for (int tt = 0; tt < n; tt++) {
		//	_e << tt << "::" << f[tt] << "," << lastidx[tt] << ":" << mis[lastidx[tt]].s << "->" << mis[lastidx[tt]].t << _l;
		//}
		_e << _l;
		if (largestT == 0) {
			// every mission is used
			break;
		}
		int machinemax = f[n - 1];
		_e << "max=" << machinemax << ",lt=" << largestT << _l;
		total += machinemax;
		int curT = n - 1;
		while (true) {
			if (curT == 0) break;
			int ind = lastidx[curT];
			if (ind < 0) break;
			_e << "t=" << curT << ": " << mis[ind].s << "->" << mis[ind].t << ", q=\t" << mis[ind].q << " at ind" << ind << _l;
			used[ind] = true;
			curT = mis[ind].s;
		}
		//_e << _l;
	}
	_e << "testcase: " << n << " " << m << " " << l << _l;
	_e << "result:" << total << _l << _l;
	for (int i = 0; i < m; i++) {
		if (!used[i]) {
			int s = mis[i].s, t = mis[i].t;
			_e << s << "->" << t << " q=" << mis[i].q << _l;
		}
	}

	_o << total << _l;
	return;
}


// Week 10: Bonus Level / 100 points
// Dynamic programming, counting the directions to obtain disjoint paths
int maxFour(int x, int y, int z, int w) {
	return std::max(std::max(x, y), std::max(z, w));
}
void BonusLevel() {
	const int N = 150; // you said it was 100!
					   // so: always use std::vector... don't use arrays?
	int n; _i >> n;
	//int f[N*2][N][N] = {};
	vector< vector< vector<int> > > f(n * 2);
	for (int i = 0; i < n * 2; i++) {
		f[i] = vector< vector<int> >(n);
		for (int j = 0; j < n; j++) {
			f[i][j] = vector<int>(n);
		}
	}
	int a[N][N] = {};
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < n; j++) {
			_i >> a[i][j];
		}
	}
	int total = a[0][0] + a[n - 1][n - 1];
	a[0][0] = a[n - 1][n - 1] = 0;

	f[1][1][0] = a[1][0] + a[0][1];
	/*
	f[k][v1][v2] = max{ f[k-1][v1][v2], f[k-1][v1][v2-1], f[k-1][v1-1][v2], f[k-1][v1-1][v2-1] } + a1 + a2;
	*/
	for (int k = 2; k < 2 * n - 2; k++) {
		for (int v1 = std::max(1, k - n + 2); v1 <= std::min(k, n - 1); v1++) {
			int a1 = a[k - v1][v1];
			for (int v2 = std::max(0, k - n + 1); v2 < v1; v2++) { // v2 < v1!
				int a2 = a[k - v2][v2];
				int i2 = k - v2, j2 = v2;
				int dd = 0, dr = 0, rd = 0, rr = 0; // d -- v->v; r-- v->v+1;
				if (v1 - 1 > v2) {
					rd = f[k - 1][v1 - 1][v2] + a1 + a2;
				}
				if (v2 > 0) {
					rr = f[k - 1][v1 - 1][v2 - 1] + a1 + a2;
				}
				if (v1 < k) {
					dd = f[k - 1][v1][v2] + a1 + a2;
				}
				if (v1 < k && v2 > 0) {
					dr = f[k - 1][v1][v2 - 1] + a1 + a2;
				}
				f[k][v1][v2] = maxFour(dd, dr, rd, rr);
			}
		}
	}

	_o << f[2 * n - 3][n - 1][n - 2] + total << _l;
	return;
}


// Week 12: High School Teams / 100 points
// Divide and list -- not easy ehhh..
inline int nOnes(int k, int n = 32) {
	int nones = 0;
	for (int i = 0; i<n; i++)
		if (k&(1 << i)) nones++;
	return nones;
}
inline long long choose(int n, int k) {
	long long ret = 1;
	long long kfact = 1;
	for (int i = 0; i<k; i++) {
		ret *= n - i;
		kfact *= i + 1;
	}
	return ret / kfact;
}
void chooseK(int n, int k, vector<int>& ck) {
	int ct = 0;
	for (int i = 0; i<(1 << n); i++) {
		if (nOnes(i, n) <= k) {
			ck.push_back(i);
			//ct++;
		}
	}
}
int findTeams(const vector<int>& s, int cset, int n, map<int, int> & m) {

	int cn = nOnes(cset, n);
	int cs[50] = {};
	int csum = 0;
	int ct = 0;
	for (int i = 0; i<n; i++) {
		// cerr<<(bool)(cset&(1<<i)) << ":" <<endl;
		if (cset&(1 << i)) {
			cs[ct] = s[i];
			ct++;
			// cerr<<i<<","<<s[i];
			csum += s[i];
		}
		// cerr<<"h\n";
	}
	//cerr << endl;
	//if (csum % 2 == 1) return 0;

	int nteams = 0;
	//int cn = cs.size();
	int teamsum = 0;
	for (int t1 = 0; t1<(1 << cn); t1++) {
		teamsum = 0;
		for (int j = 0; j<cn; j++) {
			if (t1&(1 << j))
				teamsum += cs[j];
		}
		int diff = (csum - teamsum * 2);
		m[diff]++;
		if (teamsum == csum - teamsum) //legacy
			nteams++;
	}
	cerr << "nt" << nteams << endl;
	return nteams; //legacy
}
// vm[i][val] = number of cases of strength difference _val_, with _i_ non-players 
void findTeamMap(int n, int k, vector< map<int, int> > & vm) {
	if (k > n) k = n;

	vector<int> s(n);
	for (int i = 0; i<n; i++) {
		cin >> s[i];
	}

	vector<int> ck;
	chooseK(n, k, ck);

	int nck = ck.size();
	cerr << "nck" << nck << endl;

	for (int i = 0; i<nck; i++) {
		int cset = ((1 << n) - 1)&(~ck[i]); // c_i = 1 --> not use i
		int nones = nOnes(ck[i], n);
		//cerr << ck[i] << "non" << nones << endl;
		findTeams(s, cset, n, vm[nones]);
	}

}
// m[val] = sum_i(vm[i][val])
void mergeMap(vector< map<int, int> > & vm, vector< map<int, int> > & vm_merged) {
	int l = vm.size(); // k+1

	for (int i = 0; i < l; i++) {
		map<int, int>::iterator mit = vm[i].begin();
		for (; mit != vm[i].end(); mit++) {
			int val = mit->first;
			for (int j = i; j < l; j++) {
				vm_merged[j][val] += mit->second;
			}
		}
	}
}
long long countTotalTeams_u(vector< map<int, int> > & vm1, vector< map<int, int> > & vm2, int k) {
	long long total = 0;
	int l = std::min(k + 1, (int)vm1.size());
	for (int i = 0; i < l; i++) {
		int res = std::min(k - i, l - 1);
		map<int, int> ::iterator mit = vm1[i].begin();
		for (; mit != vm1[i].end(); mit++) {
			int val = mit->first, cnt1 = mit->second;
			for (int j = 0; j <= res; j++) {
				map<int, int>::iterator mit2 = vm2[j].find(-val);
				if (mit2 != vm2[j].end()) {
					//int added = cnt1*mit2->second / (val == 0 ? 1 : 4);
					int added = cnt1*mit2->second;
					total += added;
				}
			}
		}
	}
	//total /= 4;
	return total;
}
long long countTotalTeams(vector< map<int, int> > & vm1, vector< map<int, int> > & vm2_merged, int k) {
	long long total = 0;
	int l = std::min(k + 1, (int)vm1.size());
	for (int i = 0; i < l; i++) {
		int res = std::min(k - i, (int)vm2_merged.size() - 1);
		cerr << res << " ";
		map<int, int>::iterator mit = vm1[i].begin();
		for (; mit != vm1[i].end(); mit++) {
			int val = mit->first, cnt1 = mit->second;
			map<int, int>::iterator mit2 = vm2_merged[res].find(val);
			if (mit2 != vm2_merged[res].end()) {
				int cnt2 = mit2->second;
				total += (long long)cnt1 * cnt2;
			}
		}
	}
	//total /= 4;
	cerr << endl;
	return total;
}
void HighSchoolTeams() {
	int n, k;
	cin >> n >> k;

	long long result = 0;
	cerr << "testcase" << n << " " << k << endl;
	int n1 = n / 2, n2 = n - n1;

	vector< map<int, int> > vm1(std::min(k, n1) + 1), vm2(std::min(k, n2) + 1);

	findTeamMap(n1, k, vm1);
	findTeamMap(n2, k, vm2);
	cerr << "ftm" << endl;
	vector< map<int, int> > vm2_merged(std::min(k, n2) + 1);
	mergeMap(vm2, vm2_merged);
	cerr << "mm" << endl;
	result = countTotalTeams(vm1, vm2_merged, k);
	//result = countTotalTeams_u(vm1, vm2, k);
	cout << result << endl;
	return;
}


// week 11: Punch
struct Beverage {
	int c;
	int v;
	Beverage(int c=0, int v=0): c(c), v(v){}
};
void Punch() {
	int n, k;
	cin >> n >> k;
	vector<Beverage> bevs(n);
	for (int i = 0; i < n; i++) {
		int c, v;
		cin >> c >> v;
		bevs[i] = Beverage(c, v);
	}

	int f[2][10001] = {};
	int nbevs[2][10001] = {};
	for (int j = 0; j <= k; j++) {
		f[0][j] = bevs[0].c * (j / bevs[0].v + (j%bevs[0].v > 0)); // ceil(j/v_i)
		if (j > 0)
			nbevs[0][j] = 1;
	}

	for (int i = 1; i < n; i++) {
		int cv = bevs[i].v;
		int cc = bevs[i].c;
		for (int offset = 0; offset < cv; offset++) {
			// fill a list 
			bool prevusei = false; // whether beverage i is used in f[i][j-cv]
			for (int j = offset; j <= k; j += cv) {
				if (j < cv) {
					if (j == 0) {
						f[1][j] = 0; continue;
					}
					// compare f[i-1][j] with cc*1
					int comp1 = f[0][j], comp2 = cc;
					if (comp1 > comp2) {
						f[1][j] = comp2; nbevs[1][j] = 1;
						prevusei = true;
					}
					else {
						f[1][j] = comp1; nbevs[1][j] = nbevs[0][j];
						prevusei = false;
					}
				}
				else {
					// min{f[i-1][j], f[i][j-cv]}
					int comp1 = f[0][j], comp2 = f[1][j - cv] + cc;
					if (comp1 > comp2) {
						f[1][j] = comp2;
						if (prevusei) 
							nbevs[1][j] = nbevs[1][j - cv];
						else nbevs[1][j] = nbevs[1][j - cv] + 1;
						prevusei = true;
					}
					else if (comp1 < comp2) {
						f[1][j] = comp1;
						nbevs[1][j] = nbevs[0][j];
						prevusei = false;
					}
					else {
						f[1][j] = comp1; // =comp2
						// comp1 == comp2
						int nbev1 = nbevs[0][j], nbev2 = nbevs[1][j - cv] + (1-prevusei);
						if (nbev1 < nbev2) {
							nbevs[1][j] = nbev2; prevusei = true;
						}
						else {
							nbevs[1][j] = nbev1; prevusei = false;
						}
					}
				}
			}
		}

		for (int j = 0; j <= k; j++) {
			f[0][j] = f[1][j];
			f[1][j] = 0;
			nbevs[0][j] = nbevs[1][j];
			nbevs[1][j] = 0;
		}
	}

	//for (int i = 0; i < n; i++) {
	//	cerr << bevs[i].c << "," << bevs[i].v << ":" << endl;
	//	for (int j = 0; j <= k; j++) {
	//		cerr << j<<":"<< f[1][j] << "," << nbevs[1][j] << " ";
	//	}
	//	cerr << endl;
	//}

	cout << f[0][k] << " " << nbevs[0][k] << endl;
	return;
}

// week 11 : Defensive Line
struct Segment {
	int a;
	int b;
	int l; // l=b-a+1
	Segment(int a=-1, int b=-1, int l=-1): a(a), b(b), l(l){}
};
bool CompareSegmentbyB(const Segment s1, const Segment s2) {
	return s1.b < s2.b;
}
void DefensiveLine() {
	// input
	int n, m, k;
	cin >> n >> m >> k;
	vector<int> v(n), accum(n);
	for (int i = 0; i < n; i++) {
		cin >> v[i];
		if (i == 0) accum[0] = v[0];
		else accum[i] = accum[i - 1] + v[i];
	}

	// find segments that sum to k.
	vector<Segment> segs;
	for (int i = 0; i < n; i++) {
		int accumVal = i>0?accum[i-1]:0;
		int remain = k + accumVal;
		vector<int>::iterator vit = lower_bound(accum.begin(), accum.end(), remain);
		if (vit != accum.end() && *vit == remain) { // found
			int ca = i, cb = vit - accum.begin(), cl = cb-ca+1;
			Segment seg(ca, cb, cl);
			segs.push_back(seg);
		}
	}
	if (segs.empty() || segs.size() < m) {
		// no good segments
		cout << "fail" << endl;
		return;
	}

	std::sort(segs.begin(), segs.end(), CompareSegmentbyB); // for fast maximum finding
	int L = segs.size();
	vector<int> dp(L), prevdp(L);
	vector<int> maxs(L); // max dp[0:i]
	vector<int> maxbposs(L);
	for (int i = 0; i < L; i++) {
		//cerr << "a" << segs[i].a << "b" << segs[i].b << " ";
		dp[i] = segs[i].l;
		prevdp[i] = segs[i].l;
		if (i == 0) maxs[0] = dp[0];
		else {
			maxs[i] = std::max(dp[i], maxs[i - 1]);
			//cerr << maxs[i] << " ";
		}
	}

	for (int j = 0; j < L; j++) {
		Segment seg = segs[j];
		vector<Segment>::iterator maxbpos = lower_bound(segs.begin(), segs.end(), Segment(seg.a, seg.a, seg.a), CompareSegmentbyB);
		if (maxbpos == segs.begin()) {
			maxbposs[j] = -1;
		}
		else {
			maxbposs[j] = maxbpos - segs.begin() - 1;
		}
	}

	// O(m*L*logL) for 100 pts
	for (int i = 1; i < m; i++) {
		cerr << "i:" << i << endl;
		bool changed = false;
		for (int j = 0; j < L; j++) {
			Segment seg = segs[j];
			//cerr << std::distance(segs.begin(), maxbpos) << "|";
			if (maxbposs[j] == -1) {
				// no valid b
				continue;
			}
			else {
				int maxbind = maxbposs[j];
				int maxv = maxs[maxbind];
				dp[j] = maxv + seg.l;
				if (dp[j] > prevdp[j]) changed = true;
			}
		}

		if (!changed) {
			cout << "fail" << endl;
			return;
		}
		maxs[0] = dp[0];
		for (int j = 0; j < L; j++) {
			prevdp[j] = dp[j];
			if (j > 0) {
				maxs[j] = std::max(dp[j], maxs[j - 1]);
				//cerr << maxs[j] << " ";
			}
		}
	}

	/* O(m*L*L) for 50 pts
	for (int i = 1; i < m; i++) {
		bool changed = false;
		for (int j = 0; j < L; j++) {
			Segment seg = segs[j];
			int maxv = 0;
			for (int j1 = 0; j1 < L; j1++) {
				if (segs[j1].a >= seg.a) break; // ordered by a

				if (segs[j1].b < seg.a && prevdp[j1] > maxv) {
					maxv = prevdp[j1];
				}
			}
			dp[j] = maxv + seg.l;
			if (dp[j] > prevdp[j]) {
				changed = true;
			}
		}
		if (!changed) {
			cout << "fail" << endl;
			return;
		}
		for (int j = 0; j < L; j++) {
			prevdp[j] = dp[j];
		}
	}
	*/

	int overallMax = 0;
	for (int j = 0; j < L; j++) {
		if (overallMax < dp[j]) {
			overallMax = dp[j];
		}
	}

	cout << overallMax << endl;
	return;

}


/*
From this exercise:
Never attempt to 'simplify' logical comparisons with complicated arithmetics
when it can be solved with a simple lookup!!!!
Just write a function and list the return values...
It really can ruin an exam.
09.10.17
It is wrong... Only got 80/100.
*/
struct Jedi {
	int a;
	int b;
	int l;
	bool crossm;
	Jedi(int aa = -1, int bb = -1, int ll = -1, bool cm = false) :a(aa), b(bb), l(ll), crossm(cm) {}
};
/*
This function saved my day!
Not until when I wrote this function did I realize that the logical
relationship is actually THIS SIMPLE.
*/
bool isJediNotOverlapping(const Jedi& j1, const Jedi& j2) {
	if (j1.crossm && j2.crossm)
		return false;
	else if ((j1.crossm && !j2.crossm) || !j1.crossm && j2.crossm) {
		return j1.b<j2.a && j1.a>j2.b;
	}
	else {
		return j1.a>j2.b || j1.b<j2.a;
	}
}
bool compareJediWithb(const Jedi& ja, const Jedi& jb) {
	if (ja.b == jb.b) return ja.l < jb.l;
	return ja.b<jb.b;
}
void AttackoftheClones() {
	int n, m;
	_i >> n >> m;
	vector<Jedi> vjd, vjcompact;
	int ta, tb, tl;
	bool tcm;
	for (int i = 0; i<n; i++) {
		cin >> ta >> tb;
		tcm = (ta>tb);
		tl = (tb + (tcm ? m : 0)) - ta + 1;
		vjd.push_back(Jedi(ta, tb, tl, tcm));
	}
	sort(vjd.begin(), vjd.end(), compareJediWithb);

	// make compact
	Jedi tjd;
	int ta1, ta2, i, j, ii, jj;
	for (i = 0; i<n;) {
		tjd = vjd[i];
		vjcompact.push_back(tjd);
		ta1 = tjd.a - m*tjd.crossm;
		j = i + 1;
		while (j<n) {
			//jj = (j+i)%n;
			ta2 = vjd[j].a - m*vjd[j].crossm;
			if (ta2 <= ta1) {
				j++;
			}
			else {
				i = j;
				break;
			}
		}
		if (j == n) break;
	}
	int ncompact = vjcompact.size();
	while (ncompact>1 && vjcompact[0].l - (vjcompact[0].b + m - vjcompact[ncompact - 1].b) >= vjcompact[ncompact - 1].l) {
		vjcompact.erase(vjcompact.begin());
		ncompact--;
	}
	_e << "n=" << n << ", ncompact=" << ncompact << _l;

	int maxjd = 0, indi, indj;
	std::vector<int> first(ncompact, -1), last(ncompact, -1), prev(ncompact, -1), njds(ncompact, -1);
	// search for the first one, i=0
	int curjd = 1;
	i = 0;
	indi = i;
	last[i] = (ncompact + i - 1) % ncompact;
	bool outofZone = false;
	for (int j = 1; j < ncompact; j++) {
		// indj is the current candidate
		// indi is the last chosen
		indj = (j + i) % ncompact;
		if (outofZone && !isJediNotOverlapping(vjcompact[indj], vjcompact[i])) {
			last[i] = indi;
			break;
		}
		if (isJediNotOverlapping(vjcompact[indj], vjcompact[indi])) {
			if (!outofZone) {
				outofZone = true;
			}
			first[indi] = indj;
			prev[indj] = indi;
			curjd++;
			indi = indj;
		}
	}
	njds[0] = curjd;
	maxjd = curjd;
	// search for others
	for (i = 1; i < ncompact; i++) {
		int curjd;
		_e << "i=" << i << ", " << vjcompact[i].a << "-->" << vjcompact[i].b;
		if (prev[i] != -1) {
			int searchstart = (last[prev[i]] + 1) % ncompact;
			last[i] = (ncompact + i - 1) % ncompact;
			_e << "prev_i=" << prev[i] << " " << njds[prev[i]] << _l;
			_e << "ss=" << searchstart << _l;
			indi = searchstart;
			curjd = njds[prev[i]] - 1;
			for (int j = searchstart; j != i; j++) {
				if (j >= ncompact) j %= ncompact;
				if (!isJediNotOverlapping(vjcompact[j], vjcompact[i])) {
					_e << "break at:" << j << _l;
					last[i] = indi;
					break;
				}
				if (isJediNotOverlapping(vjcompact[j], vjcompact[indi])) {
					first[indi] = j;
					prev[j] = indi;
					curjd++;
					indi = indj;
				}
			}
		}
		else {
			// ordinary search
			curjd = 1;
			indi = i;
			last[i] = (ncompact + i - 1) % ncompact;
			bool outofZone = false;
			for (int j = 1; j < ncompact; j++) {
				// indj is the current candidate
				// indi is the last chosen
				indj = (j + i) % ncompact;
				if (outofZone && !isJediNotOverlapping(vjcompact[indj], vjcompact[i])) {
					last[i] = indi;
					break;
				}
				if (isJediNotOverlapping(vjcompact[indj], vjcompact[indi])) {
					if (!outofZone) {
						outofZone = true;
					}
					first[indi] = indj;
					prev[indj] = indi;
					curjd++;
					indi = indj;
				}
			}
		}
		_e << " curjd=" << curjd << _l;
		njds[i] = curjd;
		maxjd = std::max(curjd, maxjd);
	}

	//int maxjd = 0, indi, indj;
	//for (i = 0; i<ncompact; i++) {
	//	int curjd = 1;
	//	indi = i;
	//	_e << "i=" << i << ", " << vjcompact[i].a << "-->" << vjcompact[i].b;
	//	bool outofZone = false;
	//	for (j = 1; j<ncompact; j++) {
	//		indj = (j + i) % ncompact;
	//		if (outofZone && !isJediNotOverlapping(vjcompact[indj], vjcompact[i]))
	//		{
	//			//_e << ", break at j=" << indj << _l;
	//			break;
	//		}
	//		if (isJediNotOverlapping(vjcompact[indj], vjcompact[indi]))
	//		{
	//			outofZone = true;
	//			curjd++;
	//			indi = indj;
	//		}
	//	}
	//	_e << " curjd=" << curjd << _l;
	//	if (curjd>maxjd) {
	//		maxjd = curjd;
	//	}
	//}
	_o << maxjd << endl;
	return;
}
