#pragma once

#include<iostream>
#include<vector>
#include<map>

class UnionFind {
public:
	UnionFind(const int n=0) {
		m_par.clear();
		m_par.reserve(n);
		m_rank.clear();
		m_rank.reserve(n);
		for (int i = 0; i < n; i++) {
			m_par.push_back(i);
			m_rank.push_back(0);
			m_setsize.insert(std::make_pair(i, 1));
		}
		m_maxsize = m_setsize.empty() ? 0 : 1;
	}

	UnionFind(const std::vector<int> & par) {
		int n = par.size();
		m_par.clear();
		m_par = std::vector<int>(n);
		m_rank.clear();
		m_rank = std::vector<int>(n);
		for (int i = 0; i < n; i++) {
			m_par[i] = par[i];
			m_rank[i] = par[i] == i ? 1 : 0;
			m_setsize[par[i]]++;
		}
		m_maxsize = 0;
		for (std::map<int, int>::iterator mit = m_setsize.begin(); mit != m_setsize.end(); ++mit) {
			m_maxsize = std::max(mit->second, m_maxsize);
		}
	}

	int getMaxSize() const {
		return m_maxsize;
	}

	void printSets() {
		int n = m_par.size();
		_e << "sets: ";
		for (int i = 0; i < n; i++) {
			_e << m_par[i] << " ";
		}
		_e << _l;
	}

	std::string toString() {
		std::string s = "set: ";
		for (auto it = m_par.begin(); it != m_par.end(); ++it) {
			s += std::to_string(findSet(*it)) + " ";
		}
		s += "\n";
		s += "maxsize: " + std::to_string(m_maxsize) + "\n";
		return s;
	}

	void unionSets(const int &i1, const int &i2);
	
	void append();

	int findSet(const int& i);

	bool inSameSet(const int &i1, const int &i2);

private:
	std::vector<int> m_par;
	std::vector<int> m_rank;
	std::map<int, int> m_setsize;
	int m_maxsize;
};

// handle append now
void UnionFind::unionSets(const int &i1, const int &i2) {
	int n = m_par.size();
	//_e << "union: " << i1 << "," << i2 << " " << n << _l;
	assert(i1 <= n && i2 <= n);
	assert(i1 != i2);
	if (i1 == n) {
		int s2 = findSet(i2);
		m_par.push_back(s2);
		m_rank.push_back(0);
		m_setsize[s2]++;
		m_maxsize = std::max(m_maxsize, m_setsize[s2]);
	}
	else if (i2 == n) {
		int s1 = findSet(i1);
		m_par.push_back(s1);
		m_rank.push_back(0);
		m_setsize[s1]++;
		m_maxsize = std::max(m_maxsize, m_setsize[s1]);
	}
	else {
		int s1 = findSet(i1), s2 = findSet(i2);
		if (s1 == s2) return;
		if (m_rank[s1] < m_rank[s2]) {
			m_par[s1] = s2;
			m_setsize[s2] += m_setsize[s1];
			m_setsize.erase(s1);
			m_maxsize = std::max(m_maxsize, m_setsize[s2]);
		}
		else {
			m_par[s2] = s1;
			m_setsize[s1] += m_setsize[s2];
			m_maxsize = std::max(m_maxsize, m_setsize[s1]);
			m_setsize.erase(s2);
			if (m_rank[s1] == m_rank[s2]) m_rank[s1]++;
		}
	}
}

void UnionFind::append() {
	int n = m_par.size();
	m_par.push_back(n);
	m_rank.push_back(0);
	m_setsize[n] = 1;
}

int UnionFind::findSet(const int& i) {
	if (m_par[i] == i) return i;
	else return findSet(m_par[i]);
}

bool UnionFind::inSameSet(const int& i1, const int &i2) {
	return findSet(i1) == findSet(i2);
}