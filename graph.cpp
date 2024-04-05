#include <algorithm>
#include <climits>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "graph.h"

using namespace std;

// constructor, empty graph
// directionalEdges defaults to true
Graph::Graph(bool directionalEdges) { directEdge = !directionalEdges; }

// destructor
Graph::~Graph() {
  for (auto &i : graphVertices) {
    delete i;
  }
  graphVertices.clear();
}

// @return total number of vertices
int Graph::verticesSize() const { return graphVertices.size(); }

// @return total number of edges
int Graph::edgesSize() const {
  int retrn{0};
  for (auto *i : graphVertices) {
    retrn += i->edges.size();
  }
  return (directEdge ? retrn / 2 : retrn);
}

int Graph::findVertexIndex(const string &vertexLabel,
                           const string &targetLabel) const {
  // If looking for a vertex in the main graphVertices list
  if (vertexLabel.empty()) {
    for (size_t i = 0; i < graphVertices.size(); ++i) {
      if (graphVertices[i]->name == targetLabel) {
        return static_cast<int>(i);
      }
    }
  } else {
    // If looking for an edge in a specific vertex's edge list
    int vertexIndex = findVertexIndex("", vertexLabel);
    if (vertexIndex != -1) { // Ensure the vertex exists
      const auto &edges = graphVertices[vertexIndex]->edges;
      for (size_t i = 0; i < edges.size(); ++i) {
        if (edges[i].first->name == targetLabel) {
          return static_cast<int>(i);
        }
      }
    }
  }
  return -1; // Return -1 if not found
}

// @return number of edges from given vertex, -1 if vertex not found
int Graph::vertexDegree(const string &label) const {
  int vertexIndex = findVertexIndex("", label);
  if (vertexIndex != -1) {
    return static_cast<int>(graphVertices[vertexIndex]->edges.size());
  }
  return -1; // More explicitly return -1 when the vertex is not found
}

// @return true if vertex added, false if it already is in the graph
bool Graph::add(const string &label) {
  if (!contains(label)) {
    Vertex *newVertex = new Vertex(label);

    // Find the insertion point using binary search since graphVertices is
    // sorted
    auto it = lower_bound(graphVertices.begin(), graphVertices.end(), newVertex,
                          [](const Vertex *lhs, const Vertex *rhs) {
                            return lhs->name < rhs->name;
                          });

    graphVertices.insert(it, newVertex);
    return true;
  }
  return false;
}

/** return true if vertex already in graph */
bool Graph::contains(const string &label) const {
  return findVertexIndex("", label) != -1;
}

// @return string representing edges and weights, "" if vertex not found
// A-3->B, A-5->C should return B(3),C(5)
string Graph::getEdgesAsString(const string &label) const {
  int vertexIndex = findVertexIndex("", label);
  if (vertexIndex != -1) {
    stringstream ss;
    const auto &edges = graphVertices[vertexIndex]->edges;
    for (size_t i = 0; i < edges.size(); ++i) {
      ss << edges[i].first->name << "(" << edges[i].second << ")";
      if (i < edges.size() - 1) {
        ss << ",";
      }
    }
    return ss.str();
  }
  return "";
}

// @return true if successfully connected
bool Graph::connect(const string &from, const string &to, int weight) {
  // Ensure both vertices exist in the graph, add them if not.
  if (!contains(from)) {
    add(from);
  }
  if (!contains(to) && from != to) {
    add(to);
  }

  // Obtain indexes after potential addition of vertices
  int fromIndex = findVertexIndex("", from);
  int toIndex = findVertexIndex("", to);

  // Avoid adding duplicate edges or loops
  if (fromIndex == -1 || toIndex == -1 || from == to ||
      findVertexIndex(from, to) != -1) {
    return false;
  }

  auto fromPos =
      lower_bound(graphVertices[fromIndex]->edges.begin(),
                  graphVertices[fromIndex]->edges.end(), to,
                  [&](const pair<Vertex *, int> &a, const string &b) {
                    return a.first->name < b;
                  });
  graphVertices[fromIndex]->edges.insert(fromPos,
                                         {graphVertices[toIndex], weight});

  // For undirected graphs, add an edge in the opposite direction
  if (directEdge) {
    auto toPos =
        lower_bound(graphVertices[toIndex]->edges.begin(),
                    graphVertices[toIndex]->edges.end(), from,
                    [&](const pair<Vertex *, int> &a, const string &b) {
                      return a.first->name < b;
                    });
    graphVertices[toIndex]->edges.insert(toPos,
                                         {graphVertices[fromIndex], weight});
  }

  return true;
}

bool Graph::disconnect(const string &from, const string &to) {
  if (!contains(from) || !contains(to) || from == to) {
    return false;
  }

  bool disconnected = false;
  int fromIndex = findVertexIndex("", from);
  int toIndex = findVertexIndex("", to);

  // Remove edge from 'from' to 'to'
  auto itFrom = std::find_if(graphVertices[fromIndex]->edges.begin(),
                             graphVertices[fromIndex]->edges.end(),
                             [&to](const pair<Vertex *, int> &edge) {
                               return edge.first->name == to;
                             });
  if (itFrom != graphVertices[fromIndex]->edges.end()) {
    graphVertices[fromIndex]->edges.erase(itFrom);
    disconnected = true;
  }

  // If the graph is undirected, remove the edge from 'to' to 'from'
  if (directEdge && disconnected) {
    auto itTo = std::find_if(graphVertices[toIndex]->edges.begin(),
                             graphVertices[toIndex]->edges.end(),
                             [&from](const pair<Vertex *, int> &edge) {
                               return edge.first->name == from;
                             });
    if (itTo != graphVertices[toIndex]->edges.end()) {
      graphVertices[toIndex]->edges.erase(itTo);
    }
  }

  return disconnected;
}

void Graph::dfsHelper(const Vertex *curr, vector<string> &visited) {
  if (find(visited.begin(), visited.end(), curr->name) == visited.end()) {
    visited.emplace_back(curr->name);
    for (const auto &edge : curr->edges) {
      dfsHelper(edge.first, visited);
    }
  }
}

void Graph::dfs(const string &startLabel, void visit(const string &label)) {
  if (this->contains(startLabel)) {
    vector<string> visited;
    string retrn;
    dfsHelper(graphVertices[findVertexIndex("", startLabel)], visited);
    for (const auto &item : visited) {
      retrn += item;
    }
    visit(retrn);
  }
}

void Graph::bfs(const string &startLabel, void visit(const string &label)) {
  if (this->contains(startLabel)) {
    vector<string> visited;
    string ret;
    queue<Vertex *> queue;
    Vertex *startVertex = graphVertices[findVertexIndex("", startLabel)];
    queue.push(startVertex);
    visited.push_back(startVertex->name);
    while (!queue.empty()) {
      Vertex *current = queue.front();
      queue.pop();
      for (const auto &edge : current->edges) {
        if (find(visited.begin(), visited.end(), edge.first->name) ==
            visited.end()) {
          visited.push_back(edge.first->name);
          queue.push(edge.first);
        }
      }
    }
    for (const auto &vertexName : visited) {
      ret += vertexName;
    }
    visit(ret);
  }
}

void Graph::dijkstraPrimHelper(Vertex *curr,
                               map<Vertex *, pair<vector<string>, int>> &holder,
                               int distance, vector<string> path,
                               map<Vertex *, int> &distanceHolder,
                               int pastDistance) const {
  if (holder.count(curr) == 0 || holder.at(curr).second > distance) {
    path.emplace_back(curr->name);
    if (holder.count(curr) == 0) {
      holder.emplace(curr, make_pair(path, distance));
    } else {
      holder.at(curr) = make_pair(path, distance);
    }
    if (distanceHolder.count(curr) == 0) {
      distanceHolder.emplace(curr, pastDistance);
    } else {
      distanceHolder.at(curr) = pastDistance;
    }
    for (auto &edge : curr->edges) {
      dijkstraPrimHelper(edge.first, holder, distance + edge.second, path,
                         distanceHolder, edge.second);
    }
  }
}

// store the weights in a map
// store the previous label in a map
pair<map<string, int>, map<string, string>>
Graph::dijkstra(const string &startLabel) const {
  map<string, int> weights;
  map<string, string> previous;
  if (this->contains(startLabel)) {
    vector<string> starter;
    map<Vertex *, pair<vector<string>, int>> holder;
    map<Vertex *, int> temp;
    dijkstraPrimHelper(graphVertices[findVertexIndex("", startLabel)], holder,
                       0, starter, temp, 0);
    holder.erase(graphVertices.at(findVertexIndex("", startLabel)));
    while (!holder.empty()) {
      int small = INT_MAX;
      int smallIndex = 0;
      for (int i = 0; i < graphVertices.size(); i++) {
        if (holder.count(graphVertices[i]) != 0 &&
            holder.at(graphVertices[i]).second < small) {
          small = holder.at(graphVertices[i]).second;
          smallIndex = i;
        }
      }
      weights.emplace(graphVertices[smallIndex]->name, small);
      previous.emplace(
          graphVertices[smallIndex]->name,
          holder.at(graphVertices[smallIndex])
              .first.at(holder.at(graphVertices[smallIndex]).first.size() - 2));
      holder.erase(graphVertices[smallIndex]);
    }
    return make_pair(weights, previous);
  }
  return make_pair(weights, previous);
}

// minimum spanning tree using Prim's algorithm. dijkstraPrimHelper gets
// the lowest path to every single vertex.
int Graph::mstPrim(const string &startLabel,
                   void visit(const string &from, const string &to,
                              int weight)) const {
  if (this->contains(startLabel)) {
    int ret{0};
    vector<string> starter;
    map<Vertex *, pair<vector<string>, int>> holder;
    map<Vertex *, int> dists;
    dijkstraPrimHelper(graphVertices[findVertexIndex("", startLabel)], holder,
                       0, starter, dists, 0);
    while (!holder.empty()) {
      int small = INT_MAX;
      int smallIndex = 0;
      for (int i = 0; i < graphVertices.size(); i++) {
        if (holder.count(graphVertices[i]) != 0 &&
            holder.at(graphVertices[i]).second < small) {
          small = holder.at(graphVertices[i]).second;
          smallIndex = i;
        }
      }
      if (holder.at(graphVertices[smallIndex]).first.size() > 1) {
        visit(holder.at(graphVertices[smallIndex])
                  .first.at(holder.at(graphVertices[smallIndex]).first.size() -
                            2),
              holder.at(graphVertices[smallIndex])
                  .first.at(holder.at(graphVertices[smallIndex]).first.size() -
                            1),
              dists.at(graphVertices[smallIndex]));
        ret += dists.at(graphVertices[smallIndex]);
      }
      holder.erase(graphVertices[smallIndex]);
    }
    return ret;
  }
  return -1;
}

// read a text file and create the graph
bool Graph::readFile(const string &filename) {
  ifstream myfile(filename);
  if (!myfile.is_open()) {
    cerr << "Failed to open " << filename << endl;
    return false;
  }
  int edges = 0;
  int weight = 0;
  string fromVertex;
  string toVertex;
  myfile >> edges;
  for (int i = 0; i < edges; ++i) {
    myfile >> fromVertex >> toVertex >> weight;
    connect(fromVertex, toVertex, weight);
  }
  myfile.close();
  return true;
}