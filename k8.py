import itertools as it
import igraph as ig
import networkx as nx

### Helper graph functions

def dom_edges(G):
    '''Generator of dominating edges of G.'''
    for e in G.get_edgelist():
        if len(set(G.neighbors(e[0])) | set(G.neighbors(e[1]))) == G.vcount():
            yield e

def complement(G):
    return G.complementer(loops=False)

### Theorem 3 verification

L = []
with open('r38_27.g6', 'rb') as f:
    for line in f:
        L.append(line.strip())

counts = [0,0]
for i,s in enumerate(L):
    G = complement(ig.Graph.from_networkx(nx.from_graph6_bytes(s)))
    for e in dom_edges(G):
        counts[0] += 1
        break
    else: # Check for connected dominating matchings with 2 edges
        for ((u,v),(x,y)) in it.combinations(G.get_edgelist(), 2):
            if not {u,v} & {x,y} and \
               (set(G.neighbors(x)) & {u,v} or set(G.neighbors(y)) & {u,v}): #connected
                for z in range(G.vcount()): #dominating
                    if z not in {u,v,x,y} \
                       and ((z not in G.neighbors(u) and z not in G.neighbors(v))
                            or (z not in G.neighbors(x) and z not in G.neighbors(y))):
                            break # If this happens, ((u,v),(x,y)) is not dominating
                else: # If the for loop falls through, ((u,v),(x,y)) is dominating
                    counts[1] += 1
                    break
        else: # There is no connected dominating matching with <= 2 edges
            assert False
    if i % 10000 == 0:
        print(i+1, '/', len(L), counts)
print(len(L), '/', len(L), counts)
