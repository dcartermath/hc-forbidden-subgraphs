import itertools as it
import igraph as ig
from pysat.formula import CNF
from pysat.solvers import Solver
from pysat.card import CardEnc

def powerset(iterable):
    s = list(iterable)
    return it.chain.from_iterable(it.combinations(s, r) for r in range(len(s)+1))

### Helper graph functions

def dom_edges(G):
    '''Generator of dominating edges of G.'''
    for e in G.get_edgelist():
        if len(set(G.neighbors(e[0])) | set(G.neighbors(e[1]))) == G.vcount():
            yield e

def is_subgraph(G, H):
    '''Is H an induced subgraph of G?'''
    return G.subisomorphic_lad(H, induced=True)

def contains_obs(G, Hs):
    '''Is any H in Hs an induced subgraph of G?'''
    return any(is_subgraph(G, H) for H in Hs)

def reduce(L):
    '''Return list containing one representative from each isomorphism class
of graphs in L.'''
    out = []
    for i,G in enumerate(L):
        for j,H in enumerate(L[i+1:], i+1):
            if G.isomorphic(H):
                break
        else:
            out.append(G)
    return out

def complement(G):
    return G.complementer(loops=False)

def four_clique(G, baseG):
    '''Find, if possible, a set of four cliques that cover G, such that
the overlap on vertex subset baseG is at least 2 vertices. Modelled as
a SAT instance.'''
    rev = [(v, i) for v in range(G.vcount()) for i in range(4)]
    var = {x:i+1 for i,x in enumerate(rev)}
    clauses = []
    for v in range(G.vcount()):
        clauses.append([var[(v, i)] for i in range(4)])
    for (a,b) in complement(G).get_edgelist():
        for i in range(4):
            clauses.append([-var[(a, i)], -var[(b, i)]])
    cnf = CNF(from_clauses=clauses)
    card = CardEnc.atleast([var[(v, i)] for v in baseG for i in range(4)],
                           len(baseG)+2, top_id=len(rev)+1)
    cnf.extend(card)
    with Solver(bootstrap_with=cnf) as solver:
        if solver.solve():
            model = solver.get_model()
            cliques = [[], [], [], []]
            for i in model:
                if i > 0 and i < len(rev):
                    cliques[rev[i-1][1]].append(rev[i-1][0])
            return tuple(tuple(c) for c in cliques)
        return False

### Graph constructors

def gen_coning(G, H):
    '''Add an H complete to G. Called "join" in the paper.'''
    n = G.vcount()
    m = H.vcount()
    I = G.copy()
    I.add_vertices(H.vcount())
    I.add_edges((a + n, b + n) for (a,b) in H.get_edgelist())
    I.add_edges((v, u + n) for v in range(n) for u in range(m))
    return I

def parse_tikz(filename):
    '''Parse the TeX/TikZ source for Figures 3 and 4 to extract graphs H_i' and I_j.'''
    out = []
    with open(filename, 'r') as f:
        for line in f:
            L = line.strip()
            if L.startswith('\\begin{tikzpicture}'):
                G = ig.Graph()
            elif L.startswith('\\end{tikzpicture}'):
                out.append(complement(G))
            elif L.startswith('\\labvert'):
                G.add_vertex()
            elif L.startswith('\\vert'):
                G.add_vertex()
            elif L.startswith('\\edge'):
                i1 = L.index('{')
                j1 = L.index('}')
                i2 = L.index('{', j1+1)
                j2 = L.index('}', j1+1)
                G.add_edge(int(L[i1+1:j1]) - 1, int(L[i2+1:j2]) - 1)
    return out

#Hp[i] = H_{i+1}'
Hp = parse_tikz('hp_figure')
#I[i] = I_{i+1}
I = parse_tikz('i_figure')

k3compl = ig.Graph(3)
h7 = ig.Graph([(0, 3), (0, 2), (1, 6), (1, 5), (1, 4), (1, 3),
               (2, 6), (2, 4), (3, 5), (4, 6), (4, 5), (5, 6)])
w5 = ig.Graph([(0, 5), (0, 3), (0, 2), (1, 5), (1, 4), (1, 3),
               (2, 5), (2, 4), (3, 5), (4, 5)])
k23compl = ig.Graph([(0, 4), (0, 2), (1, 3), (2, 4)])
k7 = ig.Graph.Full(7)

### Paper algorithms

def canon_order(attaches):
    '''The order to add new graphs to the frontier.'''
    return sorted(attaches, key=lambda x: x.neighbors(x.vcount()-1),
                  reverse=True)

def attach(G, obss, forced=set(), avoid=set()):
    '''All graphs formed by adding one vertex to G that is adjacent to forced
and nonadjacent to avoid while not introducing any obstruction in obss, by
brute force.'''
    n = G.vcount()
    out = []
    for a in powerset([i for i in range(n) if i not in forced | avoid]):
        a = sorted(set(a) | forced)
        new = G.copy()
        new.add_vertex()
        new.add_edges((n, x) for x in a)
        if not contains_obs(new, obss + out):
            out.append(new)
    return out

def graft(G, H, obss, pairs, to_reduce=True):
    '''Graft H onto G with corresponding pairs in all possible ways; i.e. form all
(G U H)/~ with u~v for pairs (u,v), where the union is NOT disjoint (there are edges
between G and H).'''
    corr = {v:u for u,v in pairs}
    m = H.vcount()
    out = [G.copy()]
    i = G.vcount()
    for v in range(m):
        if v in corr:
            continue
        newposs = []
        for poss in out:
            forced = {corr[v2] for v2 in H.neighbors(v) if v2 in corr}
            newposs.extend(attach(poss, obss, forced,
                                  set(corr.values()) - forced))
        out = newposs
        corr[v] = i
        i += 1
    if to_reduce:
        return reduce(out)
    return out

def adv_attach(G, obss, forced=set(), avoid=set(), to_reduce=True):
    '''All graphs formed by adding one vertex to G that is adjacent to forced
and nonadjacent to avoid while not introducing any obstruction in obss, by using
graft.'''
    f = len(forced)
    a = len(avoid)
    #H defines the neighborhood of the new vertex (vertex f+a in H)
    H = G.induced_subgraph(forced | avoid)
    corr = sorted(forced | avoid) #index in H -> index in G
    revcorr = {v:k for k,v in enumerate(corr)} #the reverse
    H.add_vertex()
    H.add_edges((f+a, revcorr[x]) for x in forced)
    #grafting G onto H is faster
    poss = graft(H, G, obss, list(enumerate(corr)), to_reduce)
    corr.append(G.vcount())
    #restore vertex order
    for v in range(G.vcount()):
        if v not in forced and v not in avoid:
            corr.append(v)
    return canon_order([out.permute_vertices(corr) for out in poss])

def four_clique_solve(G, obss, coning_level=0, cached=None):
    '''Algorithm 3 with caching, and also Algorithm 2 (when coning_level is set to 0 or -1).
Here coning_level is the input k.'''
    if cached is None:
        attachments = []
        forced = []
        dominating = set()
        nonedges = {(a,b) for (a,b) in it.combinations(range(G.vcount()), 2)
                    if (a,b) not in G.get_edgelist()}
        n = G.vcount()
        cone = tuple(range(n))
        for H in adv_attach(G, obss, to_reduce=False):
            s = tuple(H.neighbors(n))
            attachments.append(s)
            for e in dom_edges(H):
                dominating.add(s)
                break
            for t in attachments[:-1]:
                if len(set(s) | set(t)) != G.vcount(): #k3compl condition
                    forced.append((s, t))
                    continue
                I = H.copy()
                I.add_vertex()
                I.add_edges([(n+1, x) for x in t])
                if contains_obs(I, obss):
                    forced.append((s, t))
    else:
        attachments = list(cached[0])
        forced = list(cached[1])
        cone = tuple(cached[2])
        dominating = set(cached[3])
    cache_attachments = list(attachments)
    cache_forced = list(forced)
    sup = G.copy()
    #coning_level == -1 represents the call to Algorithm 2 with modified P.
    if coning_level == -1:
        attachments = [a for a in attachments if a not in dominating]
        A = set(attachments)
        translate = {v:G.vcount() + i for i,v in enumerate(attachments)}
        forced = [(a,b) for a,b in forced if a in A and b in A]
        sup.add_vertices(len(attachments))
        sup.add_edges((translate[s],x) for s in attachments for x in s)
        sup.add_edges((translate[a], translate[b]) for (a,b) in forced)
        return (four_clique(sup, list(range(G.vcount()))),
                (cache_attachments, cache_forced, cone, dominating))
    attachments = [a for a in attachments if a != cone]
    A = set(attachments)
    translate = {v:G.vcount() + i for i,v in enumerate(attachments)}
    translate |= {(cone, i):G.vcount() + len(attachments) + i
                      for i in range(coning_level)}
    forced = [(a,b) for a,b in forced if a in A and b in A] \
             + [((cone, i), b) for (a,b) in forced for i in range(coning_level)
                if a == cone] \
             + [((cone, i), a) for (a,b) in forced for i in range(coning_level)
                if b == cone]
    sup.add_vertices(len(attachments) + coning_level)
    sup.add_edges([(translate[s],x) for s in attachments for x in s])
    sup.add_edges([(translate[(cone, i)], x) for x in cone for i in range(coning_level)])
    sup.add_edges((translate[a], translate[b]) for (a,b) in forced)
    return (four_clique(sup, list(range(G.vcount()))),
            (cache_attachments, cache_forced, cone, dominating))

MP3 = ig.Graph.Ring(5, circular=False)
MP3.add_vertex()
MP3.add_edge(2, 5)
#CONINGS[k] = F_k
CONINGS = [ig.Graph(1),
           ig.Graph(2),
           ig.Graph.Ring(4, circular=False),
           complement(MP3)]
def continuation(G, obss):
    '''Given H' from the frontier, returns the list of graphs to add to the frontier.'''
    #single step from Algorithm 1
    for e in sorted(dom_edges(G), key=lambda x:sorted(x, reverse=True)):
        return adv_attach(G, obss, avoid=set(e))
    #Algorithm 3
    cache = None
    for coning_level in [3,2,1,0]:
        sol, cache = four_clique_solve(G, obss, coning_level, cache)
        if sol:
            H = CONINGS[coning_level]
            I = gen_coning(G, H)
            if not contains_obs(I, obss):
                return [I]
            return []
    #Algorithm 2 with dominating edge condition
    sol, cache = four_clique_solve(G, obss, -1, cache)
    if sol:
        out = []
        new_node = G.vcount()
        for x in sorted(cache[3], key=sorted, reverse=True):
            H = G.copy()
            H.add_vertex()
            H.add_edges((new_node, v) for v in x)
            if not contains_obs(H, obss + out):
                out.append(H)
        return out
    #All checks failed
    return None

def one_step(frontier, obss, weight=0):
    '''Chooses an H' from the frontier, pops it, computes its continuation, returns
the new frontier and adds to weight accordingly. This is one iteration of the main while
loop in Algorithm 4.'''
    G = frontier[-1]
    frontier = frontier[:-1]
    new = continuation(G, obss + frontier)
    if new is None:
        return (True, frontier, weight)
    for H in new:
        frontier.append(H)
        weight += 2**H.vcount()
    return (False, frontier, weight)

def solver(start, obss):
    '''Algorithm 4.'''
    if contains_obs(start, obss):
        return (True, 0, 0)
    frontier = [start] #set A in Algorithm 4
    weight = 2**start.vcount()
    number = 0
    while frontier:
        number += 1
        peek = frontier[-1]
        fails, frontier, weight = one_step(frontier, obss, weight)
        if fails: #this should never happen in verification
            return (False, number, weight, peek)
    return (True, number, weight)

### Verification code

to_verify = []
with open('edges_figure') as f:
    for line in f:
        if line.strip().startswith('\\draw'):
            G = line.strip().split(' ')[1].replace('(', '').replace(')', '').replace(';', '')
            H = line.strip().split(' ')[3].replace('(', '').replace(')', '').replace(';', '')
            if G == 'K23c':
                Ggraph = k23compl
            elif G == 'W5':
                Ggraph = w5
            elif G == 'H7':
                Ggraph = h7
            elif G == 'K7':
                Ggraph = k7
            elif G.startswith('H'):
                Ggraph = Hp[int(G[1:-1]) - 1]
            else: # if G.startswith('I'):
                Ggraph = I[int(G[1:]) - 1]
            if H.startswith('H'):
                Hgraph = Hp[int(H[1:-1]) - 1]
            else: # if H.startswith('I'):
                Hgraph = I[int(H[1:]) - 1]
            to_verify.append((Ggraph, Hgraph, G, H))

for Ggraph, Hgraph, G, H in to_verify:
    out = solver(Ggraph, [k3compl, Hgraph])
    assert out[0]
    print(G, H, out[1], out[2])
