from pysat.solvers import Glucose3
from pysat.solvers import Glucose4
from pysat.formula import CNF
from pysat.solvers import MapleCM
import time
import sys


def construct_formulaCNF(k,v):
    
    num_edges = int(v * (v-1) / 2)

    g = MapleCM()
    
    # all colored
    for i in range(num_edges):
        g.add_clause([(i * k + c + 1) for c in range(k)])
    
    # only one color
    for i in range(num_edges):
        for c in range(k):
            for c_1 in range(k):
                if c_1 != c:
                    g.add_clause([-(i * k + c + 1), -(i * k + c_1 + 1)])
    
    edges = {}
    counter = 0
    # enumerate edges
    for i in range(v):
        for j in range(i+1,v):
                edges[(i,j)] = counter
                counter += 1  
    # for each triangle:
    print(edges)

    for c in range(k):
        for i in range(v):
            for j in range(i+1,v):
                for m in range(j+1,v):
                    e1 = edges[(i,j)]
                    e2 = edges[(i,m)]
                    e3 = edges[(j,m)]
                    g.add_clause([- (e1 * k + c + 1),-(e2 * k + c + 1),-(e3 * k + c + 1)])
    
    return g.solve()


# find maximum clique for num_colors=k

def max_clique(num_colors):
    result = 1
    v = 1
    while(True):
        print(f"{v}",end="\r",flush=True)
        if not construct_formulaCNF(num_colors,v):
            return result
        else:
            result = v
            v += 1

if __name__ == "__main__":
    
    k = int(sys.argv[1])
    assert(k > 0)
    print(f"Quering max clique size for {k} colors")
    start = time.perf_counter_ns()
    print(max_clique(k))
    end = time.perf_counter_ns()
    print(f"time: {int((end-start) / 1_000_000)} ms")
    

