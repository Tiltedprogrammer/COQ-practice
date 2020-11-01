#include <prop_parser.h>
#include <CNFTransformer.h>
#include <DPLL.h>
#include <cassert>
#include <map>


RESULT build_problem3(int k, int v){
    
    int num_edges = (v * (v-1)) / 2;

    auto g = DPLL_solver();

    //each edge colored
    for(int i = 0; i < num_edges; i++){
        std::set<int> edge_colored = std::set<int>();
        for(int c = 0; c < k; c++) {
            edge_colored.insert(i * k + c + 1);
        }
        g.add_clause(edge_colored);
    }
    //colored once
    for(int i = 0; i < num_edges; i++) {
        for (int c = 0; c < k; c++) {
            for (int c_1 = 0; c_1 < k; c_1++) {
                if(c_1 != c) {
                    g.add_clause(std::set<int>({-(i * k + c + 1), -(i * k + c_1 + 1)}));
                }
            }
        }
    }

    auto edges = std::map<std::pair<int,int>,int>();

    for(int i = 0, e = 0; i < v; i++) {
        for (int j = i + 1; j < v; j++, e++) {
            edges.insert(std::pair<std::pair<int,int>,int>(std::pair<int,int>(i,j),e));
        }
    }

    //for each triangle

    for (int c = 0; c < k; c++) {
        for (int i = 0; i < v; i++) {
            for (int j = i + 1; j < v; j++) {
                for (int l = j + 1; l < v; l++) {
                    auto e1 = edges[std::pair<int,int>(i,j)];
                    auto e2 = edges[std::pair<int,int>(i,l)];
                    auto e3 = edges[std::pair<int,int>(j,l)];
                    g.add_clause(std::set<int>{-(e1 * k + c + 1),-(e2 * k + c + 1),-(e3 * k + c + 1)});
                }
            }
        }
    }

    return g.solve();

}

int solve_problem3(int k) {
    int result = 1;
    int v = 1;
    while(true) {
        std::cout << v << "\n";
        if (build_problem3(k,v) == UNSAT) {
            return result;
        } else {
            result = v;
            v += 1;
        }
    }
}


int main(int argc, char const *argv[])
{
    // Parse any proposition that contains only integers as atoms (except 0)
    // and ~, &, | standing for \neg, \wedge, \vee resepctively
    
    //Retunrn unique_ptr to abstact class formula
    auto f = Proposition(std::string("~ 1 & 1"));

    //pretty prints the formula
    std::cout << *f.get() << std::endl;
    
    //transforms the formula to CNF via Tseitin
    //or loads DIMACS through @istream
    auto f_cnf = CNFTransformer(f.get());
    
    //pretty prints
    std::cout <<  f_cnf << std::endl;
    
    //DPLL solver
    auto solver1 = DPLL_solver();
    
    //add signle clause such as @std::set<int> or many clauses at once
    // @std::set<std::set<int>>
    solver1.add_clause(f_cnf.get_cnf());

    assert(solver1.solve() == UNSAT);

    //find max clique
    std::cout << solve_problem3(3) << std::endl;
    
    return 0;
}
