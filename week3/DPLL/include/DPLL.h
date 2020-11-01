#ifndef DPLL_H
#define DPLL_H

#include <CNFTransformer.h>

enum STATE {SAT_STATE, UNSAT_STATE, UNDERFINED_STATE};


class DPLL_solver{
    
    public:
        DPLL_solver();
        
        // void add_clause(const std::set<int>& clause); 
        
        // void add_clause(const std::set<std::set<int>>& clauses);

        void add_clause(std::set<int> clause); 
        
        void add_clause(std::set<std::set<int>> clauses);

        const std::set<int>& get_atoms() const;

        std::set<int> get_model() const;

        RESULT satisfies(interpretation& I) const;
        RESULT solve();

        friend std::ostream& operator<<(std::ostream& os, const DPLL_solver& s) {
            os << "{ " ;
            for(auto s : s.cnf){
                os << "{ ";
                for(auto e : s) {
                    os << e <<" ";
                }
                os << "} ";
            }
            os << "}\n";
            return os;
        }

    private:
        STATE state;
        CNF cnf;
        std::set<int> atoms;
        void remove_absorbed();
        RESULT dpll(CNF,interpretation&);
        CNF unit_propagate(CNF, int);
        void eliminate_pure_literal(CNF&, int);
        int choose_literal(CNF&);
        int has_unit(CNF&);
        int has_pure(CNF&);
        std::set<int> build_literals(CNF&);
        std::set<int> build_pure_literals(const std::set<int>&);
        interpretation model;
};

std::ostream& operator<<(std::ostream& out, const RESULT value);
std::ostream& operator<<(std::ostream& out, const interpretation model);

#endif