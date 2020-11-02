#include <DPLL.h>
#include <cassert>


DPLL_solver::DPLL_solver(){
    
    cnf = std::set<std::set<int>>();
    state = STATE::UNDERFINED_STATE;
    atoms = std::set<int>();
    model = std::set<int>();
};

DPLL_solver::DPLL_solver(const DPLL_solver& another) {
    
    cnf = another.cnf;
    state = another.state;
    atoms = another.atoms;
    model = another.model;
    max_literal = another.max_literal;

}

DPLL_solver DPLL_solver::operator=(const DPLL_solver& another) {
    
    cnf = another.cnf;
    state = another.state;
    atoms = another.atoms;
    model = another.model;
    max_literal = another.max_literal;

}

void DPLL_solver::add_clause(std::set<int> clause) {
    
    cnf.insert(clause);
    state = STATE::UNDERFINED_STATE;
    for (auto i: clause) {
        atoms.insert(std::abs(i));
        if(abs(i) > max_literal) {
            max_literal = abs(i);
        }
    }
}

void DPLL_solver::add_clause(std::set<std::set<int>> clauses) {
    
    state = STATE::UNDERFINED_STATE;
    for (auto s : clauses) {
        add_clause(s);
    }
}

void DPLL_solver::add_clause(std::string clause) {
    
    auto prop = Proposition(clause);
    auto cnf = CNFTransformer(prop.get(),max_literal).get_cnf();
    add_clause(cnf);
}

const CNF& DPLL_solver::get_clauses() const {
    return cnf;
}

void DPLL_solver::remove_clause(std::set<int> clause) {
    if (cnf.erase(clause)) max_literal = update_max_literal();
}
        
void DPLL_solver::remove_clause(std::set<std::set<int>> clauses) {
    for(auto& clause : clauses) {
        remove_clause(clause);
    }
}


// void DPLL_solver::add_clause(const std::set<int>& clause) {
    
//     cnf.insert(clause);
//     state = STATE::UNDERFINED_STATE;
//     for (auto i: clause) {
//         atoms.insert(std::abs(i));
//     }
// }

// void DPLL_solver::add_clause(const std::set<std::set<int>>& clauses) {
    
//     state = STATE::UNDERFINED_STATE;
//     for (auto s : clauses) {
//         add_clause(s);
//     }
// }

RESULT DPLL_solver::solve() {
    auto model_ = std::set<int>();
    auto result = dpll(cnf,model_);
    switch (result)
    {
    case RESULT::SAT:
        state = STATE::SAT_STATE;
        model = model_;
        break;
    case RESULT::UNSAT:
        state = STATE::UNSAT_STATE;
        break;
    default:
        break;
    }
    return result;
}

RESULT DPLL_solver::dpll(CNF cnf_, interpretation& model_) {

    if(cnf_.empty()) {
        // model = model_;
        return SAT;
    }
    if(cnf_.count(std::set<int>())) return UNSAT;
    //for each unit
    int unit;

    while (unit = has_unit(cnf_))
    {
        //unit propagate   
        cnf_ = unit_propagate(cnf_,unit);
        model_.insert(unit);
        
        
    }
    int pure_literal;
    while (pure_literal = has_pure(cnf_)){
        
        eliminate_pure_literal(cnf_,pure_literal);
        model_.insert(pure_literal);
    }

    
    if(cnf_.empty()) {
        // model = model_;
        return SAT;
    }
    if(cnf_.count(std::set<int>())) return UNSAT;
    auto literal = choose_literal(cnf_);
    
    cnf_.insert(std::set<int>({literal}));
    model_.insert(literal);
    if(dpll(cnf_,model_) == SAT){
        // model = model_; 
        return SAT;
    } else {
        cnf_.erase(std::set<int>({literal}));
        model_.erase(literal);
        cnf_.insert(std::set<int>({-literal}));
        model_.insert(-literal);
        
        return dpll(cnf_,model_);
    }

}

int DPLL_solver::choose_literal(CNF& cnf_) {
    auto literals = build_literals(cnf_);
    if(literals.empty()) {
        throw new std::runtime_error("No literals left");
    }
    return *literals.begin();
}

void DPLL_solver::eliminate_pure_literal(CNF& cnf_, int pure) {
    auto to_be_removed = std::set<std::set<int>>();

    for(auto& s : cnf_) {
        if(s.count(pure)) to_be_removed.insert(s);
    }
    for(auto& s: to_be_removed) {
        cnf_.erase(s);
    }
    
} 

CNF DPLL_solver::unit_propagate(CNF cnf_, int unit){
    
    auto to_be_removed = std::set<std::set<int>>();
    auto new_set = std::set<std::set<int>>();
    
    //remove disjuncts
    for (auto s: cnf_) {
        if(s.count(unit)) to_be_removed.insert(s);
    }

    for (auto s : to_be_removed) {
        assert(cnf_.erase(s) == 1);
    }
    //
    
    //remove literals
    for (auto s : cnf_) {
        if(s.count(-unit)) s.erase(-unit);
        new_set.insert(s);
    }

    return new_set;
}

std::set<int> DPLL_solver::build_literals(CNF& cnf_) {
    
    auto literals = std::set<int>();
    for (auto& s : cnf_) {
        for (auto l : s){
            literals.insert(l);
        }
    }
    return literals;
}


std::set<int> DPLL_solver::build_pure_literals(const std::set<int>& literals) {
    
    auto pure_literals = std::set<int>();

    for (auto l : literals) {
        if (literals.count(-l) == 0) pure_literals.insert(l);
    }
    return pure_literals;
}

int DPLL_solver::has_unit(CNF& cnf_) { //zero means no unit
    
    for (auto s : cnf_) {
        if (s.size() == 1) {
            return *s.begin(); 
        } 
    }
    return 0;
}

int DPLL_solver::has_pure(CNF& cnf_) {
    
    auto literals = build_literals(cnf_);
    auto pure_literals = build_pure_literals(literals);
    
    if(pure_literals.empty()) return 0;
    else return *pure_literals.begin();

}


interpretation DPLL_solver::get_model() const{
    
    if (state != STATE::SAT_STATE) {
        throw new std::runtime_error("state is not SAT_STATE");
    }
    bool all_sat = true;
    
    auto new_model = model;

    for (auto e : model) {
        if(atoms.count(std::abs(e))) all_sat = false;
    }
    if(!all_sat) {
        for (auto a : atoms) {
            if(!(model.count(a) || model.count(-a))) {
                new_model.insert(a);
            }
        }
    }
    return new_model;
}

RESULT DPLL_solver::satisfies(interpretation& I) const {
    
    bool sat = true;
    interpretation model_ = get_model();
    for(auto clause : cnf) {
        bool sat_local = false;
        for(auto literal : clause) {
            if(model_.count(literal)){
                sat_local = true;
            }
        }
        sat = sat && sat_local;
    }
    if(sat) return SAT;
    else return UNSAT;
}

const std::set<int>& DPLL_solver::get_atoms() const{
    return atoms;
}

int DPLL_solver::get_max_literal() const {
    return max_literal;
}

int DPLL_solver::update_max_literal() {
    int max_literal_ = 0;
    for (auto& disj : cnf) {
        for (auto literal : disj) {
            if (std::abs(literal) > max_literal_) {
                max_literal_ = std::abs(literal); 
            }
        }
    }
    return max_literal_;
}

// void DPLL_solver::remove_absorbed(){
    
// }

// void remove_absorbed(CNF& cnf, std::set<int>& phi) {

// }
    