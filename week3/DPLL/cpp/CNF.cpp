#include "CNFTransformer.h"
#include <sstream>


const CNF& CNFTransformer::get_cnf() const{
    return cnf;
}

int CNFTransformer::get_max_prop(Formula* f){

    int max_prop = 1;

    switch (f->type) {
    
        case Formula::prop: { 
        
            auto prop = reinterpret_cast<Prop*>(f);
            if (prop->prop_var > max_prop){
                max_prop = prop->prop_var;
            }
            break;
        }
        case Formula::neg: {
        
            auto neg_proposition = reinterpret_cast<Negation*>(f);
            int new_max = get_max_prop(neg_proposition->f);

            if (new_max > max_prop) {
                max_prop = new_max;
            }
            break;
        }
        case Formula::binary: {
            auto binary_prop = reinterpret_cast<Binary*>(f);
            int left_max = get_max_prop(binary_prop->l);
            int right_max = get_max_prop(binary_prop->r);
            if (left_max > max_prop) {
                max_prop = left_max;
            }
            if (right_max > max_prop) {
                max_prop = right_max;
            }
            break;
        }
    
    }
    return max_prop; 
}

std::pair<int,CNF> CNFTransformer::transform_helper(Formula* f,int& max_prop) {
    
    switch (f->type) {
    
    case Formula::prop:{
        auto prop = reinterpret_cast<Prop*>(f);
        return std::pair<int,CNF>(prop->prop_var,std::set<std::set<int>>());
    } 
    case Formula::neg:{
        auto neg = reinterpret_cast<Negation*>(f);
        auto delta = transform_helper(neg->f,max_prop);
        return std::pair<int,CNF>(-delta.first,delta.second);
    }
    case Formula::binary: {
        auto binary = reinterpret_cast<Binary*>(f);
        switch (binary->op)
        {
        case Connective::wedge: {

            auto left = transform_helper(binary->l,max_prop);
            auto right = transform_helper(binary->r,max_prop);
            
            for(auto l : left.second) {
                right.second.insert(l);
            }
            max_prop += 1;


            right.second.insert(std::set<int>({-max_prop,left.first}));
            right.second.insert(std::set<int>({-max_prop,right.first}));
            right.second.insert(std::set<int>({max_prop,-right.first,-left.first}));
            
            return std::pair<int,CNF>(max_prop,right.second); 
        }
    case Connective::vee: {

            auto left = transform_helper(binary->l,max_prop);
            auto right = transform_helper(binary->r,max_prop);
            
            for(auto l : left.second) {
                right.second.insert(l);
            }
            max_prop += 1;

            right.second.insert(std::set<int>({max_prop,-left.first}));
            right.second.insert(std::set<int>({max_prop,-right.first}));
            right.second.insert(std::set<int>({-max_prop,right.first,left.first}));
            
            return std::pair<int,CNF>(max_prop,right.second);
        }
        
        }
    }
    }
    throw new std::runtime_error("Non-exhaustive pattern matching");
    
}

CNF CNFTransformer::transform(Formula* f) {

    int max_prop = get_max_prop(f);
    auto res = transform_helper(f,max_prop);
    res.second.insert(std::set<int>({res.first}));
    return res.second;
}

CNF CNFTransformer::transform(Formula* f, int max_prop) {

    auto res = transform_helper(f,max_prop);
    res.second.insert(std::set<int>({res.first}));
    return res.second;
}

CNFTransformer::CNFTransformer(Formula* f, int max_prop){
    cnf = transform(f,max_prop);
}


CNFTransformer::CNFTransformer(Formula* f){
    cnf = transform(f);
}

std::string trim(const std::string& str,
                 const std::string& whitespace = " \t")
{
    const auto strBegin = str.find_first_not_of(whitespace);
    if (strBegin == std::string::npos)
        return ""; // no content

    const auto strEnd = str.find_last_not_of(whitespace);
    const auto strRange = strEnd - strBegin + 1;

    return str.substr(strBegin, strRange);
}

CNFTransformer::CNFTransformer(std::ifstream& is) {
    
    //skip comments
    cnf = std::set<std::set<int>>();
    if(!is) {
        throw new std::runtime_error("Ifstream is not opened");
    }
    std::string line;
    while (std::getline(is,line))
    {   
        std::string trimmed = trim(line);

        if (trimmed.rfind("c", 0) == 0) {
            continue;
        } else if (trimmed.rfind("p",0) == 0) {
            continue;
        }  else {
            
            int i;

            std::stringstream ss (trimmed);
            std::set<int> clause;
            while (ss >> i)
            {
                if(i != 0) {
                   clause.insert(i); 
                } else {
                    cnf.insert(clause);
                    clause.clear();
                }
            }
            
        }
    }
    
}


std::ostream& operator<<(std::ostream& out, const RESULT value){
    const char* s = 0;
#define PROCESS_VAL(p) case(p): s = #p; break;
    switch(value){
        PROCESS_VAL(SAT);     
        PROCESS_VAL(UNSAT);     
    }
#undef PROCESS_VAL

    return out << s;
}

std::ostream& operator<<(std::ostream& out, const interpretation model){
    out << "{ ";
    for (auto e : model) {
        out << e << " ";
    }
    return out << "}\n";
}