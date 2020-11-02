#ifndef CNFTRANSFORMER_H
#define CNFTRANSFORMER_H

#include "formula.h"
#include <utility>
#include <stdexcept>
#include <memory>
#include <fstream>

class CNFTransformer{
    public:
        CNFTransformer(Formula* f);
        CNFTransformer(Formula* f, int max_literal);
        CNFTransformer(std::ifstream& is);
        
        static int get_max_prop(Formula* f);
        
        const CNF& get_cnf() const;

        friend std::ostream& operator<<(std::ostream& os, const CNFTransformer& cnf) {
            os << "{ " ;
            for(auto s : cnf.cnf){
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
        CNF cnf;
        CNF transform(Formula* f);
        CNF transform(Formula* f,int max_prop);
        std::pair<int,CNF> transform_helper(Formula*f,int& max_prop);
};

#endif