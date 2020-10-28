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
        CNFTransformer(std::ifstream& is);
        static int get_max_prop(Formula* f);
        CNF cnf;

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
        CNF transform(Formula* f);
        std::pair<int,CNF> transform_helper(Formula*f,int& max_prop);
};

#endif