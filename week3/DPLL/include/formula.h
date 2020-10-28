#ifndef FORMULA_H
#define FORMULA_H

#include <iostream>
#include <set>
#include <stdexcept>

enum Connective {wedge, vee};

typedef std::set<std::set<int>> CNF;

class Formula {
    public:
        enum Type{neg, binary, prop};
        Type type;
        
        virtual void print(std::ostream& os) const = 0;
        
        friend std::ostream& operator<<(std::ostream& os, const Formula& f) {
            f.print(os);
            return os;
        }
        virtual ~Formula() {}
    protected:
        Formula(Type t) : type(t) {}
};

class Prop : public Formula {
    
    public:
        int prop_var;
        Prop(int var_name) : Formula(prop) {
            if (var_name <= 0) {
                throw new std::runtime_error("var_name should be > 0");
            } else {
                prop_var = var_name;
            }
        }

        virtual void print(std::ostream& os) const {
            os << prop_var;
        }

};

class Negation : public Formula {
    
    public:
        Formula* f;
        
        Negation(Formula* f_) : Formula(neg), f(f_){}

        virtual void print(std::ostream& os) const {
            os << "!";
            f->print(os);
        }
        ~Negation() {
            if(f) {
                delete(f);
                f=nullptr;
            }
             };
};

class Binary : public Formula {
    
    public:
        Formula* l;
        Formula* r;
        Connective op;

        Binary(Formula* left, Formula* right, Connective conn) :
            Formula(binary), l(left), r(right), op(conn) {}

        virtual void print(std::ostream& os) const {
            os << "(";
            l->print(os);
            switch (op) {
            case vee:
                os << "\\/";
                break;
            case wedge:
                os << "/\\";
                break;
            }
            r->print(os);
            os << ")";
        }

        ~Binary(){
            if(l) {
                delete(l);
                l = nullptr;
            }
            if(r) {
                delete(r);
                r = nullptr;
            }
        }
};

#endif
