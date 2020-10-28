#include "cppcmb.hpp"
#include "formula.h"
#include <string_view>
#include <cmath>
#include <memory>
#include <utility>
#include <stdexcept>
#include <algorithm>

// parser combinator
namespace pc = cppcmb;
enum AST_op {lor,land,neg};


class AST{
    public:

        AST(int p) : content(p),left_(nullptr),right_(nullptr){};
        AST(AST_op op, AST* left, AST* right) : op_(op),left_(left),right_(right){};
        
        int get_content() const {
            if(this->is_leaf()) {
                return content;
            } else {
                throw new std::runtime_error("Non leaf Node");
            }
        }
        AST (const AST& a) {
            if (a.is_leaf()){
                content = a.content;
            } else {
                op_ = a.op_;
            }
            left_ = a.left_;
            right_ = a.right_;
        }
        AST_op get_op() const{
            return op_;
        }
        AST* get_left() const{
            return left_;
        }
        AST* get_right() const{
            return right_;
        }
        bool is_leaf() const {
            if ((!right_ && !left_)) {
                return true;
            } else {
                return false;
            }
        }
        ~AST() {
            if(left_) {
                delete(left_);
                left_ = nullptr;
            }
            if(right_) {
                delete(right_);
                right_ = nullptr;
            }
        };
    private:
        int content;
        AST_op op_;
        AST* left_;
        AST* right_;
};



std::unique_ptr<Formula> AST_to_Proposotion(AST* ast) {
    
    if (ast->is_leaf()) {
        
        auto res = std::unique_ptr<Formula>(new Prop(ast->get_content()));
        return std::move(res);
    
    } else {
        switch (ast->get_op())
        {
        case AST_op::neg :{

            auto phi_ptr = AST_to_Proposotion(ast->get_left());
            
            auto res = std::unique_ptr<Formula>(new Negation(phi_ptr.get()));
            phi_ptr.release();
            return std::move(res);
        
        }
        case AST_op::lor : {

            auto l = AST_to_Proposotion(ast->get_left());
            auto r = AST_to_Proposotion(ast->get_right());
            
            auto res = std::unique_ptr<Formula>(new Binary(l.get(),r.get(),Connective::vee));
            l.release();
            r.release();
            return std::move(res);
        }
        case AST_op::land : {
            
            auto l = AST_to_Proposotion(ast->get_left());
            auto r = AST_to_Proposotion(ast->get_right());
            
            auto res = std::unique_ptr<Formula>(new Binary(l.get(),r.get(),Connective::wedge));
            l.release();
            r.release();
            return std::move(res);
        }
        default:
            throw new std::runtime_error("Non-exhaustive pattern matching");
        }
    }
}

template <char Ch>
bool is_same_char(char c) { return c == Ch; }


template <char Ch>
inline constexpr auto match = pc::one[pc::filter(is_same_char<Ch>)];

AST* negate(char ch, AST* phi) {
    auto psi = new AST(AST_op::neg,phi,nullptr);
    return psi;
}

AST* do_op(AST* l, char ch, AST* r) {
    switch (ch) {
    case '&': {
        auto phi = new AST(AST_op::land,l,r);
        return phi;
    }
    case '|': {
        auto phi = new AST(AST_op::lor,l,r);
        return phi;
    }
    }
}

AST* to_Leaf(std::vector<char> const& chs) {
    
    int n = 0;
    for (auto c : chs) n = n * 10 + (c - '0');
    
    auto res = new AST(n);
    return res;
}

cppcmb_decl(expr, AST*);
cppcmb_decl(connective, AST*);
cppcmb_decl(negation, AST*);
cppcmb_decl(atom, AST*);
cppcmb_decl(prop, AST*);
cppcmb_decl(digit, char);

cppcmb_def(expr) = pc::pass
    // | (match<'~'> & connective) [negate]
    | (expr & match<'|'> & connective) [do_op]
    | connective
    %= pc::as_memo_d;

cppcmb_def(connective) = pc::pass
    | (connective & match<'&'> & negation) [do_op]
    | negation
    %= pc::as_memo_d;

cppcmb_def(negation) = pc::pass
    | (match<'~'> & negation) [negate]
    | atom
    %= pc::as_memo_d;


cppcmb_def(atom) = pc::pass
    | (match<'('> & expr & match<')'>) [pc::select<1>]
    | prop
    %= pc::as_memo_d;

cppcmb_def(prop) =
      (+digit) [to_Leaf]
    ;

cppcmb_def(digit) = pc::one[pc::filter(isdigit)];

std::string remove_spaces(std::string s) {
    std::string res;
    for (auto ch : s) {
        if(!isspace(ch)){
            res.push_back(ch);
        }
    }
    return res;
}

std::unique_ptr<Formula> Proposition(std::string s) {
    
    std::string line = remove_spaces(s);
    
    auto parser = pc::parser(expr);
    auto res = parser.parse(line);

    if (res.is_success()) {
            auto value = res.success().value();
            auto formula = AST_to_Proposotion(value);
            delete(value);
            if(!formula.get()) {
                throw new std::runtime_error("AST to Proposition failed");
            } else {
                return formula;
            }
            
    }
        else {
            std::cout << "Failed to parse expression!" << std::endl;
            throw new std::runtime_error("Failed to parse");
    }

}
