#ifndef PROP_PARSER_H
#define PROP_PARSER_H
#include "formula.h"
#include <memory>

std::unique_ptr<Formula> Proposition(std::string s);

#endif 