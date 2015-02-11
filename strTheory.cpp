//TODO:
// ----------------------------------------------------------

#include "strTheory.h"

FILE * logFile = NULL;
int sLevel = 0;
int searchStart = 0;
int tmpStringVarCount = 0;
int tmpIntVarCount = 0;
int tmpXorVarCount = 0;
int tmpBoolVarCount = 0;
int tmpConcatCount = 0;
int tmpUnrollVarCount = 0;

std::map<std::string, Z3_ast> constStr_astNode_map;
std::map<Z3_ast, Z3_ast> length_astNode_map;

std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> containPairBoolMap;
std::map<Z3_ast, std::set<std::pair<Z3_ast, Z3_ast> > > containPairIdxMap;

std::map<Z3_ast, int> basicStrVarAxiom_added;

std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> concat_astNode_map;

std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> contains_astNode_map;
std::map<std::pair<Z3_ast, Z3_ast>, std::map<int, Z3_ast> > varForBreakConcat;

//----------------------------------------------------------------

std::map<Z3_ast, int> inputVarMap;

//----------------------------------------------------------------

std::map<Z3_ast, unsigned int> fvarLenCountMap;
std::map<Z3_ast, std::vector<Z3_ast> > fvarLenTesterMap;
std::map<Z3_ast, Z3_ast> lenTesterFvarMap;

std::map<Z3_ast, std::map<int, std::vector<std::pair<int, Z3_ast> > > > fvarValueTesterMap;
std::map<Z3_ast, std::vector<int> > valRangeMap;
std::map<Z3_ast, Z3_ast> valueTesterFvarMap;
//----------------------------------------------------------------

char * charSet = NULL;
std::map<char, int> charSetLookupTable;
int charSetSize = 0;
Z3_ast emptyConstStr;

const std::string escapeDict[] = { "\\x00", "\\x01", "\\x02", "\\x03", "\\x04", "\\x05", "\\x06", "\\x07", "\\x08", "\\t", "\\n", "\\x0b", "\\x0c",
    "\\r", "\\x0e", "\\x0f", "\\x10", "\\x11", "\\x12", "\\x13", "\\x14", "\\x15", "\\x16", "\\x17", "\\x18", "\\x19", "\\x1a", "\\x1b", "\\x1c",
    "\\x1d", "\\x1e", "\\x1f", " ", "!", "\\\"", "#", "$", "%", "&", "'", "(", ")", "*", "+", ",", "-", ".", "/", "0", "1", "2", "3", "4", "5", "6",
    "7", "8", "9", ":", ";", "<", "=", ">", "?", "@", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S",
    "T", "U", "V", "W", "X", "Y", "Z", "[", "\\\\", "]", "^", "_", "`", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o",
    "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z", "{", "|", "}", "~", "\\x7f", "\\x80", "\\x81", "\\x82", "\\x83", "\\x84", "\\x85", "\\x86",
    "\\x87", "\\x88", "\\x89", "\\x8a", "\\x8b", "\\x8c", "\\x8d", "\\x8e", "\\x8f", "\\x90", "\\x91", "\\x92", "\\x93", "\\x94", "\\x95", "\\x96",
    "\\x97", "\\x98", "\\x99", "\\x9a", "\\x9b", "\\x9c", "\\x9d", "\\x9e", "\\x9f", "\\xa0", "\\xa1", "\\xa2", "\\xa3", "\\xa4", "\\xa5", "\\xa6",
    "\\xa7", "\\xa8", "\\xa9", "\\xaa", "\\xab", "\\xac", "\\xad", "\\xae", "\\xaf", "\\xb0", "\\xb1", "\\xb2", "\\xb3", "\\xb4", "\\xb5", "\\xb6",
    "\\xb7", "\\xb8", "\\xb9", "\\xba", "\\xbb", "\\xbc", "\\xbd", "\\xbe", "\\xbf", "\\xc0", "\\xc1", "\\xc2", "\\xc3", "\\xc4", "\\xc5", "\\xc6",
    "\\xc7", "\\xc8", "\\xc9", "\\xca", "\\xcb", "\\xcc", "\\xcd", "\\xce", "\\xcf", "\\xd0", "\\xd1", "\\xd2", "\\xd3", "\\xd4", "\\xd5", "\\xd6",
    "\\xd7", "\\xd8", "\\xd9", "\\xda", "\\xdb", "\\xdc", "\\xdd", "\\xde", "\\xdf", "\\xe0", "\\xe1", "\\xe2", "\\xe3", "\\xe4", "\\xe5", "\\xe6",
    "\\xe7", "\\xe8", "\\xe9", "\\xea", "\\xeb", "\\xec", "\\xed", "\\xee", "\\xef", "\\xf0", "\\xf1", "\\xf2", "\\xf3", "\\xf4", "\\xf5", "\\xf6",
    "\\xf7", "\\xf8", "\\xf9", "\\xfa", "\\xfb", "\\xfc", "\\xfd", "\\xfe", "\\xff" };

//----------------------------------------------------------------
/*
 *
 */
bool isConcatFunc(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->Concat)
    return true;
  else
    return false;
}

/*
 *
 */
inline bool isLengthFunc(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->Length)
    return true;
  else
    return false;
}

/*
 *
 */
bool isUnrollFunc(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->Unroll)
    return true;
  else
    return false;
}

/*
 *
 */
bool isRegexStar(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->RegexStar)
    return true;
  else
    return false;
}

/*
 *
 */
bool isStr2Regex(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->Str2Reg)
    return true;
  else
    return false;
}


/*
 *
 */
bool isRegexUnion(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->RegexUnion)
    return true;
  else
    return false;
}

/*
 *
 */
bool isRegexConcat(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  if (d == td->RegexConcat)
    return true;
  else
    return false;
}

/*
 *
 */
inline Z3_ast getAliasIndexAst(std::map<Z3_ast, Z3_ast> & aliasIndexMap, Z3_ast node) {
  if (aliasIndexMap.find(node) != aliasIndexMap.end())
    return aliasIndexMap[node];
  else
    return node;
}

/*
 *
 */
std::string intToString(int i) {
  std::stringstream ss;
  ss << i;
  return ss.str();
}

/*
 *
 */
inline std::string longLongToString(long long i) {
  std::stringstream ss;
  ss << i;
  return ss.str();
}

/*
 *
 */
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty) {
  Z3_symbol s = Z3_mk_string_symbol(ctx, name);
  return Z3_mk_const(ctx, s, ty);
}

/*
 *
 */
Z3_ast mk_bool_var(Z3_context ctx, const char * name) {
  Z3_sort ty = Z3_mk_bool_sort(ctx);
  return mk_var(ctx, name, ty);
}

/*
 *
 */
Z3_ast mk_int_var(Z3_context ctx, const char * name) {
  Z3_sort ty = Z3_mk_int_sort(ctx);
  return mk_var(ctx, name, ty);
}

/*
 *
 */
Z3_ast mk_int(Z3_context ctx, int v) {
  Z3_sort ty = Z3_mk_int_sort(ctx);
  return Z3_mk_int(ctx, v, ty);
}

/*
 *
 */
Z3_ast my_mk_str_value(Z3_theory t, char const * str) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);

  // if the empty string is not created, create one
  if (constStr_astNode_map.find("") == constStr_astNode_map.end()) {
    Z3_symbol empty_str_sym = Z3_mk_string_symbol(ctx, "\"\"");
    Z3_ast emptyStrNode = Z3_theory_mk_value(ctx, t, empty_str_sym, td->String);
    constStr_astNode_map[""] = emptyStrNode;
  }

  std::string keyStr = std::string(str);
  // if the str is not created, create one
  if (constStr_astNode_map.find(keyStr) == constStr_astNode_map.end()) {
    Z3_symbol str_sym = Z3_mk_string_symbol(ctx, str);
    Z3_ast strNode = Z3_theory_mk_value(ctx, t, str_sym, td->String);
    constStr_astNode_map[keyStr] = strNode;
  }
  return constStr_astNode_map[keyStr];
}

/*
 *
 */
Z3_ast my_mk_str_var(Z3_theory t, char const * name) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
  Z3_ast varAst = mk_var(ctx, name, td->String);
  basicStrVarAxiom(t, varAst, __LINE__);
  return varAst;
}

/*
 *
 */
Z3_ast my_mk_internal_string_var(Z3_theory t) {
  std::stringstream ss;
  ss << tmpStringVarCount;
  tmpStringVarCount++;
  std::string name = "$$_str" + ss.str();
  return my_mk_str_var(t, name.c_str());
}

Z3_ast my_mk_nonEmpty_string_var(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
  std::stringstream ss;
  ss << tmpStringVarCount;
  tmpStringVarCount++;
  std::string name = "$$_str" + ss.str();
  Z3_ast varAst = mk_var(ctx, name.c_str(), td->String);
  nonEmptyStrVarAxiom(t, varAst, __LINE__);
  return varAst;
}

/*
 * Make an integer variable used for intermediated representation
 */
Z3_ast my_mk_internal_int_var(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << tmpIntVarCount;
  tmpIntVarCount++;
  std::string name = "$$_int_" + ss.str();
  return mk_int_var(ctx, name.c_str());
}

Z3_ast my_mk_internal_bool_var(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << tmpBoolVarCount;
  tmpBoolVarCount++;
  std::string name = "$$_bol" + ss.str();
  return mk_bool_var(ctx, name.c_str());
}

/*
 *
 */
Z3_ast mk_internal_xor_var(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << tmpXorVarCount;
  tmpXorVarCount++;
  std::string name = "$$_xor_" + ss.str();
  return mk_int_var(ctx, name.c_str());
}

/*
 *
 */
Z3_ast mk_unrollBoundVar(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << tmpUnrollVarCount;
  tmpUnrollVarCount++;
  std::string name = "$$_unr_" + ss.str();
  return mk_int_var(ctx, name.c_str());
}

/* ---------------------------------
 * Return the node type in Enum
 * ---------------------------------
 */
T_myZ3Type getNodeType(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_ast_kind z3Kind = Z3_get_ast_kind(ctx, n);

  switch (z3Kind) {
    case Z3_NUMERAL_AST: {
      return my_Z3_Num;
      break;
    }

    case Z3_APP_AST: {
      Z3_sort s = Z3_get_sort(ctx, n);
      if (Z3_theory_is_value(t, n)) {
        Z3_sort_kind sk = Z3_get_sort_kind(ctx, s);
        Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
        if (sk == Z3_BOOL_SORT) {
          if (d == td->Contains || d == td->StartsWith || d == td->EndsWith || d == td->RegexIn) {
            return my_Z3_Func;
          } else {
            return my_Z3_ConstBool;
          }
        } else if (sk == Z3_INT_SORT) {
          if (d == td->Length || d == td->Indexof || d == td->Indexof2 || d == td->LastIndexof) {
            return my_Z3_Func;
          }
        } else if (sk == Z3_UNKNOWN_SORT) {
          if (s == td->String) {
            if (d == td->Concat || d == td->SubString || d == td->Replace || d == td->Unroll || d == td->CharAt) {
              return my_Z3_Func;
            } else {
              return my_Z3_ConstStr;
            }
          }
          if (s == td->Regex) {
            if (d == td->RegexConcat
                || d == td->RegexStar
                || d == td->RegexUnion
                || d == td->Str2Reg

                || d == td->RegexDigit
                || d == td->RegexAlpha
                || d == td->RegexAlnum
                || d == td->RegexLower
                || d == td->RegexUpper
                || d == td->RegexWord
               )
              return my_Z3_Func;
            else
              return my_Z3_Regex_Var;
          }
        }
      } else {
        //Z3 native functions fall into this category
        Z3_sort s = Z3_get_sort(ctx, n);
        if (s == td->String) {
          return my_Z3_Str_Var;
        } else if (s == td->Regex) {
          return my_Z3_Regex_Var;
        } else if (s == Z3_mk_int_sort(ctx)) {
          return my_Z3_Int_Var;
        } else {
          return my_Z3_Func;
        }
      }
      break;
    }
    case Z3_VAR_AST: {
      return my_Z3_Var;
      break;
    }
    default: {
      break;
    }
  }
  return my_Z3_Unknown;
}

/*
 *
 */
bool isConstStr(Z3_theory t, Z3_ast node) {
  if (node == NULL)
    return false;
  if (getNodeType(t, node) == my_Z3_ConstStr) {
    return true;
  } else {
    return false;
  }
}

bool isStrVar(Z3_theory t, Z3_ast node) {
  if (node == NULL)
    return false;

  if (getNodeType(t, node) == my_Z3_Str_Var) {
    return true;
  } else {
    return false;
  }
}

inline bool isStringSort(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_sort s = Z3_get_sort(ctx, n);
  if (s == td->String)
    return true;
  else
    return false;
}

inline bool isRegexSort(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_sort s = Z3_get_sort(ctx, n);
  if (s == td->String)
    return true;
  else
    return false;
}

/*
 *
 */
Z3_ast mk_1_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) {
  Z3_ast args[1] = { x };
  return Z3_mk_app(ctx, f, 1, args);
}

/*
 *
 */
Z3_ast mk_2_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) {
  Z3_ast args[2] = { x, y };
  return Z3_mk_app(ctx, f, 2, args);
}

/*
 *
 */
Z3_ast my_mk_and(Z3_theory t, Z3_ast * item, int count) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (count == 0)
    return Z3_mk_true(ctx);
  else if (count == 1)
    return item[0];
  else
    return Z3_mk_and(ctx, count, item);
}

/*
 *
 */
Z3_ast mk_2_and(Z3_theory t, Z3_ast and1, Z3_ast and2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast and_items[2] = { and1, and2 };
  return Z3_mk_and(ctx, 2, and_items);
}

/*
 *
 */
Z3_ast mk_2_or(Z3_theory t, Z3_ast and1, Z3_ast and2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast and_items[2] = { and1, and2 };
  return Z3_mk_or(ctx, 2, and_items);
}

/*
 *
 */
Z3_ast mk_2_sub(Z3_theory t, Z3_ast ast1, Z3_ast ast2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ast_items[2] = { ast1, ast2 };
  return Z3_mk_sub(ctx, 2, ast_items);
}

/*
 *
 */
Z3_ast mk_2_add(Z3_theory t, Z3_ast ast1, Z3_ast ast2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ast_items[2] = { ast1, ast2 };
  return Z3_mk_add(ctx, 2, ast_items);
}

/*
 *
 */
Z3_ast mk_and_fromVector(Z3_theory t, std::vector<Z3_ast> & vec) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (vec.size() == 0) {
    return NULL;
  } else if (vec.size() == 1) {
    return vec[0];
  } else {
    Z3_ast * items = new Z3_ast[vec.size()];
    for (unsigned int i = 0; i < vec.size(); i++)
      items[i] = vec[i];
    Z3_ast toAssert = Z3_mk_and(ctx, vec.size(), items);
    delete[] items;
    return toAssert;
  }
}


Z3_ast mk_and_fromSet(Z3_theory t, const std::set<Z3_ast> & fSet) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (fSet.size() == 0) {
    return NULL;
  } else if (fSet.size() == 1) {
    return (*fSet.begin());
  } else {
    Z3_ast * items = new Z3_ast[fSet.size()];
    int i = 0;
    std::set<Z3_ast>::const_iterator itor = fSet.begin();
    for (; itor != fSet.end(); itor++) {
      items[i++] = *itor;
    }
    Z3_ast toAssert = Z3_mk_and(ctx, fSet.size(), items);
    delete[] items;
    return toAssert;
  }
}

/*
 *
 */
Z3_ast mk_or_fromVector(Z3_theory t, std::vector<Z3_ast> & vec) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (vec.size() == 0) {
    return NULL;
  } else if (vec.size() == 1) {
    return vec[0];
  } else {
    Z3_ast * items = new Z3_ast[vec.size()];
    for (unsigned int i = 0; i < vec.size(); i++)
      items[i] = vec[i];
    Z3_ast toAssert = Z3_mk_or(ctx, vec.size(), items);
    delete[] items;
    return toAssert;
  }
}


Z3_ast mk_or_fromSet(Z3_theory t, const std::set<Z3_ast> & fSet) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (fSet.size() == 0) {
    return NULL;
  } else if (fSet.size() == 1) {
    return (*fSet.begin());
  } else {
    Z3_ast * items = new Z3_ast[fSet.size()];
    int i = 0;
    std::set<Z3_ast>::const_iterator itor = fSet.begin();
    for (; itor != fSet.end(); itor++) {
      items[i++] = *itor;
    }
    Z3_ast toAssert = Z3_mk_or(ctx, fSet.size(), items);
    delete[] items;
    return toAssert;
  }
}

/*
 *
 */
Z3_ast mk_length(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  if (length_astNode_map.find(n) == length_astNode_map.end()) {
    if (isConstStr(t, n)) {
      length_astNode_map[n] = mk_int(ctx, getConstStrValue(t, n).length());
    } else {
      length_astNode_map[n] = mk_1_arg_app(ctx, td->Length, n);
    }
  }
  return length_astNode_map[n];
}

/*
 *
 */
Z3_ast mk_unroll(Z3_theory t, Z3_ast n, Z3_ast bound) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

  Z3_ast unrollFunc = NULL;
  unrollFunc = mk_2_arg_app(ctx, td->Unroll, n, bound);

  std::vector<Z3_ast> items;
  items.push_back(Z3_mk_eq(ctx, Z3_mk_eq(ctx, bound, mk_int(ctx, 0)), Z3_mk_eq(ctx, unrollFunc, my_mk_str_value(t, ""))));
  items.push_back(Z3_mk_ge(ctx, bound, mk_int(ctx, 0)));
  items.push_back(Z3_mk_ge(ctx, mk_length(t, unrollFunc), mk_int(ctx, 0)));
  addAxiom(t, mk_and_fromVector(t, items), __LINE__, false);

  return unrollFunc;
}

/*
 *
 */
Z3_ast mk_contains(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  std::pair<Z3_ast, Z3_ast> containsKey(n1, n2);
  if (contains_astNode_map.find(containsKey) == contains_astNode_map.end()) {
    if (isConstStr(t, n1) && isConstStr(t, n2)) {
      std::string n1Str = getConstStrValue(t, n1);
      std::string n2Str = getConstStrValue(t, n2);
      if (n1Str.find(n2Str) != std::string::npos)
        contains_astNode_map[containsKey] = Z3_mk_true(ctx);
      else
        contains_astNode_map[containsKey] = Z3_mk_false(ctx);
    } else {
      contains_astNode_map[containsKey] = mk_2_arg_app(ctx, td->Contains, n1, n2);
    }
  }
  return contains_astNode_map[containsKey];
}

/*
 *
 */
Z3_ast mk_concat(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  if (n1 == NULL || n2 == NULL) {
    fprintf(stdout, "> Error: the strings to be concat cannot be NULL (@ %d).\n", __LINE__);
    exit(0);
  } else {
    bool n1HasEqcValue = false;
    bool n2HasEqcValue = false;
    n1 = get_eqc_value(t, n1, n1HasEqcValue);
    n2 = get_eqc_value(t, n2, n2HasEqcValue);

    if (n1HasEqcValue && n2HasEqcValue) {
      return Concat(t, n1, n2);
    } else if (n1HasEqcValue && !n2HasEqcValue) {
      bool n2_isConcatFunc = isConcatFunc(t, n2);
      if (getConstStrValue(t, n1) == "") {
        return n2;
      }
      if (n2_isConcatFunc) {
        Z3_ast n2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 0);
        Z3_ast n2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 1);
        if (isConstStr(t, n2_arg0)) {
          n1 = Concat(t, n1, n2_arg0); // n1 will be a constant
          n2 = n2_arg1;
        }
      }
    } else if (!n1HasEqcValue && n2HasEqcValue) {
      if (getConstStrValue(t, n2) == "") {
        return n1;
      }

      if (isConcatFunc(t, n1)) {
        Z3_ast n1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 0);
        Z3_ast n1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 1);
        if (isConstStr(t, n1_arg1)) {
          n1 = n1_arg0;
          n2 = Concat(t, n1_arg1, n2); // n2 will be a constant
        }
      }
    } else {
      if (isConcatFunc(t, n1) && isConcatFunc(t, n2)) {
        Z3_ast n1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 0);
        Z3_ast n1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n1), 1);
        Z3_ast n2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 0);
        Z3_ast n2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n2), 1);
        if (isConstStr(t, n1_arg1) && isConstStr(t, n2_arg0)) {
          Z3_ast tmpN1 = n1_arg0;
          Z3_ast tmpN2 = Concat(t, n1_arg1, n2_arg0);
          n1 = mk_concat(t, tmpN1, tmpN2);
          n2 = n2_arg1;
        }
      }
    }

    //------------------------------------------------------
    // * Z3_ast ast1 = mk_2_arg_app(ctx, td->Concat, n1, n2);
    // * Z3_ast ast2 = mk_2_arg_app(ctx, td->Concat, n1, n2);
    // Z3 treats (ast1) and (ast2) as two different nodes.
    //-------------------------------------------------------
    std::pair<Z3_ast, Z3_ast> concatArgs(n1, n2);
    Z3_ast concatAst = NULL;
    if (concat_astNode_map.find(concatArgs) == concat_astNode_map.end()) {
      concatAst = mk_2_arg_app(ctx, td->Concat, n1, n2);
      concat_astNode_map[concatArgs] = concatAst;

      Z3_ast concat_length = mk_length(t, concatAst);

      std::vector<Z3_ast> childrenVector;
      getNodesInConcat(t, concatAst, childrenVector);
      Z3_ast * items = new Z3_ast[childrenVector.size()];
      for (unsigned int i = 0; i < childrenVector.size(); i++) {
        items[i] = mk_length(t, childrenVector[i]);
      }
      Z3_ast lenAssert = Z3_mk_eq(ctx, concat_length, Z3_mk_add(ctx, childrenVector.size(), items));
      addAxiom(t, lenAssert, __LINE__, false);
      delete[] items;

    } else {
      concatAst = concat_astNode_map[concatArgs];
    }
    return concatAst;
  }
}

/*
 *
 */
Z3_ast getLengthAST(Z3_theory t, Z3_ast n) {
  return mk_length(t, n);
}

/*
 * Query the integer theory.
 *   - If n has length value in integer theory, return the value.
 *   - Else, return -1.
 */
int getLenValue(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast lenAst = getLengthAST(t, n);
  Z3_ast lenValueAst = Z3_theory_get_value_of_len(t, lenAst);
  if (lenValueAst == NULL) {
    return -1;
  }
  if (getNodeType(t, n) == my_Z3_ConstStr || lenAst != lenValueAst) {
    char * str = (char *) Z3_ast_to_string(ctx, lenValueAst);
    int len = atoi(str);
    if (len < 0) {
      __debugPrint(logFile, "\n\n\n\n\n!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      __debugPrint(logFile, "ERROR: length of ");
      printZ3Node(t, n)
      __debugPrint(logFile, " < 0\n");
      exit(0);
    }
    return len;
  }
  return -1;
}

int getIntValue(Z3_theory t, Z3_ast n, bool & hasValue) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast valueAst = Z3_theory_get_value_of_len(t, n);
  hasValue = false;
  if (valueAst == NULL) {
    return -1;
  }
  if (n != valueAst) {
    char * str = (char *) Z3_ast_to_string(ctx, valueAst);
    int val = atoi(str);
    hasValue = true;
    return val;
  }
  return -1;
}

/*
 *
 */
void addAxiom(Z3_theory t, Z3_ast toAssert, int line, bool display) {
#ifdef DEBUGLOG
  if (display) {
    if (searchStart == 1) {
      __debugPrint(logFile, "---------------------\nAxiom Add(@%d, Level %d):\n", line, sLevel);
      printZ3Node(t, toAssert);
      __debugPrint(logFile, "\n---------------------\n\n");
    } else {
      __debugPrint(logFile, "---------------------\nAssertion Add(@%d, Level %d):\n", line, sLevel);
      printZ3Node(t, toAssert);
      __debugPrint(logFile, "\n---------------------\n\n");
    }
  }
#endif

  if (toAssert == NULL) {
    return;
  }

  if (searchStart == 1) {
    Z3_theory_assert_axiom(t, toAssert);
  } else {
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_assert_cnstr(ctx, toAssert);
  }
}

/*
 *
 */
void print_eq_class(Z3_theory t, Z3_ast n) {
#ifdef DEBUGLOG
  __debugPrint(logFile, " EQC={ ");
  Z3_ast curr = n;
  int count = 0;
  do {
    if (count != 0) {
      __debugPrint(logFile, ", ");
    }
    printZ3Node(t, curr);
    curr = Z3_theory_get_eqc_next(t, curr);
    count++;
  }while (curr != n);
  __debugPrint(logFile, " }");
#endif
}

/*
 *
 */
void __printZ3Node(Z3_theory t, Z3_ast node) {
#ifdef DEBUGLOG
  Z3_context ctx = Z3_theory_get_context(t);
  if (node == NULL) {
    __debugPrint(logFile, "NULL");
    return;
  }

  T_myZ3Type nodeType = getNodeType(t, node);
  switch (nodeType) {
    case my_Z3_ConstStr: {
      std::string str = getConstStrValue(t, node);
      __debugPrint(logFile, "\"%s\"", str.c_str());
      break;
    }
    case my_Z3_Func: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    case my_Z3_Num: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    case my_Z3_Var: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    case my_Z3_Str_Var: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    case my_Z3_Quantifier: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    case my_Z3_Unknown: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
    default: {
      __debugPrint(logFile, "%s", Z3_ast_to_string(ctx, node));
      break;
    }
  }
#endif
}

/*
 * Look for the equivalent constant for a node "n"
 * Iterate the equivalence class
 * If there is a constant,
 *    return the constant
 * Otherwise,
 *    return n
 */
Z3_ast get_eqc_value(Z3_theory t, Z3_ast n, bool & hasEqcValue) {
  Z3_ast curr = n;
  do {
    if (Z3_theory_is_value(t, curr)) {
      if (isConstStr(t, curr)) {
        hasEqcValue = true;
        return curr;
      }
    }
    curr = Z3_theory_get_eqc_next(t, curr);
  } while (curr != n);
  hasEqcValue = false;
  return n;
}

/*
 *
 */
std::string getConstStrValue(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::string strValue;
  if (isConstStr(t, n)) {
    char * str = (char *) Z3_ast_to_string(ctx, n);
    if (strcmp(str, "\"\"") == 0)
      strValue = std::string("");
    else
      strValue = std::string(str);
  } else {
    strValue == std::string("__NotConstStr__");
  }
  return strValue;
}

/*
 *
 */
int getConstIntValue(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, n) == my_Z3_Num) {
    char * str = (char *) Z3_ast_to_string(ctx, n);
    int val = atoi(str);
    return val;
  } else {
    fprintf(stdout, "> Error: converting a non integer string to int @ %d. Exit.\n", __LINE__);
    fflush(stdout);
    exit(0);
  }
  return -1;
}

/*
 *
 */
Z3_ast registerContain(Z3_theory t, Z3_ast str, Z3_ast subStr) {

#ifdef DEBUGLOG
  __debugPrint(logFile, ">> [containRegister] Contains(");
  printZ3Node(t, str);
  __debugPrint(logFile, ", ");
  printZ3Node(t, subStr);
#endif

  std::pair<Z3_ast, Z3_ast> key = std::make_pair(str, subStr);
  if (containPairBoolMap.find(key) == containPairBoolMap.end()) {
    containPairBoolMap[key] = my_mk_internal_bool_var(t);
    containPairIdxMap[str].insert(key);
    containPairIdxMap[subStr].insert(key);
  }

#ifdef DEBUGLOG
    __debugPrint(logFile, ") = ");
    printZ3Node(t, containPairBoolMap[key]);
    __debugPrint(logFile, "\n");
#endif

    return containPairBoolMap[key];
}

/*
 *
 */
Z3_ast Concat(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  bool n1HasEqcValue = false;
  bool n2HasEqcValue = false;
  Z3_ast v1 = get_eqc_value(t, n1, n1HasEqcValue);
  Z3_ast v2 = get_eqc_value(t, n2, n2HasEqcValue);
  if (n1HasEqcValue && n2HasEqcValue) {
    std::string n1_str = getConstStrValue(t, v1);
    std::string n2_str = getConstStrValue(t, v2);
    std::string result = n1_str + n2_str;
    return my_mk_str_value(t, result.c_str());
  } else if (n1HasEqcValue && !n2HasEqcValue) {
    if (getConstStrValue(t, v1) == "") {
      return n2;
    }
  } else if (!n1HasEqcValue && n2HasEqcValue) {
    if (getConstStrValue(t, v2) == "") {
      return n1;
    }
  }
  return NULL;
}

/*
 * The inputs:
 *    ~ nn: non const node
 *    ~ eq_str: the equivalent constant string of nn
 *  Iterate the parent of all eqc nodes of nn, looking for:
 *    ~ concat node
 *  to see whether some concat nodes can be simplified.
 */

void simplifyParent(Z3_theory t, Z3_ast nn, Z3_ast eq_str) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast n_eqNode = nn;
  std::string eq_strValue = getConstStrValue(t, eq_str);
  do {
    unsigned num_parents = Z3_theory_get_num_parents(t, n_eqNode);
    for (unsigned i = 0; i < num_parents; i++) {
      Z3_ast parent = Z3_theory_get_parent(t, n_eqNode, i);

      if (isConcatFunc(t, parent)) {
        Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, parent), 0);
        Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, parent), 1);

        // length part
        int parentLen = getLenValue(t, parent);

        if (arg0 == n_eqNode) {
          int arg0Len = getLenValue(t, eq_str);
          int arg1Len = getLenValue(t, arg1);

#ifdef DEBUGLOG
          __debugPrint(logFile, ">> [simplifyParent 1]\n");
          __debugPrint(logFile, "   * parent = ");
          printZ3Node(t, parent);
          __debugPrint(logFile, "\n");
          __debugPrint(logFile, "   * | parent | = %d\n", parentLen);
          __debugPrint(logFile, "     * | arg0 | = %d\n", arg0Len);
          __debugPrint(logFile, "     * | arg1 | = %d\n", arg1Len);
          __debugPrint(logFile, "\n\n");
#endif

          if (parentLen != -1 && arg1Len == -1) {
            Z3_ast implyL11 = mk_2_and(t, Z3_mk_eq(ctx, mk_length(t, parent), mk_int(ctx, parentLen)),
                Z3_mk_eq(ctx, mk_length(t, arg0), mk_int(ctx, arg0Len)));
            int makeUpLenArg1 = parentLen - arg0Len;
            Z3_ast lenAss = NULL;
            if (makeUpLenArg1 >= 0) {
              Z3_ast implyR11 = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, makeUpLenArg1));
              lenAss = Z3_mk_implies(ctx, implyL11, implyR11);
            } else {
              lenAss = Z3_mk_not(ctx, implyL11);
            }
            addAxiom(t, lenAss, __LINE__);
          }

          // (Concat n_eqNode arg1) /\ arg1 has eq const
//          int arg0Eqarg1 = 0;
//          if (inSameEqc(t, arg0, arg1)) {
//            arg0Eqarg1 = 1;
//          }
//          Z3_ast concatResult = NULL;
//          if (arg0Eqarg1 == 1) {
//            concatResult = Concat(t, eq_str, eq_str);
//          } else {
//            concatResult = Concat(t, eq_str, arg1);
//          }
////          Z3_ast concatResult = Concat(t, eq_str, arg1);
//          if (concatResult != NULL) {
//            Z3_ast arg1Value = NULL;
//            if (arg0Eqarg1 == 1) {
//              arg1Value = eq_str;
//            } else {
//              bool arg1HasEqcValue = false;
//              arg1Value = get_eqc_value(t, arg1, arg1HasEqcValue);
//            }
////            bool arg1HasEqcValue = false;
////            Z3_ast arg1Value = get_eqc_value(t, arg1, arg1HasEqcValue);

          Z3_ast concatResult = Concat(t, eq_str, arg1);
          if (concatResult != NULL) {
            bool arg1HasEqcValue = false;
            Z3_ast arg1Value = get_eqc_value(t, arg1, arg1HasEqcValue);
            Z3_ast implyL = NULL;
            if (arg1 != arg1Value) {
              Z3_ast eq_ast1 = Z3_mk_eq(ctx, n_eqNode, eq_str);
              Z3_ast eq_ast2 = Z3_mk_eq(ctx, arg1, arg1Value);
              implyL = mk_2_and(t, eq_ast1, eq_ast2);
            } else {
              implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
            }

            if (!inSameEqc(t, parent, concatResult)) {
              Z3_ast implyR = Z3_mk_eq(ctx, parent, concatResult);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          } else if (isConcatFunc(t, n_eqNode)) {
            Z3_ast simpleConcat = mk_concat(t, eq_str, arg1);
            if (!inSameEqc(t, parent, simpleConcat)) {
              Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
              Z3_ast implyR = Z3_mk_eq(ctx, parent, simpleConcat);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          }
        }

        if (arg1 == n_eqNode) {
          int arg0Len = getLenValue(t, arg0);
          int arg1Len = getLenValue(t, eq_str);

#ifdef DEBUGLOG
          __debugPrint(logFile, ">> [simplifyParent 2]\n");
          __debugPrint(logFile, "   * parent = ");
          printZ3Node(t, parent);
          __debugPrint(logFile, "\n");
          __debugPrint(logFile, "   * | parent | = %d\n", parentLen);
          __debugPrint(logFile, "     * | arg0 | = %d\n", arg0Len);
          __debugPrint(logFile, "     * | arg1 | = %d\n", arg1Len);
          __debugPrint(logFile, "\n\n");
#endif

          if (parentLen != -1 && arg0Len == -1) {
            Z3_ast implyL11 = mk_2_and(t, Z3_mk_eq(ctx, mk_length(t, parent), mk_int(ctx, parentLen)),
                Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, arg1Len)));
            int makeUpLenArg0 = parentLen - arg1Len;
            Z3_ast lenAss = NULL;
            if (makeUpLenArg0 >= 0) {
              Z3_ast implyR11 = Z3_mk_eq(ctx, mk_length(t, arg0), mk_int(ctx, makeUpLenArg0));
              lenAss = Z3_mk_implies(ctx, implyL11, implyR11);
            } else {
              lenAss = Z3_mk_not(ctx, implyL11);
            }
            addAxiom(t, lenAss, __LINE__);
          }

          // (Concat arg0 n_eqNode) /\ arg0 has eq const
//          int arg0Eqarg1 = 0;
//          if (inSameEqc(t, arg0, arg1)) {
//            arg0Eqarg1 = 1;
//          }
//          Z3_ast concatResult = NULL;
//          if (arg0Eqarg1 == 1) {
//            concatResult = Concat(t, eq_str, eq_str);
//          } else {
//            concatResult = Concat(t, arg0, eq_str);
//          }
//
//          if (concatResult != NULL) {
//            Z3_ast arg0Value = NULL;
//            if (arg0Eqarg1 == 1) {
//              arg0Value = eq_str;
//            } else {
//              bool arg0HasEqcValue = false;
//              arg0Value = get_eqc_value(t, arg0, arg0HasEqcValue);
//            }

          Z3_ast concatResult = Concat(t, arg0, eq_str);
          if (concatResult != NULL) {
            bool arg0HasEqcValue = false;
            Z3_ast arg0Value = get_eqc_value(t, arg0, arg0HasEqcValue);
            Z3_ast implyL = NULL;
            if (arg0Value != arg0) {
              Z3_ast eq_ast1 = Z3_mk_eq(ctx, arg0, arg0Value);
              Z3_ast eq_ast2 = Z3_mk_eq(ctx, n_eqNode, eq_str);
              implyL = mk_2_and(t, eq_ast1, eq_ast2);
            } else {
              implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
            }

            if (!inSameEqc(t, parent, concatResult)) {
              Z3_ast implyR = Z3_mk_eq(ctx, parent, concatResult);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          }

          else if (isConcatFunc(t, n_eqNode)) {
            Z3_ast simpleConcat = mk_concat(t, arg0, eq_str);
            if (!inSameEqc(t, parent, simpleConcat)) {
              Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
              Z3_ast implyR = Z3_mk_eq(ctx, parent, simpleConcat);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          }
        }

        //---------------------------------------------------------
        // Case (2-1) begin: (Concat n_eqNode (Concat str var))
        if (arg0 == n_eqNode && isConcatFunc(t, arg1)) {
#ifdef DEBUGLOG
          __debugPrint(logFile, ">> [simplifyParent 3 @ %d] ", __LINE__);
          __debugPrint(logFile, "\n\n");
#endif
          Z3_ast r_concat_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg1), 0);
          if (isConstStr(t, r_concat_arg0)) {
            Z3_ast combined_str = Concat(t, eq_str, r_concat_arg0);
            Z3_ast r_concat_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg1), 1);
            Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
            Z3_ast simplifiedAst = mk_concat(t, combined_str, r_concat_arg1);

            if (!inSameEqc(t, parent, simplifiedAst)) {
              Z3_ast implyR = Z3_mk_eq(ctx, parent, simplifiedAst);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          }
        }
        // Case (2-1) end: (Concat n_eqNode (Concat str var))
        //---------------------------------------------------------

        //---------------------------------------------------------
        // Case (2-2) begin: (Concat (Concat var str) n_eqNode)
        if (isConcatFunc(t, arg0) && arg1 == n_eqNode) {
#ifdef DEBUGLOG
          __debugPrint(logFile, ">> [simplifyParent 4 @ %d] ", __LINE__);
          __debugPrint(logFile, "\n\n");
#endif
          Z3_ast l_concat_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg0), 1);
          if (isConstStr(t, l_concat_arg1)) {
            Z3_ast combined_str = Concat(t, l_concat_arg1, eq_str);
            Z3_ast l_concat_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, arg0), 0);
            Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
            Z3_ast simplifiedAst = mk_concat(t, l_concat_arg0, combined_str);

            if (!inSameEqc(t, parent, simplifiedAst)) {
              Z3_ast implyR = Z3_mk_eq(ctx, parent, simplifiedAst);
              Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
              addAxiom(t, implyToAssert, __LINE__);
            }
          }
        }
        // Case (2-2) end: (Concat (Concat var str) n_eqNode)
        //---------------------------------------------------------

        // Have to look up one more layer: if the parent of the concat is another concat
        //-------------------------------------------------
        // Case (3-1) begin: (Concat (Concat var n_eqNode) str )
        if (arg1 == n_eqNode) {
          int concat_parent_num = Z3_theory_get_num_parents(t, parent);
          for (int j = 0; j < concat_parent_num; j++) {
            Z3_ast concat_parent = Z3_theory_get_parent(t, parent, j);
            if (isConcatFunc(t, concat_parent)) {
              Z3_ast concat_parent_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat_parent), 0);
              Z3_ast concat_parent_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat_parent), 1);
              if (concat_parent_arg0 == parent && isConstStr(t, concat_parent_arg1)) {
#ifdef DEBUGLOG
                __debugPrint(logFile, "\n\n>> [simplifyParent 5 @ %d] ", __LINE__);
                printZ3Node(t, concat_parent);
                __debugPrint(logFile, "\n");
#endif
                Z3_ast combinedStr = Concat(t, eq_str, concat_parent_arg1);
                Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                Z3_ast simplifiedAst = mk_concat(t, arg0, combinedStr);

                if (!inSameEqc(t, concat_parent, simplifiedAst)) {
                  Z3_ast implyR = Z3_mk_eq(ctx, concat_parent, simplifiedAst);
                  Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                  addAxiom(t, implyToAssert, __LINE__);
                }
              }
            }
          }
        }
        // Case (3-1) end: (Concat (Concat var n_eqNode) str )
        // Case (3-2) begin: (Concat str (Concat n_eqNode var) )
        if (arg0 == n_eqNode) {
          int concat_parent_num = Z3_theory_get_num_parents(t, parent);
          for (int j = 0; j < concat_parent_num; j++) {
            Z3_ast concat_parent = Z3_theory_get_parent(t, parent, j);
            if (isConcatFunc(t, concat_parent)) {
              Z3_app parent_app = Z3_to_app(ctx, concat_parent);
              Z3_ast concat_parent_arg0 = Z3_get_app_arg(ctx, parent_app, 0);
              Z3_ast concat_parent_arg1 = Z3_get_app_arg(ctx, parent_app, 1);
              if (concat_parent_arg1 == parent && isConstStr(t, concat_parent_arg0)) {
#ifdef DEBUGLOG
                __debugPrint(logFile, ">> [simplifyParent 6 @ %d] ", __LINE__);
                printZ3Node(t, concat_parent);
                __debugPrint(logFile, "\n\n");
#endif
                Z3_ast combinedStr = Concat(t, concat_parent_arg0, eq_str);
                Z3_ast implyL = Z3_mk_eq(ctx, n_eqNode, eq_str);
                Z3_ast simplifiedAst = mk_concat(t, combinedStr, arg1);

                if (!inSameEqc(t, concat_parent, simplifiedAst)) {
                  Z3_ast implyR = Z3_mk_eq(ctx, concat_parent, simplifiedAst);
                  Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR);
                  addAxiom(t, implyToAssert, __LINE__);
                }
              }
            }
          }
        }
        // Case (3-2) end: (Concat str (Concat n_eqNode var) )
      }
    }
    n_eqNode = Z3_theory_get_eqc_next(t, n_eqNode);
  } while (n_eqNode != nn);
}

/*
 * Check whether Concat(a, b) can equal to a constant string
 */
int canConcatEqStr(Z3_theory t, Z3_ast concat, std::string str) {
  int strLen = str.length();
  if (isConcatFunc(t, concat)) {
    std::vector<Z3_ast> args;
    getNodesInConcat(t, concat, args);
    Z3_ast ml_node = args[0];
    Z3_ast mr_node = args[args.size() - 1];

    if (isConstStr(t, ml_node)) {
      std::string ml_str = getConstStrValue(t, ml_node);
      int ml_len = ml_str.length();
      if (ml_len > strLen)
        return 0;
      int cLen = ml_len;
      if (ml_str != str.substr(0, cLen))
        return 0;
    }

    if (isConstStr(t, mr_node)) {
      std::string mr_str = getConstStrValue(t, mr_node);
      int mr_len = mr_str.length();
      if (mr_len > strLen)
        return 0;
      int cLen = mr_len;
      if (mr_str != str.substr(strLen - cLen, cLen))
        return 0;
    }

    int sumLen = 0;
    for (unsigned int i = 0; i < args.size(); i++) {
      Z3_ast oneArg = args[i];
      if (isConstStr(t, oneArg)) {
        std::string arg_str = getConstStrValue(t, oneArg);
        if (str.find(arg_str) == std::string::npos) {
          return 0;
        }
        sumLen += getConstStrValue(t, oneArg).length();
      }
    }
    if (sumLen > strLen)
      return 0;
  }
  return 1;
}

/*
 * For two concats "assumed" to be equal by Z3, before having their concrete values:
 * Check whether the two concat can be equal
 */
int canConcatEqConcat(Z3_theory t, Z3_ast concat1, Z3_ast concat2) {
  // make sure left and right are concat functions
  if (isConcatFunc(t, concat1) && isConcatFunc(t, concat2)) {
    {
      // Suppose concat1 = concat(x, y), concat2 = concat(m, n)
      Z3_ast concat1_mostL = getMostLeftNodeInConcat(t, concat1);
      Z3_ast concat2_mostL = getMostLeftNodeInConcat(t, concat2);
      // if both x and m are const strings, check whether they have the same prefix
      if (isConstStr(t, concat1_mostL) && isConstStr(t, concat2_mostL)) {

        std::string concat1_mostL_str = getConstStrValue(t, concat1_mostL);
        std::string concat2_mostL_str = getConstStrValue(t, concat2_mostL);
        int cLen = std::min(concat1_mostL_str.length(), concat2_mostL_str.length());
        if (concat1_mostL_str.substr(0, cLen) != concat2_mostL_str.substr(0, cLen)) {
          return 0;
        }
      }
    }

    {
      Z3_ast concat1_mostR = getMostRightNodeInConcat(t, concat1);
      Z3_ast concat2_mostR = getMostRightNodeInConcat(t, concat2);
      // if both m and n are const strings, check whether they have the same suffix
      if (isConstStr(t, concat1_mostR) && isConstStr(t, concat2_mostR)) {
        std::string concat1_mostR_str = getConstStrValue(t, concat1_mostR);
        std::string concat2_mostR_str = getConstStrValue(t, concat2_mostR);
        int cLen = std::min(concat1_mostR_str.length(), concat2_mostR_str.length());
        if (concat1_mostR_str.substr(concat1_mostR_str.length() - cLen, cLen) != concat2_mostR_str.substr(concat2_mostR_str.length() - cLen, cLen)) {
          return 0;
        }
      }
    }
  }
  return 1;
}

/*
 * Decide whether two n1 and n2 are ALREADY in a same eq class
 * Or n1 and n2 are ALREADY treated equal by the core
 * BUT, they may or may not be really equal
 */
bool inSameEqc(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  if (n1 == n2)
    return true;
  Z3_ast curr = Z3_theory_get_eqc_next(t, n1);
  while (curr != n1) {
    if (curr == n2)
      return true;
    curr = Z3_theory_get_eqc_next(t, curr);
  }
  return false;
}

/*
 *
 */
bool canTwoNodesEq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  Z3_ast n1_curr = n1;
  Z3_ast n2_curr = n2;

  // case 0: n1_curr is const string, n2_curr is const string
  if (isConstStr(t, n1_curr) && isConstStr(t, n2_curr)) {
    if (n1_curr != n2_curr) {
      return false;
    }
  }
  // case 1: n1_curr is concat, n2_curr is const string
  else if (isConcatFunc(t, n1_curr) && isConstStr(t, n2_curr)) {
    std::string n2_curr_str = getConstStrValue(t, n2_curr);
    if (canConcatEqStr(t, n1_curr, n2_curr_str) != 1) {
      return false;
    }
  }
  // case 2: n2_curr is concat, n1_curr is const string
  else if (isConcatFunc(t, n2_curr) && isConstStr(t, n1_curr)) {
    std::string n1_curr_str = getConstStrValue(t, n1_curr);
    if (canConcatEqStr(t, n2_curr, n1_curr_str) != 1) {
      return false;
    }
  } else if (isConcatFunc(t, n1_curr) && isConcatFunc(t, n2_curr)) {
    if (canConcatEqConcat(t, n1_curr, n2_curr) != 1) {
      return false;
    }
  }

  return true;
}

/*
 * Get constant strings (from left to right) in an AST node and return them in astList
 */
void getconstStrAstsInNode(Z3_theory t, Z3_ast node, std::list<Z3_ast> & astList) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (isConstStr(t, node)) {
    astList.push_back(node);
  } else if (getNodeType(t, node) == my_Z3_Func) {
    Z3_app func_app = Z3_to_app(ctx, node);
    int argCount = Z3_get_app_num_args(ctx, func_app);
    for (int i = 0; i < argCount; i++) {
      Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
      getconstStrAstsInNode(t, argAst, astList);
    }
  }
}

/*
 *
 */
void strEqLengthAxiom(Z3_theory t, Z3_ast varAst, Z3_ast strAst, int line) {
  Z3_context ctx = Z3_theory_get_context(t);

  if (getNodeType(t, varAst) == my_Z3_Str_Var) {
    std::string vName = std::string(Z3_ast_to_string(ctx, varAst));
    if (vName.length() >= 6 && (vName.substr(0, 6) == "$$_len" || vName.substr(0, 6) == "$$_val" || vName.substr(0, 6) == "$$_uRt")) {
      return;
    }
  }

  if (getNodeType(t, strAst) == my_Z3_Str_Var) {
    std::string vName = std::string(Z3_ast_to_string(ctx, strAst));
    if (vName.length() >= 6 && (vName.substr(0, 6) == "$$_len" || vName.substr(0, 6) == "$$_val" || vName.substr(0, 6) == "$$_uRt")) {
      return;
    }
  }

  Z3_ast implyL = Z3_mk_eq(ctx, varAst, strAst);
  Z3_ast implyR = Z3_mk_eq(ctx, mk_length(t, varAst), mk_length(t, strAst));
  Z3_ast lenAxiom = Z3_mk_implies(ctx, implyL, implyR);
  addAxiom(t, lenAxiom, line, true);
}

/*
 *
 */
int haveEQLength(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  int n1Len = getLenValue(t, n1);
  int n2Len = getLenValue(t, n2);

  if (n1Len != -1 && n1Len == n2Len) {
    return 1;
  } else if (n1Len == -1 && n2Len == -1) {
    Z3_ast n1Root = Z3_theory_getArithEqcRoot(t, mk_length(t, n1));
    Z3_ast n2Root = Z3_theory_getArithEqcRoot(t, mk_length(t, n2));
    if (n1Root != NULL && n1Root == n2Root) {
      return 2;
    } else {
      return 0;
    }
  } else {
    return 0;
  }
}

/*
 *
 */
int inferLenConcat(Z3_theory t, Z3_ast n) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n), 0);
  Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n), 1);
  int arg0_len = getLenValue(t, arg0);
  int arg1_len = getLenValue(t, arg1);
  if (arg0_len != -1 && arg1_len != -1 && getLenValue(t, n) == -1) {
    Z3_ast l_items[2];
    int lc = 0;
    Z3_ast axl = NULL;
    if (mk_length(t, arg0) != mk_int(ctx, arg0_len)) {
      l_items[lc++] = Z3_mk_eq(ctx, mk_length(t, arg0), mk_int(ctx, arg0_len));
    }
    if (mk_length(t, arg1) != mk_int(ctx, arg1_len)) {
      l_items[lc++] = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, arg1_len));
    }
    if (lc == 1)
      axl = l_items[0];
    else
      axl = Z3_mk_and(ctx, lc, l_items);

    int nnLen = arg0_len + arg1_len;
    Z3_ast axr = Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, nnLen));

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> [inferLenConcat] ");
    printZ3Node(t, n);
    __debugPrint(logFile, "\n");
#endif

    addAxiom(t, Z3_mk_implies(ctx, axl, axr), __LINE__);
    return nnLen;
  } else {
    return -1;
  }
}

/*
 *
 */
void inferLenConcatArg(Z3_theory t, Z3_ast n, int len) {
  if (len < 0)
    return;

  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n), 0);
  Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, n), 1);
  int arg0_len = getLenValue(t, arg0);
  int arg1_len = getLenValue(t, arg1);

  Z3_ast l_items[2];
  int lc = 0;
  Z3_ast axl = NULL;
  Z3_ast axr = NULL;
  if (mk_length(t, n) != mk_int(ctx, len)) {
    l_items[lc++] = Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, len));
  }

  if (arg0_len == -1 && arg1_len != -1) {
    if (mk_length(t, arg1) != mk_int(ctx, arg1_len)) {
      l_items[lc++] = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, arg1_len));
    }
    int arg0Len = len - arg1_len;
    if (arg0Len >= 0) {
      axr = Z3_mk_eq(ctx, mk_length(t, arg0), mk_int(ctx, arg0Len));
    } else {
      //negate
    }
  } else if (arg0_len != -1 && arg1_len == -1) {
    if (mk_length(t, arg0) != mk_int(ctx, arg0_len)) {
      l_items[lc++] = Z3_mk_eq(ctx, mk_length(t, arg0), mk_int(ctx, arg0_len));
    }
    int arg1Len = len - arg0_len;
    if (arg1Len >= 0) {
      axr = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, arg1Len));
    } else {
      //negate
    }
  } else {

  }

  if (axr != NULL) {
    if (lc == 1)
      axl = l_items[0];
    else
      axl = Z3_mk_and(ctx, lc, l_items);
    addAxiom(t, Z3_mk_implies(ctx, axl, axr), __LINE__);
  }
}

/*
 *
 */
void inferLenConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  int nnLen = getLenValue(t, nn1);
  if (nnLen == -1)
    nnLen = getLenValue(t, nn2);

  // ---------------------------------------------
  // case 1:
  //    Know: a1_arg0 and a1_arg1
  //    Unknown: nn1
  if (isConcatFunc(t, nn1)) {
    int nn1ConcatLen = inferLenConcat(t, nn1);
    if (nnLen == -1 && nn1ConcatLen != -1)
      nnLen = nn1ConcatLen;
  }
  // ---------------------------------------------
  // case 2:
  //    Know: a1_arg0 and a1_arg1
  //    Unknown: nn1
  if (isConcatFunc(t, nn2)) {
    int nn2ConcatLen = inferLenConcat(t, nn2);
    if (nnLen == -1 && nn2ConcatLen != -1)
      nnLen = nn2ConcatLen;
  }

  if (nnLen != -1) {
    if (isConcatFunc(t, nn1)) {
      inferLenConcatArg(t, nn1, nnLen);
    }
    if (isConcatFunc(t, nn2)) {
      inferLenConcatArg(t, nn2, nnLen);
    }
  }
}

/*
 *
 */
void printStrArgLen(Z3_theory t, Z3_ast node, int ll) {
#ifdef DEBUGLOG
  Z3_context ctx = Z3_theory_get_context(t);
  int nnLen = getLenValue(t, node);
  __debugPrint(logFile, "  ");
  for (int i = 0; i < ll; i++) {
    __debugPrint(logFile, "   ");
  }
  __debugPrint(logFile, " ** |");
  printZ3Node(t, node);
  __debugPrint(logFile, "| = %d  (Root = ", nnLen);
  printZ3Node(t, Z3_theory_getArithEqcRoot(t, mk_length(t, node)));
  __debugPrint(logFile, ")\n");

  if (isConcatFunc(t, node)) {
    Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
    Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 1);
    printStrArgLen(t, arg0, ll + 1);
    printStrArgLen(t, arg1, ll + 1);
  }
#endif
}

/*
 *
 */
Z3_ast simplifyConcat(Z3_theory t, Z3_ast node) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::map<Z3_ast, Z3_ast> resolvedMap;
  std::vector<Z3_ast> argVec;
  getNodesInConcat(t, node, argVec);

  for (unsigned int i = 0; i < argVec.size(); i++) {
    bool vArgHasEqcValue = false;
    Z3_ast vArg = get_eqc_value(t, argVec[i], vArgHasEqcValue);
    if (vArg != argVec[i]) {
      resolvedMap[argVec[i]] = vArg;
    }
  }

  if (resolvedMap.size() == 0) {
    return node;
  } else {
    Z3_ast resultAst = my_mk_str_value(t, "");
    for (unsigned int i = 0; i < argVec.size(); i++) {
      bool vArgHasEqcValue = false;
      Z3_ast vArg = get_eqc_value(t, argVec[i], vArgHasEqcValue);
      resultAst = mk_concat(t, resultAst, vArg);
    }

#ifdef DEBUGLOG
    __debugPrint(logFile, ">>  ");
    printZ3Node(t, node);
    __debugPrint(logFile, "  is simplified to  ");
    printZ3Node(t, resultAst);
    __debugPrint(logFile, "\n");
#endif

    if (inSameEqc(t, node, resultAst)) {
      __debugPrint(logFile, "    The two concats are already in a same eqc. SKIP\n\n");
    } else {
      Z3_ast * items = new Z3_ast[resolvedMap.size()];
      int pos = 0;
      std::map<Z3_ast, Z3_ast>::iterator itor = resolvedMap.begin();
      for (; itor != resolvedMap.end(); itor++) {
        items[pos++] = Z3_mk_eq(ctx, itor->first, itor->second);
      }
      Z3_ast implyL = NULL;
      if (pos == 1) {
        implyL = items[0];
      } else {
        implyL = Z3_mk_and(ctx, pos, items);
      }
      Z3_ast implyR = Z3_mk_eq(ctx, node, resultAst);
      Z3_ast toAdd = Z3_mk_implies(ctx, implyL, implyR);
      addAxiom(t, toAdd, __LINE__);
    }
    return resultAst;
  }
}

/*
 *
 */
void printContext(Z3_theory t) {
#ifdef DEBUGLOG
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
  __debugPrint(logFile, "\n\n== Context ====================================\n");
  printZ3Node(t, ctxAssign);
  __debugPrint(logFile, "\n===============================================\n\n");
#endif
}

/*
 *
 */
int checkLength2ConstStr(Z3_theory t, Z3_ast otherNode, Z3_ast otherEqc, Z3_ast constNode, Z3_ast constEqc, int line) {
  Z3_context ctx = Z3_theory_get_context(t);
  int strLen = getConstStrValue(t, constEqc).length();
  if (isConcatFunc(t, otherEqc)) {
    // otherEqc is a concat.
    int sumLen = 0;
    std::vector<Z3_ast> args;
    std::vector<Z3_ast> items;
    getNodesInConcat(t, otherEqc, args);
    for (unsigned int i = 0; i < args.size(); i++) {
      Z3_ast oneArg = args[i];
      int argLen = getLenValue(t, oneArg);
      if (argLen != -1) {
        if (!isConstStr(t, oneArg)) {
          items.push_back(Z3_mk_eq(ctx, mk_length(t, oneArg), mk_int(ctx, argLen)));
        }
        sumLen += argLen;
        if (sumLen > strLen) {
          if (otherNode != otherEqc)
            items.push_back(Z3_mk_eq(ctx, otherNode, otherEqc));
          if (constNode != constEqc)
            items.push_back(Z3_mk_eq(ctx, constNode, constEqc));
          items.push_back(Z3_mk_eq(ctx, constNode, otherNode));
          Z3_ast * ll = new Z3_ast[items.size()];
          for (unsigned int i = 0; i < items.size(); i++) {
            ll[i] = items[i];
          }
          Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_and(ctx, items.size(), ll));
          delete[] ll;
          addAxiom(t, toAssert, line);
          __debugPrint(logFile, "\n\n>> Inconsistent Length Detected: Concat <--> constStr @ %d.\n\n", line);
          return -1;
        }
      }
    }
  } else {
    int oLen = getLenValue(t, otherEqc);
    if (oLen != -1 && oLen != strLen) {
      Z3_ast l = Z3_mk_eq(ctx, otherEqc, constEqc);
      Z3_ast r = Z3_mk_eq(ctx, mk_length(t, otherEqc), mk_length(t, constEqc));
      Z3_ast toAssert = Z3_mk_implies(ctx, l, r);

      addAxiom(t, toAssert, line);
      __debugPrint(logFile, "\n\n>> Inconsistent Length Detected: var <--> constStr @ %d.\n\n", line);
      return -1;
    }
  }

  if (getLenValue(t, otherEqc) == -1) {
    Z3_ast l = Z3_mk_eq(ctx, otherEqc, constEqc);
    Z3_ast r = Z3_mk_eq(ctx, mk_length(t, otherEqc), mk_length(t, constEqc));
    Z3_ast toAssert = Z3_mk_implies(ctx, l, r);
    addAxiom(t, toAssert, __LINE__);
  }

  return 0;
}

/*
 *
 */
int checkLengthConcat2Var(Z3_theory t, Z3_ast concat, Z3_ast var) {
  Z3_context ctx = Z3_theory_get_context(t);
  int varLen = getLenValue(t, var);

  // length of var is not available
  if (varLen == -1) {
    return 0;
  }
  // length of var is available
  else {
    int sumLen = 0;
    std::vector<Z3_ast> args;
    std::vector<Z3_ast> items;
    getNodesInConcat(t, concat, args);
    for (unsigned int i = 0; i < args.size(); i++) {
      Z3_ast oneArg = args[i];
      int argLen = getLenValue(t, oneArg);
      if (argLen != -1) {
        if (!isConstStr(t, oneArg) && argLen != 0) {
          items.push_back(Z3_mk_eq(ctx, mk_length(t, oneArg), mk_int(ctx, argLen)));
        }
        sumLen += argLen;
        if (sumLen > varLen) {
          items.push_back(Z3_mk_eq(ctx, mk_length(t, var), mk_int(ctx, varLen)));
          items.push_back(Z3_mk_eq(ctx, concat, var));
          Z3_ast * ll = new Z3_ast[items.size()];
          for (unsigned int i = 0; i < items.size(); i++) {
            ll[i] = items[i];
          }
          Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_and(ctx, items.size(), ll));
          delete[] ll;
          addAxiom(t, toAssert, __LINE__);
          __debugPrint(logFile, "\n\n>> Inconsistent Length Detected in Concat <--> Var @ %d.\n\n", __LINE__);
          return -1;
        }
      }
    }
    return 0;
  }
}

/*
 *
 */
int checkLengthVar2Var(Z3_theory t, Z3_ast var1, Z3_ast var2) {
  Z3_context ctx = Z3_theory_get_context(t);
  int var1Len = getLenValue(t, var1);
  int var2Len = getLenValue(t, var2);
  if (var1Len != -1 && var2Len != -1 && var1Len != var2Len) {
    Z3_ast items[3];
    items[0] = Z3_mk_eq(ctx, mk_length(t, var1), mk_int(ctx, var1Len));
    items[1] = Z3_mk_eq(ctx, mk_length(t, var2), mk_int(ctx, var2Len));
    items[2] = Z3_mk_eq(ctx, var1, var2);
    Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_and(ctx, 3, items));
    addAxiom(t, toAssert, __LINE__);
    __debugPrint(logFile, "\n\n>> Inconsistent Length Detected in Var <--> Var @ %d.\n\n", __LINE__);
    return -1;
  }
  return 0;
}

/*
 *
 */
int checkLengthConcat2Concat(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::vector<Z3_ast> concat1Args;
  std::vector<Z3_ast> concat2Args;
  getNodesInConcat(t, n1, concat1Args);
  getNodesInConcat(t, n2, concat2Args);
  int concat1LenFixed = 1;
  int concat2LenFixed = 1;
  std::vector<Z3_ast> items;
  int sum1 = 0;
  int sum2 = 0;

  for (unsigned int i = 0; i < concat1Args.size(); i++) {
    Z3_ast oneArg = concat1Args[i];
    int argLen = getLenValue(t, oneArg);
    if (argLen != -1) {
      sum1 += argLen;
      if (!isConstStr(t, oneArg)) {
        items.push_back(Z3_mk_eq(ctx, mk_length(t, oneArg), mk_int(ctx, argLen)));
      }
    } else {
      concat1LenFixed = 0;
    }
  }

  for (unsigned int i = 0; i < concat2Args.size(); i++) {
    Z3_ast oneArg = concat2Args[i];
    int argLen = getLenValue(t, oneArg);
    if (argLen != -1) {
      sum2 += argLen;
      if (!isConstStr(t, oneArg)) {
        items.push_back(Z3_mk_eq(ctx, mk_length(t, oneArg), mk_int(ctx, argLen)));
      }
    } else {
      concat2LenFixed = 0;
    }
  }

  items.push_back(Z3_mk_eq(ctx, n1, n2));
  Z3_ast * ll = new Z3_ast[items.size()];
  for (unsigned int i = 0; i < items.size(); i++) {
    ll[i] = items[i];
  }
  Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_and(ctx, items.size(), ll));

  int conflict = 0;
  if (concat1LenFixed == 1 && concat2LenFixed == 1) {
    if (sum1 != sum2) {
      conflict = 1;
    }
  } else if (concat1LenFixed != 1 && concat2LenFixed == 1) {
    if (sum1 > sum2) {
      conflict = 1;
    }
  } else if (concat1LenFixed == 1 && concat2LenFixed != 1) {
    if (sum1 < sum2) {
      conflict = 1;
    }
  }

  if (conflict == 1) {
    addAxiom(t, toAssert, __LINE__);
    __debugPrint(logFile, "\n\n>> Inconsistent Length Detected in Concat <--> Concat @ %d.\n\n", __LINE__);
    return -1;
  }
  return 0;
}

/*
 *
 */
int checkLengthEqVarConcat(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  // n1 and n2 are not const string: either variable or concat
  bool n1Concat = isConcatFunc(t, n1);
  bool n2Concat = isConcatFunc(t, n2);
  if (n1Concat && n2Concat) {
    return checkLengthConcat2Concat(t, n1, n2);
  }
  // n1 is concat, n2 is variable
  else if (n1Concat && (!n2Concat)) {
    return checkLengthConcat2Var(t, n1, n2);
  }
  // n1 is variable, n2 is concat
  else if ((!n1Concat) && n2Concat) {
    return checkLengthConcat2Var(t, n2, n1);
  }
  // n1 and n2 are both variables
  else {
    return checkLengthVar2Var(t, n1, n2);
  }
  return 0;
}

/*
 *
 */
int checkLengConsistency(Z3_theory t, Z3_ast n1, Z3_ast eqc_n1, Z3_ast n2, Z3_ast eqc_n2, int line) {
//  if (n1 == eqc_n1 || n2 == eqc_n2) {
//   return 0;
//  }

  int n1Len = getLenValue(t, eqc_n1);
  if (n1Len == -1 && isConcatFunc(t, eqc_n1)) {
    n1Len = inferLenConcat(t, eqc_n1);
  }

  int n2Len = getLenValue(t, eqc_n2);
  if (n2Len == -1 && isConcatFunc(t, eqc_n2)) {
    n2Len = inferLenConcat(t, eqc_n2);
  }

  if (isConstStr(t, eqc_n1) && isConstStr(t, eqc_n2)) {
    // if two nodes are const strings, the consistency is already checked in value space in canTwoNodesEq()
    // just return 0 to make compiler happy
    return 0;
  } else if (isConstStr(t, eqc_n1) && (!isConstStr(t, eqc_n2))) {
    return checkLength2ConstStr(t, n2, eqc_n2, n1, eqc_n1, __LINE__);
  } else if (isConstStr(t, eqc_n2) && (!isConstStr(t, eqc_n1))) {
    return checkLength2ConstStr(t, n1, eqc_n1, n2, eqc_n2, __LINE__);
  } else {
    // eqc_n1 and eqc_n2 is either var or concat
    return checkLengthEqVarConcat(t, eqc_n1, eqc_n2);
  }
  return 0;
}


/*
 *
 */
void checkRegexIn(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::set<Z3_ast> eqNodeSet;
  Z3_ast nn1EqConst = collectEqNodes(t, nn1, eqNodeSet);
  Z3_ast nn2EqConst = collectEqNodes(t, nn2, eqNodeSet);
  Z3_ast constStr = (nn1EqConst != NULL) ? nn1EqConst : nn2EqConst;
  if (constStr == NULL) {
    return;
  } else {
    std::set<Z3_ast>::iterator itor = eqNodeSet.begin();
    for (; itor != eqNodeSet.end(); itor++) {
      if (regexInVarRegStrMap.find(*itor) != regexInVarRegStrMap.end()) {
        std::set<std::string>::iterator strItor = regexInVarRegStrMap[*itor].begin();
        for (; strItor != regexInVarRegStrMap[*itor].end(); strItor++) {
          std::string regStr = *strItor;
          std::string constStrValue = getConstStrValue(t, constStr);
          std::pair<Z3_ast, std::string> key1 = std::make_pair(*itor, regStr);
          if (regexInBoolMap.find(key1) != regexInBoolMap.end()) {
            Z3_ast boolVar = regexInBoolMap[key1];
            std::regex e(regStr);
            bool matchRes = std::regex_match(constStrValue, e);

#ifdef DEBUGLOG
            __debugPrint(logFile, ">> [checkRegexIn] ");
            printZ3Node(t, *itor);
            __debugPrint(logFile, " \\in %s ::= ", regStr.c_str());
            printZ3Node(t, boolVar);
            __debugPrint(logFile, "\n");
#endif
            Z3_ast toAssert = NULL;
            Z3_ast implyL = Z3_mk_eq(ctx, *itor, constStr);
            if (matchRes) {
              toAssert = Z3_mk_implies(ctx, implyL, Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx) ) );
            } else {
              toAssert = Z3_mk_implies(ctx, implyL, Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx) ) );
            }
            addAxiom(t, toAssert, __LINE__);
          }
        }
      }
    }
  }

}


//==================================================
// Should do equal check among eqc members of nn1 and nn2
// to discover incorrect nn1 = nn2, e.g
//--------------------------------------------------
//** cb_new_eq() : y2 = _!#_str3
// * [EQC] : { y2, (Concat ce m2) }, size = 2
// * [EQC] : { _!#_str3, (Concat abc x2) }, size = 2
//--------------------------------------------------
// y2 can not be equal to _!#_str3.
// Add an assertion: {y2 = (Concat ce m2)} /\ {_!#_str3 = (Concat abc x2)} --> y2 != _!#_str3
//==================================================
int newEqCheck(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast eqc_nn1 = nn1;
  do {
    Z3_ast eqc_nn2 = nn2;
    do {
      // inconsistency check: value
      if (canTwoNodesEq(t, eqc_nn1, eqc_nn2) == false) {
        Z3_ast l_item[3];
        int l_pos = 0;
        if (nn1 != eqc_nn1)
          l_item[l_pos++] = Z3_mk_eq(ctx, nn1, eqc_nn1);
        if (nn2 != eqc_nn2)
          l_item[l_pos++] = Z3_mk_eq(ctx, nn2, eqc_nn2);
        l_item[l_pos++] = Z3_mk_eq(ctx, nn1, nn2);
        Z3_ast toAssert = Z3_mk_not(ctx, my_mk_and(t, l_item, l_pos));
        addAxiom(t, toAssert, __LINE__);
        __debugPrint(logFile, "\n\n>> Inconsistent detected in newEqCheck.\n\n\n");
        return -1;
      }
      if (checkLengConsistency(t, nn1, eqc_nn1, nn2, eqc_nn2, __LINE__) == -1) {
        return -1;
      }
      eqc_nn2 = Z3_theory_get_eqc_next(t, eqc_nn2);
    } while (eqc_nn2 != nn2);
    eqc_nn1 = Z3_theory_get_eqc_next(t, eqc_nn1);
  } while (eqc_nn1 != nn1);

  // contain consistency check
  if (containPairBoolMap.size() > 0) {
    checkContainInNewEq(t, nn1, nn2);
  }

  if (regexInBoolMap.size() > 0) {
    __debugPrint(logFile, "\n>> checkRegexIn in newEqCheck.\n");
    checkRegexIn(t, nn1, nn2);
  }

//  bool regexChecked = consistCheckRegex(t, nn1, nn2);
//  if (!regexChecked) {
//    return -1;
//  }
  return 0;
}

/*
 * In cb_new_eq, when $$_len_varX = "more", more len tests are needed for varX
 */
void moreLenTests(Z3_theory t, Z3_ast lenTester, std::string lenTesterValue) {
  if (lenTesterFvarMap.find(lenTester) != lenTesterFvarMap.end()) {
    Z3_ast fVar = lenTesterFvarMap[lenTester];
    Z3_ast toAssert = genLenValOptionsForFreeVar(t, fVar, lenTester, lenTesterValue);

    addAxiom(t, toAssert, __LINE__, false);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n---------------------\n");
    __debugPrint(logFile, ">> Var: ");
    printZ3Node(t, fVar);
    __debugPrint(logFile," (@%d, Level %d):\n ", __LINE__, sLevel);
    printZ3Node(t, toAssert);
    __debugPrint(logFile, "\n---------------------\n");
#endif
  }
}

/*
 *
 */
void moreValueTests(Z3_theory t, Z3_ast valTester, std::string valTesterValue) {
  Z3_ast fVar = valueTesterFvarMap[valTester];
  int lenTesterCount = fvarLenTesterMap[fVar].size();

  Z3_ast effectiveLenInd = NULL;
  std::string effectiveLenIndiStr = "";
  for (int i = 0; i < lenTesterCount; i++) {
    Z3_ast len_indicator_pre = fvarLenTesterMap[fVar][i];
    bool indicatorHasEqcValue = false;
    Z3_ast len_indicator_value = get_eqc_value(t, len_indicator_pre, indicatorHasEqcValue);
    if (indicatorHasEqcValue) {
      std::string len_pIndiStr = getConstStrValue(t, len_indicator_value);
      if (len_pIndiStr != "more") {
        effectiveLenInd = len_indicator_pre;
        effectiveLenIndiStr = len_pIndiStr;
        break;
      }
    }
  }
  Z3_ast valueAssert = genFreeVarOptions(t, fVar, effectiveLenInd, effectiveLenIndiStr, valTester, valTesterValue);
  addAxiom(t, valueAssert, __LINE__, false);

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n---------------------\n");
  __debugPrint(logFile, ">> Var: ");
  printZ3Node(t, fVar);
  __debugPrint(logFile," (@%d, Level %d):\n ", __LINE__, sLevel);
  printZ3Node(t, valueAssert);
  __debugPrint(logFile, "\n---------------------\n");
#endif
}

void cb_arith_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2) {

}

// ----------------------------------
//   ** cb_new_eq():
//      nn1 = "more"
//      nn2 = $$_len_x2_2
//   ** cb_new_eq():
//      nn1 = "33"
//      nn2 = $$_val_x2_8_0
//   ----------------------------------
int freeVarAttempt(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, nn1) == my_Z3_Str_Var) {
    std::string vName = std::string(Z3_ast_to_string(ctx, nn1));
    if (vName.length() >= 6) {
      std::string vPrefix = vName.substr(0, 6);
      // length attempts
      if (vPrefix == "$$_len") {
        if (getNodeType(t, nn2) == my_Z3_ConstStr) {
          moreLenTests(t, nn1, getConstStrValue(t, nn2));
        }
        return 1;
      }
      // value attempts
      else if (vPrefix == "$$_val") {
        if (getNodeType(t, nn2) == my_Z3_ConstStr && "more" == getConstStrValue(t, nn2)) {
          moreValueTests(t, nn1, getConstStrValue(t, nn2));
        }
        return 1;
      } else if (vPrefix == "$$_uRt") {
        return 1;
      }
    }
  }
  return 0;
}

void groupNodeInEqc(Z3_theory t, Z3_ast n, std::set<Z3_ast> & concats, std::set<Z3_ast> & vars, std::set<Z3_ast> & constStrs) {
  Z3_ast eqcNode = n;
  do {
    if (isConcatFunc(t, eqcNode)) {
      Z3_ast simConcat = simplifyConcat(t, eqcNode);
      if (simConcat != eqcNode) {
        if (isConcatFunc(t, simConcat)) {
          concats.insert(simConcat);
        } else {
          if (isConstStr(t, simConcat)) {
            constStrs.insert(simConcat);
          } else {
            vars.insert(simConcat);
          }
        }
      } else {
        concats.insert(simConcat);
      }
    } else {
      if (isConstStr(t, eqcNode)) {
        constStrs.insert(eqcNode);
      } else {
        vars.insert(eqcNode);
      }
    }
    eqcNode = Z3_theory_get_eqc_next(t, eqcNode);
  } while (eqcNode != n);
}

void printAstSet(Z3_theory t, std::set<Z3_ast> & astSet) {
#ifdef DEBUGLOG
  std::set<Z3_ast>::iterator itor = astSet.begin();
  for (; itor != astSet.end(); itor++) {
    printZ3Node(t, *itor);
    __debugPrint(logFile, ", ");
  }
  __debugPrint(logFile, "\n");
#endif
}

/*
 *
 */
void new_eq_handler(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  //"str_eq --> length_eq" constraints
  Z3_context ctx = Z3_theory_get_context(t);

  int nn1Len = getLenValue(t, nn1);
  int nn2Len = getLenValue(t, nn2);
  Z3_ast emptyStr = my_mk_str_value(t, "");
  if (nn1Len == 0) {
    if (!inSameEqc(t, nn1, emptyStr) && nn2 != emptyStr) {
      Z3_ast eql = Z3_mk_eq(ctx, mk_length(t, nn1), mk_int(ctx, 0));
      Z3_ast eqr = Z3_mk_eq(ctx, nn1, emptyStr);
      Z3_ast toAss = Z3_mk_eq(ctx, eql, eqr);
      addAxiom(t, toAss, __LINE__);
    }
  }

  if (nn2Len == 0) {
    if (!inSameEqc(t, nn2, emptyStr) && nn1 != emptyStr) {
      Z3_ast eql = Z3_mk_eq(ctx, mk_length(t, nn2), mk_int(ctx, 0));
      Z3_ast eqr = Z3_mk_eq(ctx, nn2, emptyStr);
      Z3_ast toAss = Z3_mk_eq(ctx, eql, eqr);
      addAxiom(t, toAss, __LINE__);
    }
  }

  int hasLenType = haveEQLength(t, nn1, nn2);
  if (hasLenType == 1) {
    __debugPrint(logFile, ">> length(nn1) = length(nn2) is already known. SKIP-1.\n\n");
  } else if (hasLenType == 2) {
    __debugPrint(logFile, ">> nn1Root = ");
    printZ3Node(t, Z3_theory_getArithEqcRoot(t, mk_length(t, nn1)));
    __debugPrint(logFile, "\n");
    __debugPrint(logFile, ">> nn2Root = ");
    printZ3Node(t, Z3_theory_getArithEqcRoot(t, mk_length(t, nn2)));
    __debugPrint(logFile, "\n");
    __debugPrint(logFile, ">> length(nn1) = length(nn2) is already known. SKIP-2.\n\n");
  } else {
    strEqLengthAxiom(t, nn1, nn2, __LINE__);
  }

  std::set<Z3_ast> concats_nn1Eqc;
  std::set<Z3_ast> vars_nn1Eqc;
  std::set<Z3_ast> constStrs_nn1Eqc;
  groupNodeInEqc(t, nn1, concats_nn1Eqc, vars_nn1Eqc, constStrs_nn1Eqc);
  std::set<Z3_ast> concats_nn2Eqc;
  std::set<Z3_ast> vars_nn2Eqc;
  std::set<Z3_ast> constStrs_nn2Eqc;
  groupNodeInEqc(t, nn2, concats_nn2Eqc, vars_nn2Eqc, constStrs_nn2Eqc);

#ifdef DEBUGLOG
  __debugPrint(logFile, ">> EQC(n1):\n");
  __debugPrint(logFile, "   -- [Concat] ");
  printAstSet(t, concats_nn1Eqc);
  __debugPrint(logFile, "   -- [Var] ");
  printAstSet(t, vars_nn1Eqc);
  __debugPrint(logFile, "   -- [Const] ");
  printAstSet(t, constStrs_nn1Eqc);

  __debugPrint(logFile, ">> EQC(n2):\n");
  __debugPrint(logFile, "   -- [Concat] ");
  printAstSet(t, concats_nn2Eqc);
  __debugPrint(logFile, "   -- [Var] ");
  printAstSet(t, vars_nn2Eqc);
  __debugPrint(logFile, "   -- [Const] ");
  printAstSet(t, constStrs_nn2Eqc);
  __debugPrint(logFile, "\n\n");
#endif

  //  --------------------------------------------------------------------------
  //  step 1: concat = concat, but avoid duplicated splits
  //          e.g. eqc1 = {concat1, concat2, concat3}
  //               eqc2 = {concat4}
  //          split concat4 with one of concat in eqc1 seems to be sufficient
  int hasCommon = 0;
  if (concats_nn1Eqc.size() != 0 && concats_nn2Eqc.size() != 0) {
    std::set<Z3_ast>::iterator itor1 = concats_nn1Eqc.begin();
    std::set<Z3_ast>::iterator itor2 = concats_nn2Eqc.begin();
    for (; itor1 != concats_nn1Eqc.end(); itor1++) {
      if (concats_nn2Eqc.find(*itor1) != concats_nn2Eqc.end()) {
        hasCommon = 1;
        break;
      }
    }
    for (; itor2 != concats_nn2Eqc.end(); itor2++) {
      if (concats_nn1Eqc.find(*itor2) != concats_nn1Eqc.end()) {
        hasCommon = 1;
        break;
      }
    }
    if (hasCommon == 0) {
      simplifyConcatEq(t, *(concats_nn1Eqc.begin()), *(concats_nn2Eqc.begin()));
    }
  }

  // ------------------------------------
  //  step 2: concat = constStr
  if (constStrs_nn1Eqc.size() != 0) {
    Z3_ast conStr = *(constStrs_nn1Eqc.begin());
    std::set<Z3_ast>::iterator itor2 = concats_nn2Eqc.begin();
    for (; itor2 != concats_nn2Eqc.end(); itor2++) {
      solve_concat_eq_str(t, *itor2, conStr);
    }
  } else if (constStrs_nn2Eqc.size() != 0) {
    Z3_ast conStr = *(constStrs_nn2Eqc.begin());
    std::set<Z3_ast>::iterator itor1 = concats_nn1Eqc.begin();
    for (; itor1 != concats_nn1Eqc.end(); itor1++) {
      solve_concat_eq_str(t, *itor1, conStr);
    }
  }

  //----------------------------------------------
  // A possible new_eq order:
  //   (1) v1 = "const": use "const" to simplify nodes having v1
  //   (2) v2 = v1:
  //       If we only check whether v1 or v2 is constant, we will miss the chance to
  //       simplify nodes with v2 since eqc(v1)="const"
  // Therefore, let's look at the eqc value of nn1 and nn2.
  //----------------------------------------------
  bool nn1HasEqcValue = false;
  bool nn2HasEqcValue = false;
  Z3_ast nn1_value = get_eqc_value(t, nn1, nn1HasEqcValue);
  Z3_ast nn2_value = get_eqc_value(t, nn2, nn2HasEqcValue);
  if (nn1HasEqcValue && !nn2HasEqcValue) {
    simplifyParent(t, nn2, nn1_value);
  }

  if (!nn1HasEqcValue && nn2HasEqcValue) {
    simplifyParent(t, nn1, nn2_value);
  }

  // ------------------------------------
  // regex
  // ------------------------------------
  Z3_ast nn1EqConst = NULL;
  std::set<Z3_ast> nn1EqUnrollFuncs;
  get_eqc_allUnroll(t, nn1, nn1EqConst, nn1EqUnrollFuncs);
  Z3_ast nn2EqConst = NULL;
  std::set<Z3_ast> nn2EqUnrollFuncs;
  get_eqc_allUnroll(t, nn2, nn2EqConst, nn2EqUnrollFuncs);

  if (nn2EqConst != NULL) {
    for (std::set<Z3_ast>::iterator itor1 = nn1EqUnrollFuncs.begin(); itor1 != nn1EqUnrollFuncs.end(); itor1++) {
      processUnrollEqConstStr(t, *itor1, nn2EqConst);
    }
  }

  if (nn1EqConst != NULL) {
    for (std::set<Z3_ast>::iterator itor2 = nn2EqUnrollFuncs.begin(); itor2 != nn2EqUnrollFuncs.end(); itor2++) {
      processUnrollEqConstStr(t, *itor2, nn1EqConst);
    }
  }
}

/*
 *
 */
void cb_new_eq(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  Z3_context ctx = Z3_theory_get_context(t);
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n\n\n\n");
  __debugPrint(logFile, "=================================================================================\n");
  __debugPrint(logFile, "** cb_new_eq():\n");
  printZ3Node(t, nn1);
  __debugPrint(logFile, "  = ");
  printZ3Node(t, nn2);
  __debugPrint(logFile, "\n");
#endif

  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  if (Z3_get_sort(ctx, nn1) != td->String || Z3_get_sort(ctx, nn2) != td->String) {
    __debugPrint(logFile, "-----------------\n");
    __debugPrint(logFile, ">> [cb_new_eq] SKIP: NOT String Sort @ %d\n\n", __LINE__);
    __debugPrint(logFile, "=================================================================================\n");
    return;
  }

#ifdef DEBUGLOG
  __debugPrint(logFile, "-----------------\n");
  printStrArgLen(t, nn1, 0);
  __debugPrint(logFile, "-----------------\n");
  printStrArgLen(t, nn2, 0);
  __debugPrint(logFile, "=================================================================================\n");
#endif

  if (freeVarAttempt(t, nn1, nn2) == 1 || freeVarAttempt(t, nn2, nn1) == 1) {
    return;
  }

  if (isConcatFunc(t, nn1) && isConcatFunc(t, nn2)) {
    bool nn1HasEqcValue = false;
    bool nn2HasEqcValue = false;
    Z3_ast nn1_value = get_eqc_value(t, nn1, nn1HasEqcValue);
    Z3_ast nn2_value = get_eqc_value(t, nn2, nn2HasEqcValue);
    if (nn1HasEqcValue && !nn2HasEqcValue) {
      simplifyParent(t, nn2, nn1_value);
    }

    if (!nn1HasEqcValue && nn2HasEqcValue) {
      simplifyParent(t, nn1, nn2_value);
    }

    Z3_ast nn1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 0);
    Z3_ast nn1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 1);
    Z3_ast nn2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 0);
    Z3_ast nn2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 1);
    if (nn1_arg0 == nn2_arg0 && inSameEqc(t, nn1_arg1, nn2_arg1)) {
      __debugPrint(logFile, ">> [cb_new_eq] SKIP: a1_arg0 == a2_arg0 @ %d\n\n", __LINE__);
      return;
    }

    if (nn1_arg1 == nn2_arg1 && inSameEqc(t, nn1_arg0, nn2_arg0)) {
      __debugPrint(logFile, ">> [cb_new_eq] SKIP: a1_arg1 == a2_arg1 @ %d\n\n", __LINE__);
      return;
    }
  }

  // Consistency check first
  if (newEqCheck(t, nn1, nn2) == -1) {
    return;
  }
#ifdef DEBUGLOG
  __debugPrint(logFile, ">> check done\n\n");
#endif

  new_eq_handler(t, nn1, nn2);
}

/*
 * Add axioms that are true for any string var
 */
void basicStrVarAxiom(Z3_theory t, Z3_ast vNode, int line) {
  if (basicStrVarAxiom_added.find(vNode) == basicStrVarAxiom_added.end()) {
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast lenTerm = mk_length(t, vNode);

    Z3_ast strlen_ge = Z3_mk_ge(ctx, lenTerm, mk_int(ctx, 0));
    addAxiom(t, strlen_ge, line, false);

    Z3_ast strLen_zero = Z3_mk_eq(ctx, lenTerm, mk_int(ctx, 0));
    Z3_ast str_empty = Z3_mk_eq(ctx, vNode, my_mk_str_value(t, ""));
    Z3_ast str_eq_ast2 = Z3_mk_eq(ctx, strLen_zero, str_empty);
    addAxiom(t, str_eq_ast2, line, false);

    basicStrVarAxiom_added[vNode] = 1;
  }
}

void nonEmptyStrVarAxiom(Z3_theory t, Z3_ast vNode, int line) {
  if (basicStrVarAxiom_added.find(vNode) == basicStrVarAxiom_added.end()) {
    Z3_context ctx = Z3_theory_get_context(t);
    Z3_ast lenTerm = mk_length(t, vNode);
    Z3_ast strlen_ge = Z3_mk_gt(ctx, lenTerm, mk_int(ctx, 0));
    addAxiom(t, strlen_ge, line, false);
    basicStrVarAxiom_added[vNode] = 1;
  }
}

/*
 * Add axioms that are true for any string var
 */
void basicConcatAxiom(Z3_theory t, Z3_ast vNode, int line) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast lenAst = mk_length(t, vNode);
  std::list<Z3_ast> astList;
  getconstStrAstsInNode(t, vNode, astList);
  int len = 0;
  std::list<Z3_ast>::iterator itor = astList.begin();
  for (; itor != astList.end(); itor++)
    len += getConstStrValue(t, (*itor)).length();

  if (len != 0)
    addAxiom(t, Z3_mk_ge(ctx, lenAst, mk_int(ctx, len)), __LINE__, false);
}

/*
 * Mark variable appeared in map "varAppearMap"
 */
void classifyAstByType(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<Z3_ast, int> & concatMap,
    std::map<Z3_ast, int> & unrollMap) {
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_context ctx = Z3_theory_get_context(t);
  T_myZ3Type nodeType = getNodeType(t, node);

  if (nodeType == my_Z3_Str_Var) {
    std::string vName = std::string(Z3_ast_to_string(ctx, node));
    if (!(vName.length() >= 6 && (vName.substr(0, 6) == "$$_len" || vName.substr(0, 6) == "$$_val" || vName.substr(0, 6) == "$$_uRt"))) {
      varMap[node] = 1;
    }
  } else if (getNodeType(t, node) == my_Z3_Func) {
    Z3_app func_app = Z3_to_app(ctx, node);
    Z3_func_decl funcDecl = Z3_get_app_decl(ctx, func_app);

    if (funcDecl == td->Length) {
      return;
    } else if (funcDecl == td->Concat) {
      Z3_ast arg0 = Z3_get_app_arg(ctx, func_app, 0);
      Z3_ast arg1 = Z3_get_app_arg(ctx, func_app, 1);
      bool arg0HasEq = false;
      bool arg1HasEq = false;
      Z3_ast arg0Val = get_eqc_value(t, arg0, arg0HasEq);
      Z3_ast arg1Val = get_eqc_value(t, arg1, arg1HasEq);

      int canskip = 0;

      if (arg0HasEq && arg0Val == emptyConstStr) {
        canskip = 1;
      }

      if (canskip == 0 && arg1HasEq && arg1Val == emptyConstStr) {
        canskip = 1;
      }

      if (concatMap.find(node) == concatMap.end()) {
        if (canskip == 0) {
          concatMap[node] = 1;
        }
      }
    } else if (funcDecl == td->Unroll) {
      if (unrollMap.find(node) == unrollMap.end())
        unrollMap[node] = 1;
    }

    int argCount = Z3_get_app_num_args(ctx, func_app);
    for (int i = 0; i < argCount; i++) {
      Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
      classifyAstByType(t, argAst, varMap, concatMap, unrollMap);
    }
  } else {

  }
}

/*
 *
 */
inline bool isInterestingFuncKind(Z3_decl_kind func_decl) {
  bool result = true;
  switch (func_decl) {
    case Z3_OP_EQ:
      result = true;
      break;
    default:
      result = false;
//        case Z3_OP_DISTINCT:
//        case Z3_OP_ITE:
//        case Z3_OP_AND:
//        case Z3_OP_OR:
//        case Z3_OP_IFF:
//        case Z3_OP_XOR:
//        case Z3_OP_NOT:
//        case Z3_OP_IMPLIES:
//            result = false;
//            break;
//        default:
//            result = true;
  }
  return result;
}

void classifyAstByTypeInPositiveContext(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<Z3_ast, int> & concatMap,
    std::map<Z3_ast, int> & unrollMap) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ctxAssign = Z3_get_context_assignment(ctx);

  if (Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, Z3_to_app(ctx, ctxAssign))) != Z3_OP_AND) {
    if (getNodeType(t, ctxAssign) == my_Z3_Func) {
      Z3_app func_app = Z3_to_app(ctx, ctxAssign);
      Z3_decl_kind func_decl = Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, func_app));
      if (isInterestingFuncKind(func_decl)) {
        classifyAstByType(t, ctxAssign, varMap, concatMap, unrollMap);
      }
    }
  } else {
    int argCount = Z3_get_app_num_args(ctx, Z3_to_app(ctx, ctxAssign));
    for (int i = 0; i < argCount; i++) {
      Z3_ast argAst = Z3_get_app_arg(ctx, Z3_to_app(ctx, ctxAssign), i);
      if (getNodeType(t, argAst) == my_Z3_Func) {
        Z3_app func_app = Z3_to_app(ctx, argAst);
        Z3_decl_kind func_decl = Z3_get_decl_kind(ctx, Z3_get_app_decl(ctx, func_app));

        if (isInterestingFuncKind(func_decl)) {
          classifyAstByType(t, argAst, varMap, concatMap, unrollMap);
        }
      }
    }
  }

}

/*
 *
 */

void getNodesInConcat(Z3_theory t, Z3_ast node, std::vector<Z3_ast> & nodeList) {
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, node) != my_Z3_Func || (getNodeType(t, node) == my_Z3_Func && Z3_get_app_decl(ctx, Z3_to_app(ctx, node)) != td->Concat)) {
    nodeList.push_back(node);
    return;
  } else {
    Z3_ast leftArg = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
    Z3_ast rightArg = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 1);
    getNodesInConcat(t, leftArg, nodeList);
    getNodesInConcat(t, rightArg, nodeList);
  }
}

Z3_ast getMostLeftNodeInConcat(Z3_theory t, Z3_ast node) {
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_context ctx = Z3_theory_get_context(t);

  if (getNodeType(t, node) != my_Z3_Func || (getNodeType(t, node) == my_Z3_Func && Z3_get_app_decl(ctx, Z3_to_app(ctx, node)) != td->Concat))
    return node;
  else {
    Z3_ast concatArgL = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
    return getMostLeftNodeInConcat(t, concatArgL);
  }
}

/*
 *
 */
Z3_ast getMostRightNodeInConcat(Z3_theory t, Z3_ast node) {
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_context ctx = Z3_theory_get_context(t);

  if (getNodeType(t, node) != my_Z3_Func || (getNodeType(t, node) == my_Z3_Func && Z3_get_app_decl(ctx, Z3_to_app(ctx, node)) != td->Concat))
    return node;
  else {
    Z3_ast concatArgR = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 1);
    return getMostRightNodeInConcat(t, concatArgR);
  }
}

/*
 *
 */
bool hasLengthOfNode(Z3_theory t, Z3_ast n, std::map<Z3_ast, int> & wanted) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl d = Z3_get_app_decl(ctx, Z3_to_app(ctx, n));
  int argCount = Z3_get_app_num_args(ctx, Z3_to_app(ctx, n));

  if (argCount == 0) {
    return false;
  } else {
    if (d == td->Length) {
      if (wanted.find(Z3_get_app_arg(ctx, Z3_to_app(ctx, n), 0)) != wanted.end()) {
        return true;
      }
    } else {
      bool result = false;
      for (int i = 0; i < argCount; i++) {
        Z3_ast argAst = Z3_get_app_arg(ctx, Z3_to_app(ctx, n), i);
        result = result || hasLengthOfNode(t, argAst, wanted);
      }
      return result;
    }
  }
  return false;
}

/*
 *
 */
void print_All_Eqc(Z3_theory t) {
#ifdef DEBUGLOG
  std::map<Z3_ast, int> strVarMap;
  std::map<Z3_ast, int> concatMap;
  std::map<Z3_ast, int> printedMap;
  std::map<Z3_ast, int> unrollsMap;

  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
  classifyAstByType(t, ctxAssign, strVarMap, concatMap, unrollsMap);

  __debugPrint(logFile, "\n\n=== EQC =======================================\n");

  std::map<Z3_ast, int>::iterator itor = strVarMap.begin();
  for (; itor != strVarMap.end(); itor++) {
    if (printedMap.find(itor->first) != printedMap.end())
    continue;

    int count = 0;
    Z3_ast curr = itor->first;
    do {
      count++;
      if (count > 1)
      break;
      curr = Z3_theory_get_eqc_next(t, curr);
    }while (curr != itor->first);

    if (count > 1) {
      bool iiHasEqcValue = false;
      if (get_eqc_value(t, itor->first, iiHasEqcValue) != itor->first) {
        __debugPrint(logFile, "  > ");
      } else {
        __debugPrint(logFile, "    ");
      }
      __debugPrint(logFile, "{ ");
      Z3_ast curr = itor->first;
      do {
        printedMap[curr] = 1;
        printZ3Node(t, curr);
        __debugPrint(logFile, ",  ");
        curr = Z3_theory_get_eqc_next(t, curr);
      }while (curr != itor->first);
      __debugPrint(logFile, "}\n");
    }
  }

  itor = concatMap.begin();
  for (; itor != concatMap.end(); itor++) {
    if (printedMap.find(itor->first) != printedMap.end())
    continue;

    int count = 0;
    Z3_ast curr = itor->first;
    do {
      count++;
      if (count > 1)
      break;
      curr = Z3_theory_get_eqc_next(t, curr);
    }while (curr != itor->first);

    if (count > 1) {
      bool hasEqcValue = false;
      if (get_eqc_value(t, itor->first, hasEqcValue) != itor->first) {
        __debugPrint(logFile, "  > ");
      } else {
        __debugPrint(logFile, "    ");
      }
      __debugPrint(logFile, "{ ");
      Z3_ast curr = itor->first;
      do {
        printedMap[curr] = 1;
        printZ3Node(t, curr);
        __debugPrint(logFile, ",  ");
        curr = Z3_theory_get_eqc_next(t, curr);
      }while (curr != itor->first);
      __debugPrint(logFile, "}\n");
    }
  }
  __debugPrint(logFile, "===============================================\n");
#endif
}


/*
 * groundedMap:
 * map<node, map<Vector, Set> >
 *   "node = Concat(Vector)" under the conditions of "/\(Set)"
 *   the "node" key is after deAliasing to save space
 */

Z3_ast deAliasNode(Z3_theory t, Z3_ast node, std::map<Z3_ast, Z3_ast> & varAliasMap, std::map<Z3_ast, Z3_ast> & concatAliasMap) {
  if (isStrVar(t, node)) {
    return getAliasIndexAst(varAliasMap, node);
  } else if (isConcatFunc(t, node)) {
    return getAliasIndexAst(concatAliasMap, node);
  }
  return node;
}


void getGroundedConcats(Z3_theory t, Z3_ast node, std::map<Z3_ast, Z3_ast> & varAliasMap,
                                                  std::map<Z3_ast, Z3_ast> & concatAliasMap,
                                                  std::map<Z3_ast, Z3_ast> & varConstMap,
                                                  std::map<Z3_ast, Z3_ast> & concatConstMap,
                                                  std::map<Z3_ast, std::map<Z3_ast, int>> & varEqConcatMap,
                                                  std::map<Z3_ast, std::map<std::vector<Z3_ast>, std::set<Z3_ast> > > & groundedMap) {
  if (isUnrollFunc(t, node)) {
    return;
  }
  // **************************************************
  // first deAlias the node if it is a var or concat
  // **************************************************
  node = deAliasNode(t, node, varAliasMap, concatAliasMap);

  if (groundedMap.find(node) != groundedMap.end()) {
    return;
  }

  // haven't computed grounded concats for "node" (de-aliased)
  // ---------------------------------------------------------
  Z3_context ctx = Z3_theory_get_context(t);

  // const strings: node is de-aliased
  if (isConstStr(t, node)) {
    std::vector<Z3_ast> concatNodes;
    concatNodes.push_back(node);
    groundedMap[node][concatNodes].clear();   // no condition
  }
  // Concat functions
  else if (isConcatFunc(t, node)) {
    // if "node" equals to a constant string, the just push the constant into the concat vector
    // Again "node" has been de-aliased at the very beginning
    if (concatConstMap.find(node) != concatConstMap.end()) {
      std::vector<Z3_ast> concatNodes;
      concatNodes.push_back(concatConstMap[node]);
      groundedMap[node][concatNodes].clear();
      groundedMap[node][concatNodes].insert(Z3_mk_eq(ctx, node, concatConstMap[node]));
    }
    // node doesn't have eq constant value. Process its children.
    else {
      // merge arg0 and arg1
      Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 0);
      Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, node), 1);
      Z3_ast arg0DeAlias = deAliasNode(t, arg0, varAliasMap, concatAliasMap);
      Z3_ast arg1DeAlias = deAliasNode(t, arg1, varAliasMap, concatAliasMap);
      getGroundedConcats(t, arg0DeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);
      getGroundedConcats(t, arg1DeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

      std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator arg0_grdItor = groundedMap[arg0DeAlias].begin();
      std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator arg1_grdItor;
      for (; arg0_grdItor != groundedMap[arg0DeAlias].end(); arg0_grdItor++) {
        arg1_grdItor = groundedMap[arg1DeAlias].begin();
        for (; arg1_grdItor != groundedMap[arg1DeAlias].end(); arg1_grdItor++) {
          std::vector<Z3_ast> ndVec;
          ndVec.insert(ndVec.end(), arg0_grdItor->first.begin(), arg0_grdItor->first.end());
          int arg0VecSize = arg0_grdItor->first.size();
          int arg1VecSize = arg1_grdItor->first.size();
          if (arg0VecSize > 0 && arg1VecSize > 0 && isConstStr(t, arg0_grdItor->first[arg0VecSize - 1]) && isConstStr(t, arg1_grdItor->first[0])) {
            ndVec.pop_back();
            ndVec.push_back(Concat(t, arg0_grdItor->first[arg0VecSize - 1], arg1_grdItor->first[0]));
            for (int i = 1; i < arg1VecSize; i++) {
              ndVec.push_back(arg1_grdItor->first[i]);
            }
          } else {
            ndVec.insert(ndVec.end(), arg1_grdItor->first.begin(), arg1_grdItor->first.end());
          }
          // only insert if we don't know "node = concat(ndVec)" since one set of condition leads to this is enough
          if (groundedMap[node].find(ndVec) == groundedMap[node].end()) {
            groundedMap[node][ndVec];
            if (arg0 != arg0DeAlias) {
              groundedMap[node][ndVec].insert(Z3_mk_eq(ctx, arg0, arg0DeAlias));
            }
            groundedMap[node][ndVec].insert(arg0_grdItor->second.begin(), arg0_grdItor->second.end());

            if (arg1 != arg1DeAlias) {
              groundedMap[node][ndVec].insert(Z3_mk_eq(ctx, arg1, arg1DeAlias));
            }
            groundedMap[node][ndVec].insert(arg1_grdItor->second.begin(), arg1_grdItor->second.end());
          }
        }
      }
    }
  }
  // string variables
  else if (isStrVar(t, node)){
    // deAliasedVar = Constant
    if (varConstMap.find(node) != varConstMap.end()) {
      std::vector<Z3_ast> concatNodes;
      concatNodes.push_back(varConstMap[node]);
      groundedMap[node][concatNodes].clear();
      groundedMap[node][concatNodes].insert(Z3_mk_eq(ctx, node, varConstMap[node]));
    }
    // deAliasedVar = someConcat
    else if (varEqConcatMap.find(node) != varEqConcatMap.end()) {
      Z3_ast eqConcat = varEqConcatMap[node].begin()->first;
      Z3_ast deAliasedEqConcat = deAliasNode(t, eqConcat, varAliasMap, concatAliasMap);
      getGroundedConcats(t, deAliasedEqConcat, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

      std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator grdItor = groundedMap[deAliasedEqConcat].begin();
      for (; grdItor != groundedMap[deAliasedEqConcat].end(); grdItor++) {
        std::vector<Z3_ast> ndVec;
        ndVec.insert(ndVec.end(), grdItor->first.begin(), grdItor->first.end());
        // only insert if we don't know "node = concat(ndVec)" since one set of condition leads to this is enough
        if (groundedMap[node].find(ndVec) == groundedMap[node].end()) {
          // condition: node = deAliasedEqConcat
          groundedMap[node][ndVec].insert(Z3_mk_eq(ctx, node, deAliasedEqConcat));
          // appending conditions for "deAliasedEqConcat = CONCAT(ndVec)"
          groundedMap[node][ndVec].insert(grdItor->second.begin(), grdItor->second.end());
        }
      }
    }
    // node (has been de-aliased) != constant && node (has been de-aliased) != any concat
    // just push in the deAliasedVar
    else {
      std::vector<Z3_ast> concatNodes;
      concatNodes.push_back(node);
      groundedMap[node][concatNodes];
    }
  }
}


void printGroundedConcat(Z3_theory t, Z3_ast node, std::map<Z3_ast, std::map<std::vector<Z3_ast>, std::set<Z3_ast> > > & groundedMap) {
#ifdef DEBUGLOG
  __debugPrint(logFile, ">> printGroundedConcat: ");
  printZ3Node(t, node);
  if (groundedMap.find(node) != groundedMap.end()) {
    __debugPrint(logFile, "\n--------------------------------------\n");
    std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator itor = groundedMap[node].begin();
    for (; itor != groundedMap[node].end(); itor++) {
      __debugPrint(logFile, "   [grounded] ");
      std::vector<Z3_ast>::const_iterator vIt = itor->first.begin();
      for ( ; vIt != itor->first.end(); vIt++) {
        printZ3Node(t, *vIt);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, "\n");

      __debugPrint(logFile, "   [condition] ");
      std::set<Z3_ast>::iterator sIt = itor->second.begin();
      for ( ; sIt != itor->second.end(); sIt++) {
        printZ3Node(t, *sIt);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, "\n");
    }
  } else {
    __debugPrint(logFile, "\n Not Found\n");
  }
  __debugPrint(logFile, "\n");
#endif
}


bool isPartialInGroundedConcat(Z3_theory t, const std::vector<Z3_ast> & strVec, const std::vector<Z3_ast> &  subStrVec) {
  int strCnt = strVec.size();
  int subStrCnt = subStrVec.size();

  if ( strCnt == 0 || subStrCnt == 0) {
    return false;
  }

  // The assumption is that all consecutive constant strings are merged into one node
  if (strCnt < subStrCnt) {
    return false;
  }

  if (subStrCnt == 1) {
    if (isConstStr(t, subStrVec[0])) {
      std::string subStrVal = getConstStrValue(t, subStrVec[0]);
      for (int i = 0; i < strCnt; i++) {
        if (isConstStr(t, strVec[i])) {
          std::string strVal = getConstStrValue(t, strVec[i]);
          if (strVal.find(subStrVal) != std::string::npos) {
            return true;
          }
        }
      }
    } else {
      for (int i = 0; i < strCnt; i++) {
        if (strVec[i] == subStrVec[0]) {
          return true;
        }
      }
    }
    return false;
  } else {
    for (int i = 0; i <= (strCnt - subStrCnt); i++) {
      // The first node in subStrVect should be
      //   * constant: a suffix of a note in strVec[i]
      //   * variable:
      bool firstNodesOK = true;
      if (isConstStr(t, subStrVec[0])) {
        std::string subStrHeadVal = getConstStrValue(t, subStrVec[0]);
        if (isConstStr(t, strVec[i])) {
          std::string strHeadVal = getConstStrValue(t, strVec[i]);
          if (strHeadVal.size() >= subStrHeadVal.size()) {
            std::string suffix = strHeadVal.substr(strHeadVal.size() - subStrHeadVal.size(), subStrHeadVal.size());
            if (suffix != subStrHeadVal) {
              firstNodesOK = false;
            }
          } else {
            firstNodesOK = false;
          }
        } else {
          if (subStrVec[0] != strVec[i]) {
            firstNodesOK = false;
          }
        }
      }
      if (! firstNodesOK) {
        continue;
      }

      // middle nodes
      bool midNodesOK = true;
      for (int j = 1; j < subStrCnt - 1; j++) {
        if (subStrVec[j] != strVec[i + j]) {
          midNodesOK = false;
          break;
        }
      }
      if (!midNodesOK) {
        continue;
      }

      // tail nodes
      int tailIdx = i + subStrCnt - 1;
      if (isConstStr(t, subStrVec[subStrCnt - 1])) {
        std::string subStrTailVal = getConstStrValue(t, subStrVec[subStrCnt - 1]);
        if (isConstStr(t, strVec[tailIdx])) {
          std::string strTailVal = getConstStrValue(t, strVec[tailIdx]);
          if (strTailVal.size() >= subStrTailVal.size()) {
            std::string prefix = strTailVal.substr(0, subStrTailVal.size());
            if (prefix == subStrTailVal) {
              return true;
            } else {
              continue;
            }
          } else {
            continue;
          }
        }
      } else {
        if (subStrVec[subStrCnt - 1] == strVec[tailIdx]) {
          return true;
        } else {
          continue;
        }
      }
    }
    return false;
  }
}


void checksubSequnce(Z3_theory t, Z3_ast str, Z3_ast strDeAlias, Z3_ast subStr, Z3_ast subStrDeAlias, Z3_ast boolVar,
                     std::map<Z3_ast, std::map<std::vector<Z3_ast>, std::set<Z3_ast> > > & groundedMap) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator itorStr = groundedMap[strDeAlias].begin();
  std::map<std::vector<Z3_ast>, std::set<Z3_ast> >::iterator itorSubStr;
  for (; itorStr != groundedMap[strDeAlias].end(); itorStr++) {
    itorSubStr = groundedMap[subStrDeAlias].begin();
    for (; itorSubStr != groundedMap[subStrDeAlias].end(); itorSubStr++) {
      bool contain = isPartialInGroundedConcat(t, itorStr->first, itorSubStr->first);
      if (contain) {
        std::set<Z3_ast> litems;
        if (str != strDeAlias) {
          litems.insert(Z3_mk_eq(ctx, str, strDeAlias));
        }
        if (subStr != subStrDeAlias) {
          litems.insert(Z3_mk_eq(ctx, subStr, subStrDeAlias));
        }
        litems.insert(itorStr->second.begin(), itorStr->second.end());
        litems.insert(itorSubStr->second.begin(), itorSubStr->second.end());
        Z3_ast implyL = mk_and_fromSet(t, litems);
        Z3_ast implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
        Z3_ast toAssert = NULL;
        if (implyL == NULL) {
          toAssert = implyR;
        } else {
          toAssert = Z3_mk_implies(ctx, implyL, implyR);
        }

#ifdef DEBUGLOG
      __debugPrint(logFile, "\n[checksubSequnce] Contains(");
      printZ3Node(t, str);
      __debugPrint(logFile, ", ");
      printZ3Node(t, subStr);
      __debugPrint(logFile, ") = ");
      printZ3Node(t, boolVar);
      __debugPrint(logFile, "\n");
#endif

        addAxiom(t, toAssert, __LINE__);
      }
    }
  }

}


void computeContains(Z3_theory t, std::map<Z3_ast, Z3_ast> & varAliasMap, std::map<Z3_ast, Z3_ast> & concatAliasMap,
                                  std::map<Z3_ast, Z3_ast> & varConstMap, std::map<Z3_ast, Z3_ast> & concatConstMap,
                                  std::map<Z3_ast, std::map<Z3_ast, int>> & varEqConcatMap) {

  std::map<Z3_ast, std::map<std::vector<Z3_ast>, std::set<Z3_ast> > > groundedMap;
  std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast>::iterator containItor = containPairBoolMap.begin();
  for (; containItor != containPairBoolMap.end(); containItor++) {
    std::pair<Z3_ast, Z3_ast> key = containItor->first;
    Z3_ast containBoolVar = containItor->second;
    Z3_ast str = key.first;
    Z3_ast subStr = key.second;

    Z3_ast strDeAlias = deAliasNode(t, str, varAliasMap, concatAliasMap);
    Z3_ast subStrDeAlias = deAliasNode(t, subStr, varAliasMap, concatAliasMap);

    getGroundedConcats(t, strDeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);
    getGroundedConcats(t, subStrDeAlias, varAliasMap, concatAliasMap, varConstMap, concatConstMap, varEqConcatMap, groundedMap);

#ifdef DEBUGLOG
    printGroundedConcat(t, strDeAlias, groundedMap);
    printGroundedConcat(t, subStrDeAlias, groundedMap);
#endif

    checksubSequnce(t, str, strDeAlias, subStr, subStrDeAlias, containBoolVar, groundedMap);
  }
}


/*
 * Dependence analysis from current context assignment
 * - "freeVarMap" contains a set of variables that doesn't constrained by Concats.
 *    But it's possible that it's bounded by unrolls
 *    For the case of
 *    (1) var1 = unroll(r1, t1)
 *        var1 is in the freeVarMap
 *        > should unroll r1 for var1
 *    (2) var1 = unroll(r1, t1) /\ var1 = Concat(var2, var3)
 *        var2, var3 are all in freeVar
 *        > should split the unroll function so that var2 and var3 are bounded by new unrolls
 */
int ctxDepAnalysis(Z3_theory t, std::map<Z3_ast, int> & strVarMap, std::map<Z3_ast, int> & freeVarMap,
    std::map<Z3_ast, std::set<Z3_ast> > & unrollGroupMap) {
  std::map<Z3_ast, int> concatMap;
  std::map<Z3_ast, int> unrollMap;
  std::map<Z3_ast, Z3_ast> aliasIndexMap;
  std::map<Z3_ast, Z3_ast> var_eq_constStr_map;
  std::map<Z3_ast, Z3_ast> concat_eq_constStr_map;
  std::map<Z3_ast, std::map<Z3_ast, int> > var_eq_concat_map;
  std::map<Z3_ast, std::map<Z3_ast, int> > var_eq_unroll_map;
  std::map<Z3_ast, std::map<Z3_ast, int> > concat_eq_concat_map;
  std::map<Z3_ast, std::map<Z3_ast, int> > depMap;

  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ctxAssign = Z3_get_context_assignment(ctx);

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n*********************************************************\n");
  __debugPrint(logFile, "       Dependence Analysis\n");
  __debugPrint(logFile, "---------------------------------------------------------\n\n");
#endif

  //--------------------------------------------
  // Step 1. get variables/Concat AST appeared in context
  //--------------------------------------------
  for (std::map<Z3_ast, int>::iterator it = inputVarMap.begin(); it != inputVarMap.end(); it++) {
    strVarMap[it->first] = 1;
  }
  classifyAstByTypeInPositiveContext(t, ctxAssign, strVarMap, concatMap, unrollMap);

  // -----------------------------------------
  std::map<Z3_ast, Z3_ast> aliasUnrollSet;
  std::map<Z3_ast, int>::iterator unrollItor = unrollMap.begin();
  for (; unrollItor != unrollMap.end(); unrollItor++) {
    if (aliasUnrollSet.find(unrollItor->first) != aliasUnrollSet.end())
      continue;
    Z3_ast aRoot = NULL;
    Z3_ast curr = unrollItor->first;
    do {
      if (isUnrollFunc(t, curr)) {
        if (aRoot == NULL) {
          aRoot = curr;
        }
        aliasUnrollSet[curr] = aRoot;
      }
      curr = Z3_theory_get_eqc_next(t, curr);
    } while (curr != unrollItor->first);
  }

  for (unrollItor = unrollMap.begin(); unrollItor != unrollMap.end(); unrollItor++) {
    Z3_ast unrFunc = unrollItor->first;
    Z3_ast urKey = aliasUnrollSet[unrFunc];
    unrollGroupMap[urKey].insert(unrFunc);
  }

  //--------------------------------------------
  // Step 2. Collect alias relation
  // e.g EQC={x, y, z}
  //     aliasIndexMap[y] = x
  //     aliasIndexMap[z] = x
  std::map<Z3_ast, int>::iterator varItor = strVarMap.begin();
  for (; varItor != strVarMap.end(); varItor++) {
    if (aliasIndexMap.find(varItor->first) != aliasIndexMap.end())
      continue;

    Z3_ast aRoot = NULL;
    Z3_ast curr = varItor->first;
    do {
      if (getNodeType(t, curr) == my_Z3_Str_Var) {
        if (aRoot == NULL)
          aRoot = curr;
        else
          aliasIndexMap[curr] = aRoot;
      }
      curr = Z3_theory_get_eqc_next(t, curr);
    } while (curr != varItor->first);
  }

  //--------------------------------------------
  // Step 3: Collect interested cases
  varItor = strVarMap.begin();
  for (; varItor != strVarMap.end(); varItor++) {
    Z3_ast deAliasNode = getAliasIndexAst(aliasIndexMap, varItor->first);
    //--------------------------------------------------------------
    // (1) variable = const string
    //     e.g, z = "str1" ::=  var_eq_constStr_map[z] = "str1"
    //--------------------------------------------------------------
    if (var_eq_constStr_map.find(deAliasNode) == var_eq_constStr_map.end()) {
      bool nodeHasEqcValue = false;
      Z3_ast nodeValue = get_eqc_value(t, deAliasNode, nodeHasEqcValue);
      if (nodeHasEqcValue)
        var_eq_constStr_map[deAliasNode] = nodeValue;
    }
    //--------------------------------------------------------------
    // (2) var_eq_concat
    //       * e.g,  z = concat("str1", b)  ::=  var_eq_concat[z][concat(c, "str2")] = 1
    //     var_eq_unroll
    //       * e.g,  z = unroll(...)        ::=  var_eq_unroll[z][unroll(...)] = 1
    //-----------------------------------------------------------------
    if (var_eq_concat_map.find(deAliasNode) == var_eq_concat_map.end()) {
      Z3_ast curr = Z3_theory_get_eqc_next(t, deAliasNode);
      while (curr != deAliasNode) {
        // collect concat
        if (isConcatFunc(t, curr)) {
          Z3_ast arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, curr), 0);
          Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, curr), 1);
          bool arg0HasEqcValue = false;
          bool arg1hasEqcValue = false;
          Z3_ast arg0_value = get_eqc_value(t, arg0, arg0HasEqcValue);
          Z3_ast arg1_value = get_eqc_value(t, arg1, arg1hasEqcValue);
          bool is_arg0_emptyStr = (arg0HasEqcValue) && (getConstStrValue(t, arg0_value) == "");
          bool is_arg1_emptyStr = (arg1hasEqcValue) && (getConstStrValue(t, arg1_value) == "");
          if (!is_arg0_emptyStr && !is_arg1_emptyStr) {
            var_eq_concat_map[deAliasNode][curr] = 1;
          }
        }
        // collect unroll functions
        else if (isUnrollFunc(t, curr)) {
          var_eq_unroll_map[deAliasNode][curr] = 1;
        }

        curr = Z3_theory_get_eqc_next(t, curr);
      }
    }
  }

  // --------------------------------------------------
  // * collect aliasing relation among eq concats
  //   e.g EQC={concat1, concat2, concat3}
  //       concats_eq_Index_map[concat2] = concat1
  //       concats_eq_Index_map[concat3] = concat1
  // --------------------------------------------------
  std::map<Z3_ast, Z3_ast> concats_eq_Index_map;
  std::map<Z3_ast, int>::iterator concatItor = concatMap.begin();
  for (; concatItor != concatMap.end(); concatItor++) {
    if (concats_eq_Index_map.find(concatItor->first) != concats_eq_Index_map.end())
      continue;

    Z3_ast aRoot = NULL;
    Z3_ast curr = concatItor->first;
    do {
      if (isConcatFunc(t, curr)) {
        if (aRoot == NULL)
          aRoot = curr;
        else
          concats_eq_Index_map[curr] = aRoot;
      }
      curr = Z3_theory_get_eqc_next(t, curr);
    } while (curr != concatItor->first);
  }

  concatItor = concatMap.begin();
  for (; concatItor != concatMap.end(); concatItor++) {
    Z3_ast deAliasConcat = NULL;
    if (concats_eq_Index_map.find(concatItor->first) != concats_eq_Index_map.end())
      deAliasConcat = concats_eq_Index_map[concatItor->first];
    else
      deAliasConcat = concatItor->first;

    // --------------------------------------------------
    // (3) concat_eq_constStr:
    //     e.g,  concat(a,b) = "str1"
    // --------------------------------------------------
    if (concat_eq_constStr_map.find(deAliasConcat) == concat_eq_constStr_map.end()) {
      bool nodeHasEqcValue = false;
      Z3_ast nodeValue = get_eqc_value(t, deAliasConcat, nodeHasEqcValue);
      if (nodeHasEqcValue)
        concat_eq_constStr_map[deAliasConcat] = nodeValue;
    }
    // --------------------------------------------------
    // (4) concat_eq_concat:
    //     e.g,  concat(a,b) = concat("str1", c) /\ z = concat(a, b) /\ z = concat(e, f)
    // --------------------------------------------------
    if (concat_eq_concat_map.find(deAliasConcat) == concat_eq_concat_map.end()) {
      Z3_ast curr = deAliasConcat;
      do {
        if (isConcatFunc(t, curr)) {
          // curr is not a concat that can be reduced
          if (concatMap.find(curr) != concatMap.end()) {
            concat_eq_concat_map[deAliasConcat][curr] = 1;
          }
        }
        curr = Z3_theory_get_eqc_next(t, curr);
      } while (curr != deAliasConcat);
    }
  }

#ifdef DEBUGLOG
  {
    __debugPrint(logFile, "(0) alias: variables\n");
    std::map<Z3_ast, std::map<Z3_ast, int> > aliasSumMap;

    std::map<Z3_ast, Z3_ast>::iterator itor0 = aliasIndexMap.begin();
    for (; itor0 != aliasIndexMap.end(); itor0++)
    aliasSumMap[itor0->second][itor0->first] = 1;

    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator keyItor = aliasSumMap.begin();
    for (; keyItor != aliasSumMap.end(); keyItor++) {
      __debugPrint(logFile, "    * ");
      printZ3Node(t, keyItor->first);
      __debugPrint(logFile, " : ");
      std::map<Z3_ast, int>::iterator innerItor = keyItor->second.begin();
      for (; innerItor != keyItor->second.end(); innerItor++) {
        printZ3Node(t, innerItor->first);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(1) var = constStr:\n");
    std::map<Z3_ast, Z3_ast>::iterator itor1 = var_eq_constStr_map.begin();
    for (; itor1 != var_eq_constStr_map.end(); itor1++) {
      __debugPrint(logFile, "    * ");
      printZ3Node(t, itor1->first);
      __debugPrint(logFile, " = ");
      printZ3Node(t, itor1->second);
      if (!inSameEqc(t, itor1->first, itor1->second))
      __debugPrint(logFile, "  (notTrue in ctx)");
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(2) var = concat:\n");
    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor2 = var_eq_concat_map.begin();
    for (; itor2 != var_eq_concat_map.end(); itor2++) {
      __debugPrint(logFile, "    * ");
      printZ3Node(t, itor2->first);
      __debugPrint(logFile, " = { ");
      std::map<Z3_ast, int>::iterator i_itor = itor2->second.begin();
      for (; i_itor != itor2->second.end(); i_itor++) {
        printZ3Node(t, i_itor->first);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, " }\n");
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(3) var = unrollFunc:\n");
    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor2 = var_eq_unroll_map.begin();
    for (; itor2 != var_eq_unroll_map.end(); itor2++) {
      __debugPrint(logFile, "    * ");
      printZ3Node(t, itor2->first);
      __debugPrint(logFile, " = { ");
      std::map<Z3_ast, int>::iterator i_itor = itor2->second.begin();
      for (; i_itor != itor2->second.end(); i_itor++) {
        printZ3Node(t, i_itor->first);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, " }\n");
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(4) concat = constStr:\n");
    std::map<Z3_ast, Z3_ast>::iterator itor3 = concat_eq_constStr_map.begin();
    for (; itor3 != concat_eq_constStr_map.end(); itor3++) {
      __debugPrint(logFile, "    * ");
      printZ3Node(t, itor3->first);
      __debugPrint(logFile, " = ");
      printZ3Node(t, itor3->second);
      __debugPrint(logFile, "\n");

    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(5) eq concats:\n");
    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor4 = concat_eq_concat_map.begin();
    for (; itor4 != concat_eq_concat_map.end(); itor4++) {
      if (itor4->second.size() > 1) {
        std::map<Z3_ast, int>::iterator i_itor = itor4->second.begin();
        __debugPrint(logFile, "    * ");
        for (; i_itor != itor4->second.end(); i_itor++) {
          printZ3Node(t, i_itor->first);
          __debugPrint(logFile, " , ");
        }
        __debugPrint(logFile, "\n");
      }
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(6) eq unrolls:\n");
    std::map<Z3_ast, std::set<Z3_ast> >::iterator itor5 = unrollGroupMap.begin();
    for (; itor5 != unrollGroupMap.end(); itor5++) {
      __debugPrint(logFile, "    * ");
      std::set<Z3_ast>::iterator i_itor = itor5->second.begin();
      for (; i_itor != itor5->second.end(); i_itor++) {
        printZ3Node(t, *i_itor);
        __debugPrint(logFile, ",  ");
      }
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
  }

  {
    __debugPrint(logFile, "(7) unroll = concats:\n");
    std::map<Z3_ast, std::set<Z3_ast> >::iterator itor5 = unrollGroupMap.begin();
    for (; itor5 != unrollGroupMap.end(); itor5++) {
      __debugPrint(logFile, "    * ");
      Z3_ast unroll = itor5->first;
      printZ3Node(t, unroll);
      __debugPrint(logFile, "\n");
      Z3_ast curr = unroll;
      do {
        if (isConcatFunc(t, curr)) {
          __debugPrint(logFile, "      >>> ");
          printZ3Node(t, curr);
          __debugPrint(logFile, "\n");
        }
        curr = Z3_theory_get_eqc_next(t, curr);
      }while (curr != unroll);
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
  }

#endif

  // *****************************
  // compute contains
  // -----------------------------
  if (containPairBoolMap.size() > 0) {
    computeContains(t, aliasIndexMap, concats_eq_Index_map, var_eq_constStr_map, concat_eq_constStr_map, var_eq_concat_map);
  }

  //*****************************
  // Step 4. Dependence analysis
  //---------------------
  // (1) var = constStr
  for (std::map<Z3_ast, Z3_ast>::iterator itor = var_eq_constStr_map.begin(); itor != var_eq_constStr_map.end(); itor++) {
    Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
    Z3_ast strAst = itor->second;
    depMap[var][strAst] = 1;
  }

  // (2) var = concat
  for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = var_eq_concat_map.begin(); itor != var_eq_concat_map.end(); itor++) {
    Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
    for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
      Z3_ast concat = itor1->first;
      std::map<Z3_ast, int> inVarMap;
      std::map<Z3_ast, int> inConcatMap;
      std::map<Z3_ast, int> inUnrollMap;
      classifyAstByType(t, concat, inVarMap, inConcatMap, inUnrollMap);
      for (std::map<Z3_ast, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++) {
        Z3_ast varInConcat = getAliasIndexAst(aliasIndexMap, itor2->first);
        if (!(depMap[var].find(varInConcat) != depMap[var].end() && depMap[var][varInConcat] == 1))
          depMap[var][varInConcat] = 2;
      }
    }
  }

  for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = var_eq_unroll_map.begin(); itor != var_eq_unroll_map.end(); itor++) {
    Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
    for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
      Z3_ast unrollFunc = itor1->first;
      std::map<Z3_ast, int> inVarMap;
      std::map<Z3_ast, int> inConcatMap;
      std::map<Z3_ast, int> inUnrollMap;
      classifyAstByType(t, unrollFunc, inVarMap, inConcatMap, inUnrollMap);
      for (std::map<Z3_ast, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++) {
        Z3_ast varInFunc = getAliasIndexAst(aliasIndexMap, itor2->first);

        __debugPrint(logFile, ">> var in unroll = ");
        printZ3Node(t, itor2->first);
        __debugPrint(logFile, "\n>> dealiased var = ");
        printZ3Node(t, varInFunc);
        __debugPrint(logFile, "\n");

        // it's possible that we have both (Unroll $$_regVar_0 $$_unr_0) /\ (Unroll abcd $$_unr_0), while $$_regVar_0 = "abcd"
        // have to exclude such cases
        bool varHasValue = false;
        get_eqc_value(t, varInFunc, varHasValue);
        if (varHasValue)
          continue;

        if (depMap[var].find(varInFunc) == depMap[var].end()) {
          depMap[var][varInFunc] = 6;
        }
      }
    }
  }

  //(3) concat = constStr
  for (std::map<Z3_ast, Z3_ast>::iterator itor = concat_eq_constStr_map.begin(); itor != concat_eq_constStr_map.end(); itor++) {
    Z3_ast concatAst = itor->first;
    Z3_ast constStr = itor->second;
    std::map<Z3_ast, int> inVarMap;
    std::map<Z3_ast, int> inConcatMap;
    std::map<Z3_ast, int> inUnrollMap;
    classifyAstByType(t, concatAst, inVarMap, inConcatMap, inUnrollMap);
    for (std::map<Z3_ast, int>::iterator itor2 = inVarMap.begin(); itor2 != inVarMap.end(); itor2++) {
      Z3_ast varInConcat = getAliasIndexAst(aliasIndexMap, itor2->first);
      if (!(depMap[varInConcat].find(constStr) != depMap[varInConcat].end() && depMap[varInConcat][constStr] == 1))
        depMap[varInConcat][constStr] = 3;
    }
  }

  //--------------------------------------------------------------
  // (4) equivlent concats
  //     - possiblity 1 : concat("str", v1) = concat(concat(v2, v3), v4) = concat(v5, v6)
  //         ==> v2, v5 are constrainted by "str"
  //     - possiblity 2 : concat(v1, "str") = concat(v2, v3) = concat(v4, v5)
  //         ==> v2, v4 are constrainted by "str"
  //--------------------------------------------------------------
  std::map<Z3_ast, Z3_ast> mostLeftNodes;
  std::map<Z3_ast, Z3_ast> mostRightNodes;

  std::map<Z3_ast, int> mLIdxMap;
  std::map<int, std::set<Z3_ast> > mLMap;
  std::map<Z3_ast, int> mRIdxMap;
  std::map<int, std::set<Z3_ast> > mRMap;
  std::set<Z3_ast> nSet;

  for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = concat_eq_concat_map.begin(); itor != concat_eq_concat_map.end(); itor++) {
    mostLeftNodes.clear();
    mostRightNodes.clear();

    Z3_ast mLConst = NULL;
    Z3_ast mRConst = NULL;

    for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
      Z3_ast concatNode = itor1->first;
      Z3_ast mLNode = getMostLeftNodeInConcat(t, concatNode);
      if (getNodeType(t, mLNode) == my_Z3_ConstStr) {
        if (mLConst == NULL && getConstStrValue(t, mLNode) != "") {
          mLConst = mLNode;
        }
      } else {
        mostLeftNodes[mLNode] = concatNode;
      }

      Z3_ast mRNode = getMostRightNodeInConcat(t, concatNode);
      if (getNodeType(t, mRNode) == my_Z3_ConstStr) {
        if (mRConst == NULL && getConstStrValue(t, mRNode) != "") {
          mRConst = mRNode;
        }
      } else {
        mostRightNodes[mRNode] = concatNode;
      }
    }

    if (mLConst != NULL) {
      // -------------------------------------------------------------------------------------
      // The left most variable in a concat is constrained by a constant string in eqc concat
      // -------------------------------------------------------------------------------------
      // e.g. Concat(x, ...) = Concat("abc", ...)
      // -------------------------------------------------------------------------------------
      for (std::map<Z3_ast, Z3_ast>::iterator itor1 = mostLeftNodes.begin(); itor1 != mostLeftNodes.end(); itor1++) {
        Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itor1->first);
        if (depMap[deVar].find(mLConst) == depMap[deVar].end() || depMap[deVar][mLConst] != 1) {
          depMap[deVar][mLConst] = 4;
        }
      }
    }

    {
      // -------------------------------------------------------------------------------------
      // The left most variables in eqc concats are constrained by each other
      // -------------------------------------------------------------------------------------
      // e.g. concat(x, ...) = concat(u, ...) = ...
      //      x and u are constrained by each other
      // -------------------------------------------------------------------------------------
      nSet.clear();
      std::map<Z3_ast, Z3_ast>::iterator itl = mostLeftNodes.begin();
      for (; itl != mostLeftNodes.end(); itl++) {
        bool lfHasEqcValue = false;
        get_eqc_value(t, itl->first, lfHasEqcValue);
        if (lfHasEqcValue)
          continue;
        Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itl->first);
        nSet.insert(deVar);
      }

      if (nSet.size() > 1) {
        int lId = -1;
        for (std::set<Z3_ast>::iterator itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
          if (mLIdxMap.find(*itor2) != mLIdxMap.end()) {
            lId = mLIdxMap[*itor2];
            break;
          }
        }
        if (lId == -1)
          lId = mLMap.size();
        for (std::set<Z3_ast>::iterator itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
          bool itorHasEqcValue = false;
          get_eqc_value(t, *itor2, itorHasEqcValue);
          if (itorHasEqcValue)
            continue;
          mLIdxMap[*itor2] = lId;
          mLMap[lId].insert(*itor2);
        }
      }
    }

    if (mRConst != NULL) {
      for (std::map<Z3_ast, Z3_ast>::iterator itor1 = mostRightNodes.begin(); itor1 != mostRightNodes.end(); itor1++) {
        Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itor1->first);
        if (depMap[deVar].find(mRConst) == depMap[deVar].end() || depMap[deVar][mRConst] != 1) {
          depMap[deVar][mRConst] = 5;
        }
      }
    }

    {
      nSet.clear();
      std::map<Z3_ast, Z3_ast>::iterator itr = mostRightNodes.begin();
      for (; itr != mostRightNodes.end(); itr++) {
        Z3_ast deVar = getAliasIndexAst(aliasIndexMap, itr->first);
        nSet.insert(deVar);
      }
      if (nSet.size() > 1) {
        int rId = -1;
        std::set<Z3_ast>::iterator itor2 = nSet.begin();
        for (; itor2 != nSet.end(); itor2++) {
          if (mRIdxMap.find(*itor2) != mRIdxMap.end()) {
            rId = mRIdxMap[*itor2];
            break;
          }
        }
        if (rId == -1)
          rId = mRMap.size();
        for (itor2 = nSet.begin(); itor2 != nSet.end(); itor2++) {
          bool rHasEqcValue = false;
          get_eqc_value(t, *itor2, rHasEqcValue);
          if (rHasEqcValue)
            continue;
          mRIdxMap[*itor2] = rId;
          mRMap[rId].insert(*itor2);
        }
      }
    }
  }

#ifdef DEBUGLOG
  __debugPrint(logFile, "-- Dependence Map ---------------------------------------\n");
  for (std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = depMap.begin(); itor != depMap.end(); itor++) {
    printZ3Node(t, itor->first);
    int nnLen = getLenValue(t, itor->first);
    __debugPrint(logFile, "  [len = %d] \t-->\t", nnLen);
    for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
      printZ3Node(t, itor1->first);
      __debugPrint(logFile, "(%d), ", itor1->second);
    }
    __debugPrint(logFile, "\n");
  }
  __debugPrint(logFile, "---------------------------------------------------------\n\n\n");
#endif

  //****************
  // Step 6. Compute free variables based on dependence map.
  // the case dependence map is empty, every var in VarMap is free
  //---------------------------------------------------------------
  // remove L/R most var in eq concat since they are constrained with each other
  std::map<Z3_ast, std::map<Z3_ast, int> > lrConstrainedMap;
  for (std::map<int, std::set<Z3_ast> >::iterator itor = mLMap.begin(); itor != mLMap.end(); itor++) {
    for (std::set<Z3_ast>::iterator it1 = itor->second.begin(); it1 != itor->second.end(); it1++) {
      std::set<Z3_ast>::iterator it2 = it1;
      it2++;
      for (; it2 != itor->second.end(); it2++) {
        Z3_ast n1 = *it1;
        Z3_ast n2 = *it2;
        lrConstrainedMap[n1][n2] = 1;
        lrConstrainedMap[n2][n1] = 1;
      }
    }
  }
  for (std::map<int, std::set<Z3_ast> >::iterator itor = mRMap.begin(); itor != mRMap.end(); itor++) {
    for (std::set<Z3_ast>::iterator it1 = itor->second.begin(); it1 != itor->second.end(); it1++) {
      std::set<Z3_ast>::iterator it2 = it1;
      it2++;
      for (; it2 != itor->second.end(); it2++) {
        Z3_ast n1 = *it1;
        Z3_ast n2 = *it2;
        lrConstrainedMap[n1][n2] = 1;
        lrConstrainedMap[n2][n1] = 1;
      }
    }
  }

  if (depMap.size() == 0) {
    std::map<Z3_ast, int>::iterator itor = strVarMap.begin();
    for (; itor != strVarMap.end(); itor++) {
      Z3_ast var = getAliasIndexAst(aliasIndexMap, itor->first);
      if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
        freeVarMap[var] = 1;
      } else {
        int lrConstainted = 0;
        std::map<Z3_ast, int>::iterator lrit = freeVarMap.begin();
        for (; lrit != freeVarMap.end(); lrit++) {
          if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
            lrConstainted = 1;
            break;
          }
        }
        if (lrConstainted == 0) {
          freeVarMap[var] = 1;
        }
      }
    }
  } else {
    // if the keys in aliasIndexMap are not contained in keys in depMap, they are free
    // e.g.,  x= y /\ x = z /\ t = "abc"
    //        aliasIndexMap[y]= x, aliasIndexMap[z] = x
    //        depMap        t ~ "abc"(1)
    //        x should be free
    std::map<Z3_ast, int>::iterator itor2 = strVarMap.begin();
    for (; itor2 != strVarMap.end(); itor2++) {
      if (aliasIndexMap.find(itor2->first) != aliasIndexMap.end()) {
        Z3_ast var = aliasIndexMap[itor2->first];
        if (depMap.find(var) == depMap.end()) {
          if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
            freeVarMap[var] = 1;
          } else {
            int lrConstainted = 0;
            std::map<Z3_ast, int>::iterator lrit = freeVarMap.begin();
            for (; lrit != freeVarMap.end(); lrit++) {
              if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
                lrConstainted = 1;
                break;
              }
            }
            if (lrConstainted == 0) {
              freeVarMap[var] = 1;
            }
          }
        }
      } else if (aliasIndexMap.find(itor2->first) == aliasIndexMap.end()) {
        // if a variable is not in aliasIndexMap and not in depMap, it's free
        if (depMap.find(itor2->first) == depMap.end()) {
          Z3_ast var = itor2->first;
          if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
            freeVarMap[var] = 1;
          } else {
            int lrConstainted = 0;
            std::map<Z3_ast, int>::iterator lrit = freeVarMap.begin();
            for (; lrit != freeVarMap.end(); lrit++) {
              if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
                lrConstainted = 1;
                break;
              }
            }
            if (lrConstainted == 0) {
              freeVarMap[var] = 1;
            }
          }
        }
      }
    }

    std::map<Z3_ast, std::map<Z3_ast, int> >::iterator itor = depMap.begin();
    for (; itor != depMap.end(); itor++) {
      for (std::map<Z3_ast, int>::iterator itor1 = itor->second.begin(); itor1 != itor->second.end(); itor1++) {
        if (getNodeType(t, itor1->first) == my_Z3_Str_Var) {
          Z3_ast var = getAliasIndexAst(aliasIndexMap, itor1->first);
          // if a var is dep on itself and all dependence are type 2, it's a free variable
          // e.g {y --> x(2), y(2), m --> m(2), n(2)} y,m are free
          {
            if (depMap.find(var) == depMap.end()) {
              if (freeVarMap.find(var) == freeVarMap.end()) {
                if (lrConstrainedMap.find(var) == lrConstrainedMap.end()) {
                  freeVarMap[var] = 1;
                } else {
                  int lrConstainted = 0;
                  std::map<Z3_ast, int>::iterator lrit = freeVarMap.begin();
                  for (; lrit != freeVarMap.end(); lrit++) {
                    if (lrConstrainedMap[var].find(lrit->first) != lrConstrainedMap[var].end()) {
                      lrConstainted = 1;
                      break;
                    }
                  }
                  if (lrConstainted == 0) {
                    freeVarMap[var] = 1;
                  }
                }

              } else {
                freeVarMap[var] = freeVarMap[var] + 1;
              }
            }
          }
        }
      }
    }
  }
  return 0;
}

/*
 *
 */
Z3_ast my_mk_internal_lenTest_var(Z3_theory t, Z3_ast node, int lTries) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << "$$_len_" << Z3_ast_to_string(ctx, node) << "_" << lTries;
  std::string name = ss.str();
  return my_mk_str_var(t, name.c_str());
}

/*
 *
 */
Z3_ast my_mk_internal_ValTest_var(Z3_theory t, Z3_ast node, int len, int vTries) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << "$$_val_" << Z3_ast_to_string(ctx, node) << "_" << len << "_" << vTries;
  std::string name = ss.str();
  return my_mk_str_var(t, name.c_str());
}

/*
 *
 */
Z3_ast genLenTestOptions(Z3_theory t, Z3_ast freeVar, Z3_ast indicator, int tries) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast freeVarLen = mk_length(t, freeVar);

  std::vector<Z3_ast> orList;
  std::vector<Z3_ast> andList;

  int distance = 3;
  int l = (tries - 1) * distance;
  int h = tries * distance;
  for (int i = l; i < h; i++) {
    orList.push_back(Z3_mk_eq(ctx, indicator, my_mk_str_value(t, intToString(i).c_str())));
    andList.push_back(Z3_mk_eq(ctx, orList[orList.size() - 1], Z3_mk_eq(ctx, freeVarLen, mk_int(ctx, i))));
  }
  orList.push_back(Z3_mk_eq(ctx, indicator, my_mk_str_value(t, "more")));
  andList.push_back(Z3_mk_eq(ctx, orList[orList.size() - 1], Z3_mk_ge(ctx, freeVarLen, mk_int(ctx, h))));

  Z3_ast * or_items = new Z3_ast[orList.size()];
  Z3_ast * and_items = new Z3_ast[andList.size() + 1];
  for (int i = 0; i < (int) orList.size(); i++) {
    or_items[i] = orList[i];
  }
  and_items[0] = Z3_mk_or(ctx, orList.size(), or_items);
  for (int i = 0; i < (int) andList.size(); i++) {
    and_items[i + 1] = andList[i];
  }
  Z3_ast lenTestAssert = Z3_mk_and(ctx, andList.size() + 1, and_items);
  delete[] or_items;
  delete[] and_items;

  Z3_ast assertL = NULL;
  int testerCount = tries - 1;          //fvarLenTesterMap[freeVar].size() - 1;
  if (testerCount > 0) {
    Z3_ast * and_items_LHS = new Z3_ast[testerCount];
    Z3_ast moreAst = my_mk_str_value(t, "more");
    for (int i = 0; i < testerCount; i++) {
      and_items_LHS[i] = Z3_mk_eq(ctx, fvarLenTesterMap[freeVar][i], moreAst);
    }
    if (testerCount == 1)
      assertL = and_items_LHS[0];
    else
      assertL = Z3_mk_and(ctx, testerCount, and_items_LHS);
    delete[] and_items_LHS;
  }

  if (assertL != NULL)
    lenTestAssert = Z3_mk_implies(ctx, assertL, lenTestAssert);
  return lenTestAssert;
}

/*
 *
 */
std::string genValString(int len, std::vector<int> & encoding) {
  if (charSetSize <= 0) {
    fprintf(stdout, "> Error: Character size smaller than or equal to 0. Exit.\n");
    fflush(stdout);
    exit(0);
  }

  std::string re = std::string(len, charSet[0]);
  for (int i = 0; i < (int) encoding.size() - 1; i++) {
    int idx = encoding[i];
    re[len - 1 - i] = charSet[idx];
  }
  return re;
}

/*
 *
 */
void printVectorInt(std::vector<int> & e) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "{");
  for (int i = 0; i < (int) e.size(); i++) {
    __debugPrint(logFile, " %d, ", e[i]);
  }
  __debugPrint(logFile, "}\n");
#endif
}

/*
 * The return value means whether we covered the search space
 *   - If the next encoding is valid, return false
 *   - Otherwise, return true
 */
bool getNextValEncode(std::vector<int> & base, std::vector<int> & next) {
  int s = 0;
  int carry = 0;
  next.clear();

  for (int i = 0; i < (int) base.size(); i++) {
    if (i == 0) {
      s = base[i] + 1;
      carry = s / charSetSize;
      s = s % charSetSize;
      next.push_back(s);
    } else {
      s = base[i] + carry;
      carry = s / charSetSize;
      s = s % charSetSize;
      next.push_back(s);
    }
  }
  if (next[next.size() - 1] > 0) {
    next.clear();
    return true;
  } else {
    return false;
  }
}

/*
 *
 */
Z3_ast genValOptions(Z3_theory t, Z3_ast freeVar, Z3_ast len_indicator, Z3_ast val_indicator, std::string lenStr, int tries) {
  Z3_context ctx = Z3_theory_get_context(t);
  int distance = 32;

  // ----------------------------------------------------------------------------------------
  // generate value options encoding
  // encoding is a vector of size (len + 1)
  // e.g, len = 2,
  //      encoding {1, 2, 0} means the value option is "charSet[2]"."charSet[1]"
  //      the last item in the encoding indicates whether the whole space is covered
  //      for example, if the charSet = {a, b}. All valid encodings are
  //        {0, 0, 0}, {1, 0, 0}, {0, 1, 0}, {1, 1, 0}
  //      if add 1 to the last one, we get
  //        {0, 0, 1}
  //      the last item "1" shows this is not a valid encoding, and we have covered all space
  // ----------------------------------------------------------------------------------------
  int len = atoi(lenStr.c_str());
  bool coverAll = false;
  std::vector<std::vector<int> > options;
  std::vector<int> base;

  if (tries == 0) {
    base = std::vector<int>(len + 1, 0);
    coverAll = false;
  } else {
    Z3_ast lastestValIndi = fvarValueTesterMap[freeVar][len][tries - 1].second;

    __debugPrint(logFile, ">> Last Value Tester = ");
    printZ3Node(t, lastestValIndi);
    __debugPrint(logFile, "\n\n");

    coverAll = getNextValEncode(valRangeMap[lastestValIndi], base);
  }

  long long l = (tries) * distance;
  long long h = l;
  for (int i = 0; i < distance; i++) {
    if (coverAll)
      break;
    options.push_back(base);
    h++;
    coverAll = getNextValEncode(options[options.size() - 1], base);
  }
  valRangeMap[val_indicator] = options[options.size() - 1];

  __debugPrint(logFile, ">> Value Tester Encoding = ");
  printVectorInt(valRangeMap[val_indicator]);
  __debugPrint(logFile, "\n");

  // ----------------------------------------------------------------------------------------

  std::vector<Z3_ast> orList;
  std::vector<Z3_ast> andList;

  for (long long i = l; i < h; i++) {
    orList.push_back(Z3_mk_eq(ctx, val_indicator, my_mk_str_value(t, longLongToString(i).c_str())));
    std::string aStr = genValString(len, options[i - l]);
    Z3_ast strAst = my_mk_str_value(t, aStr.c_str());
    andList.push_back(Z3_mk_eq(ctx, orList[orList.size() - 1], Z3_mk_eq(ctx, freeVar, strAst)));
  }
  if (!coverAll) {
    orList.push_back(Z3_mk_eq(ctx, val_indicator, my_mk_str_value(t, "more")));
  }

  Z3_ast * or_items = new Z3_ast[orList.size()];
  Z3_ast * and_items = new Z3_ast[andList.size() + 1];
  for (int i = 0; i < (int) orList.size(); i++) {
    or_items[i] = orList[i];
  }
  if (orList.size() > 1)
    and_items[0] = Z3_mk_or(ctx, orList.size(), or_items);
  else
    and_items[0] = or_items[0];

  for (int i = 0; i < (int) andList.size(); i++) {
    and_items[i + 1] = andList[i];
  }
  Z3_ast valTestAssert = Z3_mk_and(ctx, andList.size() + 1, and_items);
  delete[] or_items;
  delete[] and_items;

  // ---------------------------------------
  // IF the new value tester is $$_val_x_16_i
  // Should add ($$_len_x_j = 16) /\ ($$_val_x_16_i = "more")
  // ---------------------------------------
  andList.clear();
  andList.push_back(Z3_mk_eq(ctx, len_indicator, my_mk_str_value(t, lenStr.c_str())));
  for (int i = 0; i < tries; i++) {
    Z3_ast vTester = fvarValueTesterMap[freeVar][len][i].second;
    if (vTester != val_indicator)
      andList.push_back(Z3_mk_eq(ctx, vTester, my_mk_str_value(t, "more")));
  }
  Z3_ast assertL = NULL;
  if (andList.size() == 1) {
    assertL = andList[0];
  } else {
    Z3_ast * and_items = new Z3_ast[andList.size()];
    for (int i = 0; i < (int) andList.size(); i++) {
      and_items[i] = andList[i];
    }
    assertL = Z3_mk_and(ctx, andList.size(), and_items);
  }

  valTestAssert = Z3_mk_implies(ctx, assertL, valTestAssert);
  return valTestAssert;
}

/*
 *
 */
void printValueTesterList(Z3_theory t, std::vector<std::pair<int, Z3_ast> > & testerList, int lineNum) {
#ifdef DEBUGLOG
  int ss = testerList.size();
  __debugPrint(logFile, ">> valueTesterList @ %d = { ", lineNum);
  for (int i = 0; i < ss; i++) {
    if (i % 4 == 0)
    __debugPrint(logFile, "\n    ");
    __debugPrint(logFile, "(%d, ", testerList[i].first);
    printZ3Node(t, testerList[i].second);
    __debugPrint(logFile, "), ");
  }
  __debugPrint(logFile, "\n   }\n\n");
#endif
}

/*
 *
 */
Z3_ast genFreeVarOptions(Z3_theory t, Z3_ast freeVar, Z3_ast len_indicator, std::string len_valueStr, Z3_ast valTesterInCbEq,
    std::string valTesterValueStr) {
  int len = atoi(len_valueStr.c_str());

  if (fvarValueTesterMap[freeVar].find(len) == fvarValueTesterMap[freeVar].end()) {
    int tries = 0;
    Z3_ast val_indicator = my_mk_internal_ValTest_var(t, freeVar, len, tries);
    valueTesterFvarMap[val_indicator] = freeVar;
    fvarValueTesterMap[freeVar][len].push_back(std::make_pair(sLevel, val_indicator));
    printValueTesterList(t, fvarValueTesterMap[freeVar][len], __LINE__);
    return genValOptions(t, freeVar, len_indicator, val_indicator, len_valueStr, tries);
  } else {
    // go through all previous value testers
    // If some doesn't have an eqc value, add its assertion again.
    int testerTotal = fvarValueTesterMap[freeVar][len].size();
    int i = 0;
    for (; i < testerTotal; i++) {
      Z3_ast aTester = fvarValueTesterMap[freeVar][len][i].second;

      if (aTester == valTesterInCbEq) {
        break;
      }

      bool anEqcHasValue = false;
      // Z3_ast anEqc = get_eqc_value(t, aTester, anEqcHasValue);
      get_eqc_value(t, aTester, anEqcHasValue);
      if (!anEqcHasValue) {
#ifdef DEBUGLOG
        __debugPrint(logFile, "\n>> Value tester: ");
        printZ3Node(t, aTester);
        __debugPrint(logFile, " doesn't have eqc value.\n");
#endif

        Z3_ast makeupAssert = genValOptions(t, freeVar, len_indicator, aTester, len_valueStr, i);

#ifdef DEBUGLOG
        __debugPrint(logFile, "\n---------------------\n");
        __debugPrint(logFile, ">> Var: ");
        printZ3Node(t, freeVar);
        __debugPrint(logFile," (@%d, Level %d):\n ", __LINE__, sLevel);
        printZ3Node(t, makeupAssert);
        __debugPrint(logFile, "\n---------------------\n");
#endif
        addAxiom(t, makeupAssert, __LINE__, false);
      }
    }

    if (valTesterValueStr == "more") {
      Z3_ast valTester = NULL;
      if (i + 1 < testerTotal) {
        valTester = fvarValueTesterMap[freeVar][len][i + 1].second;
      } else {
        valTester = my_mk_internal_ValTest_var(t, freeVar, len, i + 1);
        valueTesterFvarMap[valTester] = freeVar;
        fvarValueTesterMap[freeVar][len].push_back(std::make_pair(sLevel, valTester));
        printValueTesterList(t, fvarValueTesterMap[freeVar][len], __LINE__);
      }
      Z3_ast nextAssert = genValOptions(t, freeVar, len_indicator, valTester, len_valueStr, i + 1);
      return nextAssert;
    }

    return NULL;
  }
}

/*
 *
 */
Z3_ast genLenValOptionsForFreeVar(Z3_theory t, Z3_ast freeVar, Z3_ast lenTesterInCbEq, std::string lenTesterValue) {
  // -----------------------------------------------------------------------------------------------------
  // True branch will be taken in final_check:
  //   - When we discover a variable is "free" for the first time
  //     lenTesterInCbEq = NULL
  //     lenTesterValue = ""
  // False branch will be taken when invoked by cb_new_eq.
  //   - After we set up length tester for a "free" var in final_check,
  //     when the tester is assigned to some value (e.g. "more" or "4"),
  //     lenTesterInCbEq != NULL, and its value will be passed by lenTesterValue
  // The difference is that in cb_new_eq, lenTesterInCbEq and its value have NOT been put into a same eqc
  // -----------------------------------------------------------------------------------------------------



#ifdef DEBUGLOG
  int tmpLen = getLenValue(t, freeVar);
  __debugPrint(logFile, " * freeVar = ");
  printZ3Node(t, freeVar);
  __debugPrint(logFile, " (len = %d)\n", tmpLen);
#endif

  // no length assertions for this free variable has ever been added.
  if (fvarLenCountMap.find(freeVar) == fvarLenCountMap.end()) {
    fvarLenCountMap[freeVar] = 1;
    unsigned int testNum = fvarLenCountMap[freeVar];
    Z3_ast indicator = my_mk_internal_lenTest_var(t, freeVar, testNum);
    fvarLenTesterMap[freeVar].push_back(indicator);
    lenTesterFvarMap[indicator] = freeVar;

    Z3_ast lenTestAssert = genLenTestOptions(t, freeVar, indicator, testNum);
    return lenTestAssert;
  } else {
    Z3_ast effectiveLenInd = NULL;
    std::string effectiveLenIndiStr = "";
    int lenTesterCount = (int) fvarLenTesterMap[freeVar].size();

    int i = 0;
    for (; i < lenTesterCount; i++) {
      Z3_ast len_indicator_pre = fvarLenTesterMap[freeVar][i];
      bool indicatorHasEqcValue = false;
      Z3_ast len_indicator_value = get_eqc_value(t, len_indicator_pre, indicatorHasEqcValue);
#ifdef DEBUGLOG
      __debugPrint(logFile, "  * length indicator ");
      printZ3Node(t, len_indicator_pre);
      __debugPrint(logFile, " = ");
      printZ3Node(t, len_indicator_value);
      __debugPrint(logFile, "\n");
#endif
      if (indicatorHasEqcValue) {
        std::string len_pIndiStr = getConstStrValue(t, len_indicator_value);
        if (len_pIndiStr != "more") {
          effectiveLenInd = len_indicator_pre;
          effectiveLenIndiStr = len_pIndiStr;
          break;
        }
      } else {
        if (lenTesterInCbEq != len_indicator_pre) {
#ifdef DEBUGLOG
          __debugPrint(logFile, "\n>> *Warning*: length indicator: ");
          printZ3Node(t, len_indicator_pre);
          __debugPrint(logFile, " doesn't have an EQC value. i = %d, lenTesterCount = %d\n", i , lenTesterCount);
#endif
          if (i > 0) {
            effectiveLenInd = fvarLenTesterMap[freeVar][i - 1];
            if (effectiveLenInd == lenTesterInCbEq) {
              effectiveLenIndiStr = lenTesterValue;
            } else {
              bool effectiveHasEqcValue = false;
              effectiveLenIndiStr = getConstStrValue(t, get_eqc_value(t, effectiveLenInd, effectiveHasEqcValue));
            }
          }
          break;
        }
        // lenTesterInCbEq == len_indicator_pre
        else {
          if (lenTesterValue != "more") {
            effectiveLenInd = len_indicator_pre;
            effectiveLenIndiStr = lenTesterValue;
            break;
          }
        }
      }
    }

    if (effectiveLenIndiStr == "more" || effectiveLenIndiStr == "") {
      Z3_ast indicator = NULL;
      unsigned int testNum = 0;

      __debugPrint(logFile, "\n>> effectiveLenIndiStr = %s, i = %d, lenTesterCount = %d\n", effectiveLenIndiStr.c_str(), i, lenTesterCount);

      if (i == lenTesterCount) {
        fvarLenCountMap[freeVar] = fvarLenCountMap[freeVar] + 1;
        testNum = fvarLenCountMap[freeVar];
        indicator = my_mk_internal_lenTest_var(t, freeVar, testNum);
        fvarLenTesterMap[freeVar].push_back(indicator);
        lenTesterFvarMap[indicator] = freeVar;
      } else {
        indicator = fvarLenTesterMap[freeVar][i];
        testNum = i + 1;
      }
      Z3_ast lenTestAssert = genLenTestOptions(t, freeVar, indicator, testNum);
      return lenTestAssert;
    } else {
      // length is fixed
      Z3_ast valueAssert = genFreeVarOptions(t, freeVar, effectiveLenInd, effectiveLenIndiStr, NULL, "");
      return valueAssert;
    }
  }
}

/*
 *
 */
void lenTester(Z3_theory t, Z3_ast var) {
  Z3_context ctx = Z3_theory_get_context(t);
  int step = 10;
  std::vector<Z3_ast> orItems;
  Z3_ast lenAst = mk_length(t, var);
  for (int i = 0; i < step; i++) {
    orItems.push_back(Z3_mk_eq(ctx, lenAst, mk_int(ctx, i)));
  }
  orItems.push_back(Z3_mk_ge(ctx, lenAst, mk_int(ctx, step)));
  Z3_ast toAssert = mk_or_fromVector(t, orItems);
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, ">> Len tester added @ %d\n", __LINE__);
#endif
  addAxiom(t, toAssert, __LINE__);
}

/*
 *
 */
Z3_bool cb_final_check(Z3_theory t) {
  Z3_context ctx = Z3_theory_get_context(t);

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n\n\n");
  __debugPrint(logFile, "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n");
  __debugPrint(logFile, "                cb_final_check @ Level [%d] \n", sLevel);
  __debugPrint(logFile, "=============================================================\n");
#endif

  //----------------------------------------------------------------------------------
  //run dependence analysis, find free string vars
  std::map<Z3_ast, int> varAppearInAssign;
  std::map<Z3_ast, int> freeVar_map;
  std::map<Z3_ast, std::set<Z3_ast> > unrollGroup_map;
  int conflictInDep = ctxDepAnalysis(t, varAppearInAssign, freeVar_map, unrollGroup_map);
  if (conflictInDep == -1) {
    __debugPrint(logFile, "\n\n###########################################################\n\n");
    return Z3_TRUE;
  }

  //**************************************************************
  // Check whether variables appeared have eq string constants
  // If yes, all input variables are all assigned.
  //         we don't need to instantiate them as free var
  // If no, need to go ahead and assign free variables
  //**************************************************************
  int needToAssignFreeVar = 0;
  std::map<Z3_ast, int>::iterator itor = varAppearInAssign.begin();
  for (; itor != varAppearInAssign.end(); itor++) {
    std::string vName = std::string(Z3_ast_to_string(ctx, itor->first));
    if (vName.length() >= 3 && vName.substr(0, 3) == "$$_")
      continue;

    bool hasEqcValue = false;
    // Z3_ast vNode = get_eqc_value(t, itor->first, hasEqcValue);
    get_eqc_value(t, itor->first, hasEqcValue);
    if (!hasEqcValue) {
      needToAssignFreeVar = 1;
      break;
    }
  }
  if (needToAssignFreeVar == 0) {
//    checkContain(t);
    __debugPrint(logFile, "\n * All non-internal variables are assigned. Done!\n");
    __debugPrint(logFile, "###########################################################\n\n");
    return Z3_TRUE;
  }

  // -----------------------------------------------------------
  // variables in freeVar are those not bouned by Concats
  // classify variables in freeVarMap:
  // (1) freeVar = unroll(r1, t1)
  // (2) vars are not bounded by either concat or unroll
  // -----------------------------------------------------------
  std::map<Z3_ast, std::set<Z3_ast> > fv_unrolls_map;
  std::set<Z3_ast> tmpSet;
  Z3_ast constValue = NULL;
  for (std::map<Z3_ast, int>::iterator fvIt2 = freeVar_map.begin(); fvIt2 != freeVar_map.end(); fvIt2++) {
    Z3_ast var = fvIt2->first;
    tmpSet.clear();
    get_eqc_allUnroll(t, var, constValue, tmpSet);
    if (tmpSet.size() > 0) {
      fv_unrolls_map[var] = tmpSet;
    }
  }
  // erase var bounded by an unroll function from freeVar_map
  for (std::map<Z3_ast, std::set<Z3_ast> >::iterator fvIt3 = fv_unrolls_map.begin(); fvIt3 != fv_unrolls_map.end(); fvIt3++) {
    Z3_ast var = fvIt3->first;
    freeVar_map.erase(var);
  }

  // collect the case:
  //   * Concat(X, Y) = unroll(r1, t1) /\ Concat(X, Y) = unroll(r2, t2)
  //     concatEqUnrollsMap[Concat(X, Y)] = {unroll(r1, t1), unroll(r2, t2)}

  std::map<Z3_ast, std::set<Z3_ast> > concatEqUnrollsMap;
  for (std::map<Z3_ast, std::set<Z3_ast> >::iterator urItor = unrollGroup_map.begin(); urItor != unrollGroup_map.end(); urItor++) {
    Z3_ast unroll = urItor->first;
    Z3_ast curr = unroll;
    do {
      if (isConcatFunc(t, curr)) {
        concatEqUnrollsMap[curr].insert(unroll);
        concatEqUnrollsMap[curr].insert(unrollGroup_map[unroll].begin(), unrollGroup_map[unroll].end());
      }
      curr = Z3_theory_get_eqc_next(t, curr);
    } while (curr != unroll);
  }

  // --------------------------

  std::map<Z3_ast, std::set<Z3_ast> > concatFreeArgsEqUnrollsMap;
  std::set<Z3_ast> fvUnrollSet;
  for (std::map<Z3_ast, std::set<Z3_ast> >::iterator concatItor = concatEqUnrollsMap.begin(); concatItor != concatEqUnrollsMap.end(); concatItor++) {
    Z3_ast concat = concatItor->first;
    Z3_ast concatArg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat), 0);
    Z3_ast concatArg2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat), 1);
    bool arg1Bounded = false;
    bool arg2Bounded = false;
    // arg1
    if (getNodeType(t, concatArg1) == my_Z3_Str_Var) {
      if (freeVar_map.find(concatArg1) == freeVar_map.end()) {
        arg1Bounded = true;
      } else {
        fvUnrollSet.insert(concatArg1);
      }
    } else if (isConcatFunc(t, concatArg1)) {
      if (concatEqUnrollsMap.find(concatArg1) == concatEqUnrollsMap.end()) {
        arg1Bounded = true;
      }
    }
    // arg2
    if (getNodeType(t, concatArg2) == my_Z3_Str_Var) {
      if (freeVar_map.find(concatArg2) == freeVar_map.end()) {
        arg2Bounded = true;
      } else {
        fvUnrollSet.insert(concatArg2);
      }
    } else if (isConcatFunc(t, concatArg2)) {
      if (concatEqUnrollsMap.find(concatArg2) == concatEqUnrollsMap.end()) {
        arg2Bounded = true;
      }
    }
    if (!arg1Bounded && !arg2Bounded) {
      concatFreeArgsEqUnrollsMap[concat].insert(concatEqUnrollsMap[concat].begin(), concatEqUnrollsMap[concat].end());
    }
  }
  for (std::set<Z3_ast>::iterator vItor = fvUnrollSet.begin(); vItor != fvUnrollSet.end(); vItor++) {
    freeVar_map.erase(*vItor);
  }

  // Assign free variables
  std::set<Z3_ast> fSimpUnroll;

  constValue = NULL;
#ifdef DEBUGLOG
  {
    __debugPrint(logFile, "* Free Var (# %d):\n", (int)freeVar_map.size());
    __debugPrint(logFile, "---------------------------------------------------------\n");
    int low = -1;
    int high = -1;
    for (std::map<Z3_ast, int>::iterator freeVarItor1 = freeVar_map.begin(); freeVarItor1 != freeVar_map.end(); freeVarItor1++)
    {
      Z3_ast freeVar = freeVarItor1->first;
      int lenValue = getLenValue(t, freeVar);
      low = -1;
      high = -1;
      Z3_theory_get_bound_strlen(t, getLengthAST(t, freeVar), low, high);
      __debugPrint(logFile, "   ");
      printZ3Node(t, freeVar);
      __debugPrint(logFile, "\t[depCnt = %d, Length = %d (%d, %d)]\n", freeVarItor1->second, lenValue, low, high);
    }
    __debugPrint(logFile, "---------------------------------------------------------\n\n\n");
  }

  {
    __debugPrint(logFile, "* Var bounded by unroll ONLY (# %d):\n", (int)fv_unrolls_map.size());
    __debugPrint(logFile, "---------------------------------------------------------\n");
    int low = -1;
    int high = -1;
    for (std::map<Z3_ast, std::set<Z3_ast> >::iterator fvIt1 = fv_unrolls_map.begin(); fvIt1 != fv_unrolls_map.end(); fvIt1++)
    {
      Z3_ast freeVar = fvIt1->first;
      int lenValue = getLenValue(t, freeVar);
      low = -1;
      high = -1;
      Z3_theory_get_bound_strlen(t, getLengthAST(t, freeVar), low, high);
      __debugPrint(logFile, "   ");
      printZ3Node(t, freeVar);
      __debugPrint(logFile, "\t[Length = %d (%d, %d)]\n", lenValue, low, high);
    }
    __debugPrint(logFile, "---------------------------------------------------------\n\n\n");
  }

  {
    __debugPrint(logFile, "* Concats bounded by unroll with unbounded args:\n");
    __debugPrint(logFile, "---------------------------------------------------------\n");
    for (std::map<Z3_ast, std::set<Z3_ast> >::iterator fvIt2 = concatFreeArgsEqUnrollsMap.begin(); fvIt2 != concatFreeArgsEqUnrollsMap.end(); fvIt2++)
    {
      Z3_ast concat = fvIt2->first;
      printZ3Node(t, concat);
      __debugPrint(logFile, "\t-->\t");
      for (std::set<Z3_ast>::iterator urItor = fvIt2->second.begin(); urItor != fvIt2->second.end(); urItor++) {
        printZ3Node(t, *urItor);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "---------------------------------------------------------\n\n\n");
  }
#endif

  for (std::map<Z3_ast, std::set<Z3_ast> >::iterator fvIt2 = concatFreeArgsEqUnrollsMap.begin(); fvIt2 != concatFreeArgsEqUnrollsMap.end(); fvIt2++) {
    Z3_ast concat = fvIt2->first;
    for (std::set<Z3_ast>::iterator urItor = fvIt2->second.begin(); urItor != fvIt2->second.end(); urItor++) {
      Z3_ast unroll = *urItor;
      processConcatEqUnroll(t, concat, unroll);
    }
  }

  for (std::map<Z3_ast, int>::iterator fvIt = freeVar_map.begin(); fvIt != freeVar_map.end(); fvIt++) {
    Z3_ast freeVar = fvIt->first;
    std::string vName = std::string(Z3_ast_to_string(ctx, freeVar));
    if (vName.length() >= 9 && vName.substr(0, 9) == "$$_regVar") {
      continue;
    }
    Z3_ast toAssert = genLenValOptionsForFreeVar(t, freeVar, NULL, "");
    if (toAssert != NULL) {
      addAxiom(t, toAssert, __LINE__);
    }
  }

  for (std::map<Z3_ast, std::set<Z3_ast> >::iterator fvIt1 = fv_unrolls_map.begin(); fvIt1 != fv_unrolls_map.end(); fvIt1++) {
    Z3_ast var = fvIt1->first;
    fSimpUnroll.clear();
    get_eqc_simpleUnroll(t, var, constValue, fSimpUnroll);
    if (fSimpUnroll.size() == 0) {
      genAssignUnrollReg(t, fv_unrolls_map[var]);
    } else {
      Z3_ast toAssert = genAssignUnrollStr2Reg(t, var, fSimpUnroll);
      if (toAssert != NULL) {
        addAxiom(t, toAssert, __LINE__);
      }
    }
  }
  __debugPrint(logFile, "\n###########################################################\n\n");
  return Z3_TRUE;
}

/*
 *
 */
void checkInputVar(Z3_theory t, Z3_ast node) {
  Z3_context ctx = Z3_theory_get_context(t);
  T_myZ3Type nodeType = getNodeType(t, node);

  if (nodeType == my_Z3_Str_Var) {
    std::string vName = std::string(Z3_ast_to_string(ctx, node));
    if (vName.length() >= 11 && vName.substr(0, 11) == "__cOnStStR_") {
      return;
    }
    if (vName.length() >= 3 && vName.substr(0, 3) == "$$_") {
      printf("> Error: please don't define a variable with a prefix \"$$_\" (");
      printf("%s). Abort\n\n", Z3_ast_to_string(ctx, node));
      exit(0);
    }

    inputVarMap[node] = 1;
  } else if (getNodeType(t, node) == my_Z3_Func) {
    Z3_app func_app = Z3_to_app(ctx, node);
    int argCount = Z3_get_app_num_args(ctx, func_app);
    for (int i = 0; i < argCount; i++) {
      Z3_ast argAst = Z3_get_app_arg(ctx, func_app, i);
      checkInputVar(t, argAst);
    }
  } else if (nodeType == my_Z3_Regex_Var) {
    printf("> Error: please don't define a separate Regex variable (");
    printf("%s). Abort\n\n", Z3_ast_to_string(ctx, node));
    exit(0);
  }
}

/*
 *
 */
void cb_init_search(Z3_theory t) {
#ifdef DEBUGLOG
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ctxAssign = Z3_get_context_assignment(ctx);
  __debugPrint(logFile, "\n\n");
  __debugPrint(logFile, "***********************************************\n");
  __debugPrint(logFile, "*               Starting Search               *\n");
  __debugPrint(logFile, "-----------------------------------------------\n");
  printZ3Node(t, ctxAssign);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "***********************************************\n");
#endif
  searchStart = 1;

  /* initialize random seed: */
  srand(time(NULL));

  Z3_theory_set_arith_new_eq_cb(t, cb_arith_new_eq);
}


/*
 *
 */
bool inline inContainIdxMap(Z3_ast node) {
  return containPairIdxMap.find(node) != containPairIdxMap.end();
}


Z3_ast collectEqNodes(Z3_theory t, Z3_ast n, std::set<Z3_ast> & eqcSet) {
  Z3_ast curr = n;
  Z3_ast constNode = NULL;
  do {
    if (isConstStr(t, curr)) {
      constNode = curr;
    }
    eqcSet.insert(curr);
    curr = Z3_theory_get_eqc_next(t, curr);
  } while (curr != n);
  return constNode;
}

/*
 *  varNode = constNode.
 *  The values of contains with varNode may be available based on the value of constNode.
 */
void checkContainByEqcVal(Z3_theory t, Z3_ast varNode, Z3_ast constNode) {
  std::vector<Z3_ast> litems;
  Z3_context ctx = Z3_theory_get_context(t);
  if (containPairIdxMap.find(varNode) != containPairIdxMap.end()) {
    std::set<std::pair<Z3_ast, Z3_ast> >::iterator itor1 = containPairIdxMap[varNode].begin();
    for (; itor1 != containPairIdxMap[varNode].end(); itor1++) {
      Z3_ast strAst = itor1->first;
      Z3_ast substrAst = itor1->second;
      Z3_ast boolVar = containPairBoolMap[*itor1];

#ifdef DEBUGLOG
      __debugPrint(logFile, "\n[checkContainByEqcVal] Contains(");
      printZ3Node(t, strAst);
      __debugPrint(logFile, ", ");
      printZ3Node(t, substrAst);
      __debugPrint(logFile, ") = ");
      printZ3Node(t, boolVar);
      __debugPrint(logFile, "\n");
#endif

      // varEqcNode is str
      if (strAst == varNode) {
        Z3_ast implyR = NULL;
        litems.clear();

        if (strAst != constNode) {
          litems.push_back(Z3_mk_eq(ctx, strAst, constNode));
        }
        bool subStrHasEqcValue = false;
        Z3_ast substrValue = get_eqc_value(t, substrAst, subStrHasEqcValue);
        if (substrValue != substrAst) {
          litems.push_back(Z3_mk_eq(ctx, substrAst, substrValue));
        }

        if (subStrHasEqcValue) {
          std::string strConst = getConstStrValue(t, constNode);
          std::string subStrConst = getConstStrValue(t, substrValue);

#ifdef DEBUGLOG
      __debugPrint(logFile, "\n strConst = %s\n", strConst.c_str());
      __debugPrint(logFile, "\n subStrConst = %s\n", subStrConst.c_str());
      __debugPrint(logFile, "\n");
#endif

          if (strConst.find(subStrConst) != std::string::npos) {
            implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
          } else {
            implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
          }
        }
        // add assertion
        if (implyR != NULL) {
          Z3_ast toAssert = NULL;
          if (litems.size() == 0) {
            toAssert = implyR;
          } else {
            toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems), implyR);
          }
          addAxiom(t, toAssert, __LINE__);
        }
      }
      // varEqcNode is subStr
      else if (substrAst == varNode){
        Z3_ast implyR = NULL;
        litems.clear();

        if (substrAst != constNode) {
          litems.push_back(Z3_mk_eq(ctx, substrAst, constNode));
        }
        bool strHasEqcValue = false;
        Z3_ast strValue = get_eqc_value(t, strAst, strHasEqcValue);
        if (strValue != strAst) {
          litems.push_back(Z3_mk_eq(ctx, strAst, strValue));
        }

        if (strHasEqcValue) {
          std::string strConst = getConstStrValue(t, strValue);
          std::string subStrConst = getConstStrValue(t, constNode);
          if (strConst.find(subStrConst) != std::string::npos) {
            implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
          } else {
            implyR = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
          }
        }

        // add assertion
        if (implyR != NULL) {
          Z3_ast toAssert = NULL;
          if (litems.size() == 0) {
            toAssert = implyR;
          } else {
            toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems), implyR);
          }
          addAxiom(t, toAssert, __LINE__);
        }
      }
    }
  }
}


/*
 *
 */
void checkContainByEqNodes(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  // n1 and n2 are supposed to be equal under current context
  // But at this moment, they may belong to two difference EQCs in context.
  if (inContainIdxMap(n1) && inContainIdxMap(n2)) {
    Z3_context ctx = Z3_theory_get_context(t);
    std::set<std::pair<Z3_ast, Z3_ast> >::iterator keysItor1 = containPairIdxMap[n1].begin();
    std::set<std::pair<Z3_ast, Z3_ast> >::iterator keysItor2;

    for (; keysItor1 != containPairIdxMap[n1].end(); keysItor1++) {
      // keysItor1 is on set {<.., n1>, ..., <n1, ...>, ...}
      std::pair<Z3_ast, Z3_ast> key1 = *keysItor1;
      if (key1.first == n1 && key1.second == n2) {
        Z3_ast implyL = NULL;
        Z3_ast implyR = Z3_mk_eq(ctx, containPairBoolMap[key1], Z3_mk_true(ctx));
        Z3_ast toAssert1 = NULL;
        if (n1 != n2) {
          implyL = Z3_mk_eq(ctx, n1, n2);
          toAssert1 = Z3_mk_implies(ctx, implyL, implyR);
        } else {
          toAssert1 = implyR;
        }
        addAxiom(t, toAssert1, __LINE__);
      }

      for (keysItor2 = containPairIdxMap[n2].begin(); keysItor2 != containPairIdxMap[n2].end(); keysItor2++) {
        // keysItor2 is on set {<.., n2>, ..., <n2, ...>, ...}
        std::pair<Z3_ast, Z3_ast> key2 = *keysItor2;
        // skip if the pair is eq
        if (key1 == key2) {
          continue;
        }

        // ***************************
        // Case 1: Contains(m, ...) /\ Contains(n, ) /\ m = n
        // ***************************
        if (key1.first == n1 && key2.first == n2) {
          Z3_ast subAst1 = key1.second;
          Z3_ast subAst2 = key2.second;
          bool subAst1HasValue = false;
          bool subAst2HasValue = false;
          Z3_ast subValue1 = get_eqc_value(t, subAst1, subAst1HasValue);
          Z3_ast subValue2 = get_eqc_value(t, subAst2, subAst2HasValue);

#ifdef DEBUGLOG
          __debugPrint(logFile, "\n[checkContainByEqNodes] Contains(");
          printZ3Node(t, n1);
          __debugPrint(logFile, ", ");
          printZ3Node(t, subAst1);
          __debugPrint(logFile, ") = ");
          printZ3Node(t, containPairBoolMap[key1]);
          __debugPrint(logFile, ", ");

          __debugPrint(logFile, " Contains(");
          printZ3Node(t, n2);
          __debugPrint(logFile, ", ");
          printZ3Node(t, subAst2);
          __debugPrint(logFile, ") = ");
          printZ3Node(t, containPairBoolMap[key2]);
          __debugPrint(logFile, "\n");

          if (subAst1 != subValue1) {
            __debugPrint(logFile, "       ");
            printZ3Node(t, subAst1);
            __debugPrint(logFile, " = ");
            printZ3Node(t, subValue1);
            __debugPrint(logFile, "\n");
          }

          if (subAst2 != subValue2) {
            __debugPrint(logFile, "       ");
            printZ3Node(t, subAst2);
            __debugPrint(logFile, " = ");
            printZ3Node(t, subValue2);
            __debugPrint(logFile, "\n");
          }
#endif

          if (subAst1HasValue && subAst2HasValue) {
            std::vector<Z3_ast> litems1;
            if (n1 != n2) {
              litems1.push_back(Z3_mk_eq(ctx, n1, n2));
            }
            if (subValue1 != subAst1) {
              litems1.push_back(Z3_mk_eq(ctx, subAst1, subValue1));
            }
            if (subValue2 != subAst2) {
              litems1.push_back(Z3_mk_eq(ctx, subAst2, subValue2));
            }

            std::string subConst1 = getConstStrValue(t, subValue1);
            std::string subConst2 = getConstStrValue(t, subValue2);
            Z3_ast implyR = NULL;
            if (subConst1 == subConst2) {
              // key1.first = key2.first /\ key1.second = key2.second
              // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
              implyR = Z3_mk_eq(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
            } else if (subConst1.find(subConst2) != std::string::npos) {
              // key1.first = key2.first /\ Contains(key1.second, key2.second)
              // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
              implyR = Z3_mk_implies(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
            } else if (subConst2.find(subConst1) != std::string::npos) {
              // key1.first = key2.first /\ Contains(key2.second, key1.second)
              // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
              implyR = Z3_mk_implies(ctx, containPairBoolMap[key2], containPairBoolMap[key1]);
            }

            if (implyR != NULL) {
              Z3_ast toAssert = NULL;
              if (litems1.size() == 0) {
                toAssert = implyR;
              } else {
                toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems1), implyR);
              }
              addAxiom(t, toAssert, __LINE__);
            }
          } else {
            std::set<Z3_ast> subAst1Eqc;
            std::set<Z3_ast> subAst2Eqc;
            collectEqNodes(t, subAst1, subAst1Eqc);
            collectEqNodes(t, subAst2, subAst2Eqc);

            if (subAst1Eqc.find(subAst2) != subAst1Eqc.end()) {
              // -----------------------------------------------------------
              // * key1.first = key2.first /\ key1.second = key2.second
              //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
              // -----------------------------------------------------------
              std::vector<Z3_ast> litems2;
              if (n1 != n2) {
                litems2.push_back(Z3_mk_eq(ctx, n1, n2));
              }
              if (subAst1 != subAst2) {
                litems2.push_back(Z3_mk_eq(ctx, subAst1, subAst2));
              }
              Z3_ast implyR = Z3_mk_eq(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
              Z3_ast toAssert = NULL;
              if (litems2.size() == 0) {
                toAssert = implyR;
              } else {
                toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems2), implyR);
              }
              addAxiom(t, toAssert, __LINE__);
            } else {
              // -----------------------------------------------------------
              // * key1.first = key2.first
              //   check eqc(key1.second) and eqc(key2.second)
              // -----------------------------------------------------------
              std::set<Z3_ast>::iterator eqItorSub1 = subAst1Eqc.begin();
              for (; eqItorSub1 != subAst1Eqc.end(); eqItorSub1++) {
                std::set<Z3_ast>::iterator eqItorSub2 = subAst2Eqc.begin();
                for (; eqItorSub2 != subAst2Eqc.end(); eqItorSub2++) {
                  // ------------
                  // key1.first = key2.first /\ containPairBoolMap[<eqc(key1.second), eqc(key2.second)>]
                  // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                  // ------------
                  {
                    std::vector<Z3_ast> litems3;
                    if (n1 != n2) {
                      litems3.push_back(Z3_mk_eq(ctx, n1, n2));
                    }
                    Z3_ast eqSubVar1 = * eqItorSub1;
                    if (eqSubVar1 != subAst1) {
                      litems3.push_back(Z3_mk_eq(ctx, subAst1, eqSubVar1));
                    }
                    Z3_ast eqSubVar2 = * eqItorSub2;
                    if (eqSubVar2 != subAst2) {
                      litems3.push_back(Z3_mk_eq(ctx, subAst2, eqSubVar2));
                    }
                    std::pair<Z3_ast, Z3_ast> tryKey1 = std::make_pair(eqSubVar1, eqSubVar2);
                    if (containPairBoolMap.find(tryKey1) != containPairBoolMap.end()) {
#ifdef DEBUGLOG
                      __debugPrint(logFile, "                        Contains(");
                      printZ3Node(t, eqSubVar1);
                      __debugPrint(logFile, ", ");
                      printZ3Node(t, eqSubVar2);
                      __debugPrint(logFile, ") = ");
                      printZ3Node(t, containPairBoolMap[tryKey1]);
                      __debugPrint(logFile, "\n");
#endif
                      litems3.push_back(containPairBoolMap[tryKey1]);
                      Z3_ast implR = Z3_mk_implies(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
                      Z3_ast toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems3), implR);
                      addAxiom(t, toAssert, __LINE__);
                    }
                  }
                  // ------------
                  // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                  // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                  // ------------
                  {
                    std::vector<Z3_ast> litems4;
                    if (n1 != n2) {
                      litems4.push_back(Z3_mk_eq(ctx, n1, n2));
                    }
                    Z3_ast eqSubVar1 = * eqItorSub1;
                    if (eqSubVar1 != subAst1) {
                      litems4.push_back(Z3_mk_eq(ctx, subAst1, eqSubVar1));
                    }
                    Z3_ast eqSubVar2 = * eqItorSub2;
                    if (eqSubVar2 != subAst2) {
                      litems4.push_back(Z3_mk_eq(ctx, subAst2, eqSubVar2));
                    }
                    std::pair<Z3_ast, Z3_ast> tryKey2 = std::make_pair(eqSubVar2, eqSubVar1);
                    if (containPairBoolMap.find(tryKey2) != containPairBoolMap.end()) {
#ifdef DEBUGLOG
                      __debugPrint(logFile, "                        Contains(");
                      printZ3Node(t, eqSubVar2);
                      __debugPrint(logFile, ", ");
                      printZ3Node(t, eqSubVar1);
                      __debugPrint(logFile, ") = ");
                      printZ3Node(t, containPairBoolMap[tryKey2]);
                      __debugPrint(logFile, "\n");
#endif
                      litems4.push_back(containPairBoolMap[tryKey2]);
                      Z3_ast implR = Z3_mk_implies(ctx, containPairBoolMap[key2], containPairBoolMap[key1]);
                      Z3_ast toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems4), implR);
                      addAxiom(t, toAssert, __LINE__);
                    }
                  }
                }
              }
            }
          }
        }
        // ***************************
        // Case 2: Contains(..., m) /\ Contains(... , n) /\ m = n
        // ***************************
        else if (key1.second == n1 && key2.second == n2) {
          Z3_ast str1 = key1.first;
          Z3_ast str2 = key2.first;
          bool str1HasValue = false;
          bool str2HasValue = false;
          Z3_ast strVal1 = get_eqc_value(t, str1, str1HasValue);
          Z3_ast strVal2 = get_eqc_value(t, str2, str2HasValue);

#ifdef DEBUGLOG
          __debugPrint(logFile, "\n[checkContainByEqNodes] Contains(");
          printZ3Node(t, str1);
          __debugPrint(logFile, ", ");
          printZ3Node(t, n1);
          __debugPrint(logFile, ") = ");
          printZ3Node(t, containPairBoolMap[key1]);
          __debugPrint(logFile, ", ");

          __debugPrint(logFile, " Contains(");
          printZ3Node(t, str2);
          __debugPrint(logFile, ", ");
          printZ3Node(t, n2);
          __debugPrint(logFile, ") = ");
          printZ3Node(t, containPairBoolMap[key2]);
          __debugPrint(logFile, "\n");

          if (str1 != strVal1) {
            __debugPrint(logFile, "       ");
            printZ3Node(t, str1);
            __debugPrint(logFile, " = ");
            printZ3Node(t, strVal1);
            __debugPrint(logFile, "\n");
          }

          if (str2 != strVal2) {
            __debugPrint(logFile, "       ");
            printZ3Node(t, str2);
            __debugPrint(logFile, " = ");
            printZ3Node(t, strVal2);
            __debugPrint(logFile, "\n");
          }
#endif

          if (str1HasValue && str2HasValue) {
            std::vector<Z3_ast> litems1;
            if (n1 != n2) {
              litems1.push_back(Z3_mk_eq(ctx, n1, n2));
            }
            if (strVal1 != str1) {
              litems1.push_back(Z3_mk_eq(ctx, str1, strVal1));
            }
            if (strVal2 != str2) {
              litems1.push_back(Z3_mk_eq(ctx, str2, strVal2));
            }

            std::string const1 = getConstStrValue(t, strVal1);
            std::string const2 = getConstStrValue(t, strVal2);
            Z3_ast implyR = NULL;

            if (const1 == const2) {
              // key1.second = key2.second /\ key1.first = key2.first
              // ==> (containPairBoolMap[key1] = containPairBoolMap[key2])
              implyR = Z3_mk_eq(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
            } else if (const1.find(const2) != std::string::npos) {
              // key1.second = key2.second /\ Contains(key1.first, key2.first)
              // ==> (containPairBoolMap[key2] --> containPairBoolMap[key1])
              implyR = Z3_mk_implies(ctx, containPairBoolMap[key2], containPairBoolMap[key1]);
            } else if (const2.find(const1) != std::string::npos) {
              // key1.first = key2.first /\ Contains(key2.first, key1.first)
              // ==> (containPairBoolMap[key1] --> containPairBoolMap[key2])
              implyR = Z3_mk_implies(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
            }

            if (implyR != NULL) {
              Z3_ast toAssert = NULL;
              if (litems1.size() == 0) {
                toAssert = implyR;
              } else {
                toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems1), implyR);
              }
              addAxiom(t, toAssert, __LINE__);
            }
          }


          else {
            std::set<Z3_ast> str1Eqc;
            std::set<Z3_ast> str2Eqc;
            collectEqNodes(t, str1, str1Eqc);
            collectEqNodes(t, str2, str2Eqc);

            if (str1Eqc.find(str2) != str1Eqc.end()) {
              // -----------------------------------------------------------
              // * key1.first = key2.first /\ key1.second = key2.second
              //   -->  containPairBoolMap[key1] = containPairBoolMap[key2]
              // -----------------------------------------------------------
              std::vector<Z3_ast> litems2;
              if (n1 != n2) {
                litems2.push_back(Z3_mk_eq(ctx, n1, n2));
              }
              if (str1 != str2) {
                litems2.push_back(Z3_mk_eq(ctx, str1, str2));
              }
              Z3_ast implyR = Z3_mk_eq(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
              Z3_ast toAssert = NULL;
              if (litems2.size() == 0) {
                toAssert = implyR;
              } else {
                toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems2), implyR);
              }
              addAxiom(t, toAssert, __LINE__);
            } else {
              // -----------------------------------------------------------
              // * key1.second = key2.second
              //   check eqc(key1.first) and eqc(key2.first)
              // -----------------------------------------------------------
              std::set<Z3_ast>::iterator eqItorStr1 = str1Eqc.begin();
              for (; eqItorStr1 != str1Eqc.end(); eqItorStr1++) {
                std::set<Z3_ast>::iterator eqItorStr2 = str2Eqc.begin();
                for (; eqItorStr2 != str2Eqc.end(); eqItorStr2++) {
                  {
                    std::vector<Z3_ast> litems3;
                    if (n1 != n2) {
                      litems3.push_back(Z3_mk_eq(ctx, n1, n2));
                    }
                    Z3_ast eqStrVar1 = *eqItorStr1;
                    if (eqStrVar1 != str1) {
                      litems3.push_back(Z3_mk_eq(ctx, str1, eqStrVar1));
                    }
                    Z3_ast eqStrVar2 = *eqItorStr2;
                    if (eqStrVar2 != str2) {
                      litems3.push_back(Z3_mk_eq(ctx, str2, eqStrVar2));
                    }
                    std::pair<Z3_ast, Z3_ast> tryKey1 = std::make_pair(eqStrVar1, eqStrVar2);
                    if (containPairBoolMap.find(tryKey1) != containPairBoolMap.end()) {
#ifdef DEBUGLOG
                      __debugPrint(logFile, "                        Contains(");
                      printZ3Node(t, eqStrVar1);
                      __debugPrint(logFile, ", ");
                      printZ3Node(t, eqStrVar2);
                      __debugPrint(logFile, ") = ");
                      printZ3Node(t, containPairBoolMap[tryKey1]);
                      __debugPrint(logFile, "\n");
#endif
                      litems3.push_back(containPairBoolMap[tryKey1]);

                      // ------------
                      // key1.second = key2.second /\ containPairBoolMap[<eqc(key1.first), eqc(key2.first)>]
                      // ==>  (containPairBoolMap[key2] --> containPairBoolMap[key1])
                      // ------------
                      Z3_ast implR = Z3_mk_implies(ctx, containPairBoolMap[key2], containPairBoolMap[key1]);
                      Z3_ast toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems3), implR);
                      addAxiom(t, toAssert, __LINE__);
                    }
                  }

                  {
                    std::vector<Z3_ast> litems4;
                    if (n1 != n2) {
                      litems4.push_back(Z3_mk_eq(ctx, n1, n2));
                    }
                    Z3_ast eqStrVar1 = *eqItorStr1;
                    if (eqStrVar1 != str1) {
                      litems4.push_back(Z3_mk_eq(ctx, str1, eqStrVar1));
                    }
                    Z3_ast eqStrVar2 = *eqItorStr2;
                    if (eqStrVar2 != str2) {
                      litems4.push_back(Z3_mk_eq(ctx, str2, eqStrVar2));
                    }
                    std::pair<Z3_ast, Z3_ast> tryKey2 = std::make_pair(eqStrVar2, eqStrVar1);
                    if (containPairBoolMap.find(tryKey2) != containPairBoolMap.end()) {
#ifdef DEBUGLOG
                      __debugPrint(logFile, "                        Contains(");
                      printZ3Node(t, eqStrVar2);
                      __debugPrint(logFile, ", ");
                      printZ3Node(t, eqStrVar1);
                      __debugPrint(logFile, ") = ");
                      printZ3Node(t, containPairBoolMap[tryKey2]);
                      __debugPrint(logFile, "\n");
#endif
                      litems4.push_back(containPairBoolMap[tryKey2]);
                      // ------------
                      // key1.first = key2.first /\ containPairBoolMap[<eqc(key2.second), eqc(key1.second)>]
                      // ==>  (containPairBoolMap[key1] --> containPairBoolMap[key2])
                      // ------------
                      Z3_ast implR = Z3_mk_implies(ctx, containPairBoolMap[key1], containPairBoolMap[key2]);
                      Z3_ast toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems4), implR);
                      addAxiom(t, toAssert, __LINE__);
                    }
                  }
                }
              }
            }
          }

        }
      }

      if (n1 == n2) {
        break;
      }
    }
  }
}


/*
 * When the core considers n1 and n2 are equal. Check contains
 */
void checkContainInNewEq(Z3_theory t, Z3_ast n1, Z3_ast n2) {
  if (containPairBoolMap.size() == 0) {
    return;
  }

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n*****\n>> Consistency check for contains\n");
#endif

  std::set<Z3_ast> willEqClass;
  Z3_ast constStrAst = NULL;
  // -----------------------------------------------------------------------
  // eqc of n1 and eqc of n2 are not merged when n1 and n2 are found equal.
  // So, put all eqc nodes together in "willEqClass"
  // -----------------------------------------------------------------------
  Z3_ast constStrAst_1 = collectEqNodes(t, n1, willEqClass);
  Z3_ast constStrAst_2 = collectEqNodes(t, n2, willEqClass);
  constStrAst = (constStrAst_1 != NULL) ? constStrAst_1 : constStrAst_2;

#ifdef DEBUGLOG
  __debugPrint(logFile, "\nwillEqClass = { ");
  std::set<Z3_ast>::iterator ititit = willEqClass.begin();
  for (; ititit != willEqClass.end(); ititit++) {
    printZ3Node(t, *ititit);
    __debugPrint(logFile, ", ");
  }
  __debugPrint(logFile, "}\n");
  __debugPrint(logFile, "constStrAst = ");
  printZ3Node(t, constStrAst);
  __debugPrint(logFile, "\n\n");
#endif

  // ------------------------------------------
  // step 1: we may have constant values for contain checks now
  // ------------------------------------------
  if (constStrAst != NULL) {
    std::set<Z3_ast>::iterator itAst = willEqClass.begin();
    for (; itAst != willEqClass.end(); itAst++) {
      if (*itAst == constStrAst) {
        continue;
      }
      checkContainByEqcVal(t, *itAst, constStrAst);
    }
  }

  // ------------------------------------------
  // step 2: check for b1 = contains(x, m), b2 = contains(y, n)
  //         (1) x = y /\ m = n  ==>  b1 = b2
  //         (2) x = y /\ Contains(const(m), const(n))  ==>  (b1 -> b2)
  //         (3) x = y /\ Contains(const(n), const(m))  ==>  (b2 -> b1)
  //         (4) x = y /\ containPairBoolMap[<eqc(m), eqc(n)>]  ==>  (b1 -> b2)
  //         (5) x = y /\ containPairBoolMap[<eqc(n), eqc(m)>]  ==>  (b2 -> b1)
  //         (6) Contains(const(x), const(y)) /\ m = n  ==>  (b2 -> b1)
  //         (7) Contains(const(y), const(x)) /\ m = n  ==>  (b1 -> b2)
  //         (8) containPairBoolMap[<eqc(x), eqc(y)>] /\ m = n  ==>  (b2 -> b1)
  //         (9) containPairBoolMap[<eqc(y), eqc(x)>] /\ m = n  ==>  (b1 -> b2)
  // ------------------------------------------
  std::set<Z3_ast>::iterator varItor1 = willEqClass.begin();
  for (; varItor1 != willEqClass.end(); varItor1++) {
    Z3_ast varAst1 = *varItor1;
    std::set<Z3_ast>::iterator varItor2 = varItor1;
    for (; varItor2 != willEqClass.end(); varItor2++) {
      Z3_ast varAst2 = *varItor2;
      checkContainByEqNodes(t, varAst1, varAst2);
    }
  }

#ifdef DEBUGLOG
  __debugPrint(logFile, "*****\n\n");
#endif
}

/*
 *
 */
void checkContain(Z3_theory t) {
  if (containPairBoolMap.size() == 0) {
    return;
  } else {
    Z3_context ctx = Z3_theory_get_context(t);
    std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast>::iterator itor = containPairBoolMap.begin();
    for (; itor != containPairBoolMap.end(); itor++) {
      Z3_ast boolVar = itor->second;
      Z3_ast strVar = (itor->first).first;
      Z3_ast subStrVar = (itor->first).second;

      bool strHasEqcValue = false;
      bool subStrHasEqcValue = false;
      Z3_ast strValue = get_eqc_value(t, strVar, strHasEqcValue);
      Z3_ast substrValue = get_eqc_value(t, subStrVar, subStrHasEqcValue);

#ifdef DEBUGLOG
      __debugPrint(logFile, "\n-----------------------------------\n");
      __debugPrint(logFile, " >> Contains(");
      printZ3Node(t, strVar);
      __debugPrint(logFile, ", ");
      printZ3Node(t, subStrVar);
      __debugPrint(logFile, ") = ");
      printZ3Node(t, boolVar);
      __debugPrint(logFile, "\n");

      if (strHasEqcValue) {
        __debugPrint(logFile, "     - ");
        printZ3Node(t, strVar);
        __debugPrint(logFile, " = ");
        printZ3Node(t, strValue);
        __debugPrint(logFile, "\n");
      }

      if (subStrHasEqcValue) {
        __debugPrint(logFile, "     - ");
        printZ3Node(t, subStrVar);
        __debugPrint(logFile, " = ");
        printZ3Node(t, substrValue);
        __debugPrint(logFile, "\n");
      }
      __debugPrint(logFile, "\n");
#endif

      // ---------
      // Step 1: both str and subStr have concrete eqc values
      if (strHasEqcValue && subStrHasEqcValue) {
        std::string strConst = getConstStrValue(t, strValue);
        std::string subStrConst = getConstStrValue(t, substrValue);
        Z3_ast r_imply = Z3_mk_eq(ctx, boolVar, Z3_mk_false(ctx));
        if (strConst.find(subStrConst) != std::string::npos) {
          r_imply = Z3_mk_eq(ctx, boolVar, Z3_mk_true(ctx));
        }
        std::vector<Z3_ast> litems;
        if (strValue != strVar)
          litems.push_back(Z3_mk_eq(ctx, strVar, strValue));
        if (substrValue != subStrVar)
          litems.push_back(Z3_mk_eq(ctx, subStrVar, substrValue));
        Z3_ast toAssert = NULL;
        if (litems.size() == 0) {
          toAssert = r_imply;
        } else {
          toAssert = Z3_mk_implies(ctx, mk_and_fromVector(t, litems), r_imply);
        }
        addAxiom(t, toAssert, __LINE__);
      }

      // ---------------------------------------
      // Step 2: Iterate the eqc class of <str, substr>:
      //         Say v1 = str or v2 = substr, if <v1, substr> or v2 = substr in containPairBoolMap,
      //         add containPairBoolMap[<str, substr>] = containPairBoolMap[v1, substr]
      //          or containPairBoolMap[<str, substr>] = containPairBoolMap[str, v2]
      // ---------------------------------------

      Z3_ast strVarEqc = Z3_theory_get_eqc_next(t, strVar);
      while (strVarEqc != strVar) {
        std::pair<Z3_ast, Z3_ast> key = std::make_pair(strVarEqc, subStrVar);
        if (containPairBoolMap.find(key) != containPairBoolMap.end()) {
          Z3_ast bVar2 = containPairBoolMap[key];
          Z3_ast implyL = Z3_mk_eq(ctx, strVar, strVarEqc);
          Z3_ast implyR = Z3_mk_eq(ctx, boolVar, bVar2);
          Z3_ast toAssert = Z3_mk_implies(ctx, implyL, implyR);
          addAxiom(t, toAssert, __LINE__);
        }
        strVarEqc = Z3_theory_get_eqc_next(t, strVarEqc);
      }

      Z3_ast subStrVarEqc = Z3_theory_get_eqc_next(t, subStrVar);
      while (subStrVarEqc != subStrVar) {
        std::pair<Z3_ast, Z3_ast> key = std::make_pair(strVar, subStrVarEqc);
        if (containPairBoolMap.find(key) != containPairBoolMap.end()) {
          Z3_ast bVar2 = containPairBoolMap[key];
          Z3_ast implyL = Z3_mk_eq(ctx, subStrVar, subStrVarEqc);
          Z3_ast implyR = Z3_mk_eq(ctx, boolVar, bVar2);
          Z3_ast toAssert = Z3_mk_implies(ctx, implyL, implyR);
          addAxiom(t, toAssert, __LINE__);
        }
        subStrVarEqc = Z3_theory_get_eqc_next(t, subStrVarEqc);
      }
    }
  }
}

/*
 *
 */
void cb_push(Z3_theory t) {
  sLevel++;
  __debugPrint(logFile, "\n*******************************************\n");
  __debugPrint(logFile, "[PUSH]: Level = %d", sLevel);
  __debugPrint(logFile, "\n*******************************************\n");
}

/*
 *
 */
void cb_reset(Z3_theory t) {
  __debugPrint(logFile, "\n** Reset():\n");
}

/*
 *
 */
void cb_restart(Z3_theory t) {
  __debugPrint(logFile, "\n** Restart():\n");
}

/*
 *
 */
void cb_new_relevant(Z3_theory t, Z3_ast n) {
  if (getNodeType(t, n) == my_Z3_Str_Var) {
    basicStrVarAxiom(t, n, __LINE__);
  }
}

/*
 *
 */
void cb_delete(Z3_theory t) {
  __debugPrint(logFile, "\n** Delete()\n");
  PATheoryData * td = (PATheoryData *) Z3_theory_get_ext_data(t);
  free(td);
}

/*
 *
 */
void display_symbol(Z3_context c, FILE * out, Z3_symbol s) {
  switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
      fprintf(out, "#%d", Z3_get_symbol_int(c, s));
      break;
    case Z3_STRING_SYMBOL:
      fprintf(out, "%s", Z3_get_symbol_string(c, s));
      break;
    default:
      break;
  }
}

/*
 *
 */
void display_sort(Z3_theory t, FILE * out, Z3_sort ty) {
  Z3_context c = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  switch (Z3_get_sort_kind(c, ty)) {
    case Z3_UNINTERPRETED_SORT: {
      display_symbol(c, out, Z3_get_sort_name(c, ty));
      break;
    }
    case Z3_BOOL_SORT: {
      fprintf(out, "bool");
      break;
    }
    case Z3_INT_SORT:
      fprintf(out, "int");
      break;
    case Z3_REAL_SORT: {
      fprintf(out, "real");
      break;
    }
    case Z3_BV_SORT: {
      fprintf(out, "bv%d", Z3_get_bv_sort_size(c, ty));
      break;
    }
    case Z3_ARRAY_SORT: {
      fprintf(out, "[");
      display_sort(t, out, Z3_get_array_sort_domain(c, ty));
      fprintf(out, "->");
      display_sort(t, out, Z3_get_array_sort_range(c, ty));
      fprintf(out, "]");
      break;
    }
    case Z3_DATATYPE_SORT: {
      if (Z3_get_datatype_sort_num_constructors(c, ty) != 1) {
        fprintf(out, "%s", Z3_sort_to_string(c, ty));
        break;
      }

      unsigned num_fields = Z3_get_tuple_sort_num_fields(c, ty);
      unsigned i;
      fprintf(out, "(");
      for (i = 0; i < num_fields; i++) {
        Z3_func_decl field = Z3_get_tuple_sort_field_decl(c, ty, i);
        if (i > 0) {
          fprintf(out, ", ");
        }
        display_sort(t, out, Z3_get_range(c, field));
      }
      fprintf(out, ")");
      break;
    }
    default: {
      if (ty == td->String) {
        fprintf(out, "string");
        break;
      } else if (ty == td->Regex) {
        fprintf(out, "regex");
        break;
      } else {
        fprintf(out, "unknown[");
        display_symbol(c, out, Z3_get_sort_name(c, ty));
        fprintf(out, "]");
      }
      break;
    }
  }
}

/*
 *
 */
void display_ast(Z3_theory t, FILE * out, Z3_ast v) {
  Z3_context c = Z3_theory_get_context(t);
  switch (Z3_get_ast_kind(c, v)) {
    case Z3_NUMERAL_AST: {
      fprintf(out, "%s", Z3_get_numeral_string(c, v));
      break;
    }
    case Z3_APP_AST: {
      if (getNodeType(t, v) == my_Z3_ConstStr) {
        std::string str = getConstStrValue(t, v);
        std::string escapedStr = "";
        for (unsigned int i = 0; i < str.length(); i++) {
          escapedStr = escapedStr + encodeToEscape(str[i]);
        }
        fprintf(out, "\"%s\"", escapedStr.c_str());
      } else {
        fprintf(out, "%s", Z3_ast_to_string(c, v));
      }
      break;
    }
    default: {
      fprintf(out, "> Error: Cannot print the value for %s\nExit.", Z3_ast_to_string(c, v));
      exit(0);
    }
  }
}

/*
 *
 */
void display_model(Z3_theory t, FILE * out, Z3_model m) {
  Z3_context c = Z3_theory_get_context(t);
  unsigned num_constants;
  unsigned i;

  num_constants = Z3_get_model_num_constants(c, m);
  for (i = 0; i < num_constants; i++) {
    Z3_func_decl cnst = Z3_get_model_constant(c, m, i);
    Z3_symbol name = Z3_get_decl_name(c, cnst);
    Z3_ast a = Z3_mk_app(c, cnst, 0, 0);
    Z3_ast v = a;
    Z3_eval(c, m, a, &v);
    Z3_sort v_sort = Z3_get_sort(c, v);

    display_symbol(c, out, name);
    fprintf(out, " : ");
    display_sort(t, out, v_sort);

    fprintf(out, " -> ");
    display_ast(t, out, v);
    fprintf(out, "\n");
  }
}

/*
 *
 */
int check(Z3_theory t) {
  int isSAT = -1;
  Z3_model m = 0;
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_lbool result = Z3_check_and_get_model(ctx, &m);
  __debugPrint(logFile, "\n*****************************\n");
  printf("************************\n>> ");

  switch (result) {
    case Z3_L_FALSE: {
      isSAT = -1;
      if (loopDetected) {
        printf("UNKNOWN\n");
        __debugPrint(logFile, "UNKNOWN\n");
      } else {
        printf("UNSAT\n");
        __debugPrint(logFile, "UNSAT\n");
      }
      break;
    }
    case Z3_L_UNDEF: {
      isSAT = 0;
      __debugPrint(logFile, "UNKNOWN\n ");
      __debugPrint(logFile, "POSSIBLE MODEL:\n");
      __debugPrint(logFile, "-----------------------------\n");
      __debugPrint(logFile, "%s", Z3_model_to_string(ctx, m));
      printf("UNKNOWN\n");
      printf("POSSIBLE MODEL:\n");
      printf("------------------------\n");
      printf("%s", Z3_model_to_string(ctx, m));
      break;
    }
    case Z3_L_TRUE: {
      isSAT = 1;
      std::string modelStr = std::string(Z3_model_to_string(ctx, m));
      __debugPrint(logFile, "SAT\n");
      __debugPrint(logFile, "-----------------------------\n");
      __debugPrint(logFile, "%s", modelStr.c_str());
      printf("SAT\n");
      printf("------------------------\n");
      display_model(t, stdout, m);
      break;
    }
  }
  __debugPrint(logFile, "*****************************\n");
  printf("************************\n");

  if (m)
    Z3_del_model(ctx, m);

  return isSAT;
}

/*
 *Procedural attachment theory example.
 */
Z3_theory mk_pa_theory(Z3_context ctx) {
  PATheoryData * td = (PATheoryData *) malloc(sizeof(PATheoryData));
  Z3_theory Th = Z3_mk_theory(ctx, "StringAttachment", td);
  Z3_sort BoolSort = Z3_mk_bool_sort(ctx);
  Z3_sort IntSort = Z3_mk_int_sort(ctx);
  Z3_symbol string_name = Z3_mk_string_symbol(ctx, "String");
  td->String = Z3_theory_mk_sort(ctx, Th, string_name);

  Z3_symbol regexSort_name = Z3_mk_string_symbol(ctx, "Regex");
  td->Regex = Z3_theory_mk_sort(ctx, Th, regexSort_name);

  Z3_symbol concat_name = Z3_mk_string_symbol(ctx, "Concat");
  Z3_sort concat_domain[2];
  concat_domain[0] = td->String;
  concat_domain[1] = td->String;
  td->Concat = Z3_theory_mk_func_decl(ctx, Th, concat_name, 2, concat_domain, td->String);
  //---------------------------
  Z3_symbol length_name = Z3_mk_string_symbol(ctx, "Length");
  Z3_sort length_domain[1];
  length_domain[0] = td->String;
  td->Length = Z3_theory_mk_func_decl(ctx, Th, length_name, 1, length_domain, IntSort);
  //---------------------------
  Z3_symbol substring_name = Z3_mk_string_symbol(ctx, "Substring");
  Z3_sort substring_domain[3];
  substring_domain[0] = td->String;
  substring_domain[1] = IntSort;
  substring_domain[2] = IntSort;
  td->SubString = Z3_theory_mk_func_decl(ctx, Th, substring_name, 3, substring_domain, td->String);
  //---------------------------
  Z3_symbol indexof_name = Z3_mk_string_symbol(ctx, "Indexof");
  Z3_sort indexof_domain[2];
  indexof_domain[0] = td->String;
  indexof_domain[1] = td->String;
  td->Indexof = Z3_theory_mk_func_decl(ctx, Th, indexof_name, 2, indexof_domain, IntSort);
  //---------------------------
  Z3_symbol indexof2_name = Z3_mk_string_symbol(ctx, "Indexof2");
  Z3_sort indexof2_domain[3];
  indexof2_domain[0] = td->String;
  indexof2_domain[1] = td->String;
  indexof2_domain[2] = IntSort;
  td->Indexof2 = Z3_theory_mk_func_decl(ctx, Th, indexof2_name, 3, indexof2_domain, IntSort);
  //---------------------------
  Z3_symbol contains_name = Z3_mk_string_symbol(ctx, "Contains");
  Z3_sort contains_domain[2];
  contains_domain[0] = td->String;
  contains_domain[1] = td->String;
  td->Contains = Z3_theory_mk_func_decl(ctx, Th, contains_name, 2, contains_domain, BoolSort);
  //---------------------------
  Z3_symbol startsWith_name = Z3_mk_string_symbol(ctx, "StartsWith");
  Z3_sort startsWith_domain[2];
  startsWith_domain[0] = td->String;
  startsWith_domain[1] = td->String;
  td->StartsWith = Z3_theory_mk_func_decl(ctx, Th, startsWith_name, 2, startsWith_domain, BoolSort);
  //---------------------------
  Z3_symbol endsWith_name = Z3_mk_string_symbol(ctx, "EndsWith");
  Z3_sort endsWith_domain[2];
  endsWith_domain[0] = td->String;
  endsWith_domain[1] = td->String;
  td->EndsWith = Z3_theory_mk_func_decl(ctx, Th, endsWith_name, 2, endsWith_domain, BoolSort);
  //---------------------------
  Z3_symbol replace_name = Z3_mk_string_symbol(ctx, "Replace");
  Z3_sort replace_domain[3];
  replace_domain[0] = td->String;
  replace_domain[1] = td->String;
  replace_domain[2] = td->String;
  td->Replace = Z3_theory_mk_func_decl(ctx, Th, replace_name, 3, replace_domain, td->String);
  //---------------------------
  Z3_symbol lastIndexof_name = Z3_mk_string_symbol(ctx, "LastIndexof");
  Z3_sort lastIndexof_domain[2];
  lastIndexof_domain[0] = td->String;
  lastIndexof_domain[1] = td->String;
  td->LastIndexof = Z3_theory_mk_func_decl(ctx, Th, lastIndexof_name, 2, lastIndexof_domain, IntSort);
  //---------------------------
  Z3_symbol charAt_name = Z3_mk_string_symbol(ctx, "CharAt");
  Z3_sort charAt_domain[2];
  charAt_domain[0] = td->String;
  charAt_domain[1] = IntSort;
  td->CharAt = Z3_theory_mk_func_decl(ctx, Th, charAt_name, 2, charAt_domain, td->String);
  //---------------------------

  //===========================
  // Str2Reg := String --> Regex
  Z3_symbol str2Reg_name = Z3_mk_string_symbol(ctx, "Str2Reg");
  Z3_sort str2Reg_domain[1];
  str2Reg_domain[0] = td->String;
  td->Str2Reg = Z3_theory_mk_func_decl(ctx, Th, str2Reg_name, 1, str2Reg_domain, td->Regex);
  //---------------------------
  // RegexStar := Regex --> Regex
  Z3_symbol regexStar_name = Z3_mk_string_symbol(ctx, "RegexStar");
  Z3_sort regexStar_domain[1];
  regexStar_domain[0] = td->Regex;
  td->RegexStar = Z3_theory_mk_func_decl(ctx, Th, regexStar_name, 1, regexStar_domain, td->Regex);
  //---------------------------
  // RegexIn := String x Regex --> Bool
  Z3_symbol regexIn_name = Z3_mk_string_symbol(ctx, "RegexIn");
  Z3_sort regexIn_domain[2];
  regexIn_domain[0] = td->String;
  regexIn_domain[1] = td->Regex;
  td->RegexIn = Z3_theory_mk_func_decl(ctx, Th, regexIn_name, 2, regexIn_domain, BoolSort);
  //---------------------------
  // RegexUnion := Regex x Regex --> Regex
  Z3_symbol regexUnion_name = Z3_mk_string_symbol(ctx, "RegexUnion");
  Z3_sort regexUnion_domain[2];
  regexUnion_domain[0] = td->Regex;
  regexUnion_domain[1] = td->Regex;
  td->RegexUnion = Z3_theory_mk_func_decl(ctx, Th, regexUnion_name, 2, regexUnion_domain, td->Regex);
  //---------------------------
  // RegexConcat := Regex x Regex --> Regex
  Z3_symbol regexConcat_name = Z3_mk_string_symbol(ctx, "RegexConcat");
  Z3_sort regexConcat_domain[2];
  regexConcat_domain[0] = td->Regex;
  regexConcat_domain[1] = td->Regex;
  td->RegexConcat = Z3_theory_mk_func_decl(ctx, Th, regexConcat_name, 2, regexConcat_domain, td->Regex);
  //---------------------------
  // Unroll := String x Int --> String
  Z3_symbol unrollFunc_name = Z3_mk_string_symbol(ctx, "Unroll");
  Z3_sort unrollFunc_domain[2];
  unrollFunc_domain[0] = td->Regex;
  unrollFunc_domain[1] = IntSort;
  td->Unroll = Z3_theory_mk_func_decl(ctx, Th, unrollFunc_name, 2, unrollFunc_domain, td->String);
  //---------------------------
  Z3_symbol regexDigit_name = Z3_mk_string_symbol(ctx, "RegexDigit");
  Z3_sort regexDigit_domain[1];
  regexDigit_domain[0] = td->String;
  td->RegexDigit = Z3_theory_mk_func_decl(ctx, Th, regexDigit_name, 1, regexDigit_domain, td->Regex);
  //---------------------------


  Z3_set_delete_callback(Th, cb_delete);
  Z3_set_new_eq_callback(Th, cb_new_eq);
  Z3_set_final_check_callback(Th, cb_final_check);
  Z3_set_init_search_callback(Th, cb_init_search);
  Z3_set_push_callback(Th, cb_push);
  Z3_set_pop_callback(Th, cb_pop);
  Z3_set_reset_callback(Th, cb_reset);
  Z3_set_restart_callback(Th, cb_restart);
  Z3_set_new_relevant_callback(Th, cb_new_relevant);
  Z3_set_reduce_eq_callback(Th, cb_reduce_eq);
  Z3_set_reduce_app_callback(Th, cb_reduce_app);

  return Th;
}

/*
 *
 */
void throw_z3_error(Z3_context ctx, Z3_error_code c) {
}

/*
 *
 */
Z3_context mk_context_custom(Z3_config cfg) {
  Z3_context ctx;
  Z3_set_param_value(cfg, "MODEL", "true");
  ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, throw_z3_error);
  return ctx;
}

/*
 *
 */
Z3_context mk_my_context() {
  Z3_config cfg = Z3_mk_config();
  Z3_context ctx;
  ctx = mk_context_custom(cfg);
  Z3_del_config(cfg);
  return ctx;
}

/*
 *
 */
void pa_theory_example() {
  if (inputFile == "") {
    printf("No input file is provided.\n");
    return;
  }
  Z3_context ctx = mk_my_context();
  Z3_theory Th = mk_pa_theory(ctx);
  ctx = Z3_theory_get_context(Th);
  setAlphabet();

  // load cstr from inputFile
  Z3_ast fs = Z3_parse_smtlib2_file(ctx, inputFile.c_str(), 0, 0, 0, 0, 0, 0);

  // check input variable. Stop if invalid stuffs are found
  checkInputVar(Th, fs);

  emptyConstStr = my_mk_str_value(Th, "");

  __debugPrint(logFile, "Input Var Set\n***********************************************\n");
  for (std::map<Z3_ast, int>::iterator it = inputVarMap.begin(); it != inputVarMap.end(); it++) {
    printZ3Node(Th, it->first);
    __debugPrint(logFile, "\n");
    basicStrVarAxiom(Th, it->first, __LINE__);
  }
  __debugPrint(logFile, "\n\n");

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n***********************************************\nInput loaded:\n-----------------------------------------------\n");
  printZ3Node(Th, fs);
  __debugPrint(logFile, "\n-----------------------------------------------\n\n");
#endif

  Z3_assert_cnstr(ctx, fs);
  check(Th);

  // clean up
  Z3_del_context(ctx);
}

