#ifndef __strTheory_H
#define __strTheory_H 1

#include <stdio.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>
#include <memory.h>
#include <unistd.h>
#include <assert.h>
#include <map>
#include <set>
#include <list>
#include <vector>
#include <stack>
#include <string>
#include <sstream>
#include <algorithm>
#include <getopt.h>
#include <utility>
#include <limits.h>
#include <regex>


#include "z3.h"

#ifdef DEBUGLOG
  #define __debugPrint(_fp, _format, ...) { fprintf( (_fp), (_format), ##__VA_ARGS__); fflush( (_fp) ); }
  #define printZ3Node(t, n) {__printZ3Node( (t), (n));}
#else
  #define __debugPrint(_fp, _format, ...) {}
  #define printZ3Node(t, n) {}
#endif


//#define tmpLog(_format, ...) { fprintf(stdout, (_format), ##__VA_ARGS__); }
//#define logAst(t, n) {fprintf(stdout, "%s", Z3_ast_to_string(Z3_theory_get_context(t), n));}
//#define tmpLog(_format, ...) { }
//#define logAst(t, n) { }

#define lcmUnrollStep 2

extern char * charSet;
extern int charSetSize;
extern const std::string escapeDict[];
extern bool avoidLoopCut;
extern FILE * logFile;
extern std::string inputFile;
extern int sLevel;
extern bool loopDetected;


extern std::map<char, int> charSetLookupTable;

//key: pair<str, substr>, value: boolVar
extern std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> containPairBoolMap;

//key: pair<strVar, string>, value: boolVar
extern std::map<std::pair<Z3_ast, std::string>, Z3_ast> regexInBoolMap;
extern std::map<Z3_ast, std::set<std::string> > regexInVarRegStrMap;

extern std::map<std::pair<Z3_ast, Z3_ast>, std::map<int, Z3_ast> > varForBreakConcat;

extern std::set<Z3_ast> inputVarInLen;
//--------------------------------------------------

/**
 * Theory specific data-structures.
 */
typedef struct _PATheoryData
{
    Z3_sort String;
    Z3_sort Regex;

    Z3_func_decl Concat;
    Z3_func_decl Length;
    Z3_func_decl SubString;
    Z3_func_decl Indexof;
    Z3_func_decl Indexof2;
    Z3_func_decl StartsWith;
    Z3_func_decl EndsWith;
    Z3_func_decl Contains;
    Z3_func_decl Replace;
    Z3_func_decl LastIndexof;
    Z3_func_decl CharAt;

    Z3_func_decl Str2Reg;
    Z3_func_decl RegexStar;
    Z3_func_decl RegexPlus;
    Z3_func_decl RegexCharRange;
    Z3_func_decl RegexIn;
    Z3_func_decl RegexUnion;
    Z3_func_decl RegexConcat;
    Z3_func_decl Unroll;
} PATheoryData;


typedef enum
{
  my_Z3_ConstStr,    // 0
  my_Z3_ConstBool,   // 1
  my_Z3_Func,        // 2
  my_Z3_Num,         // 3
  my_Z3_Var,         // 4, boolean, bv, int varables
  my_Z3_Str_Var,     // 5
  my_Z3_Regex_Var,   // 8
  my_Z3_Quantifier,  // 7
  my_Z3_Unknown      // 9
} T_myZ3Type;

//--------------------------------------------------
// Function Declaration
//--------------------------------------------------
void setAlphabet();

std::string intToString(int i);

Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty);

Z3_ast mk_bool_var(Z3_context ctx, const char * name);

Z3_ast mk_int_var(Z3_context ctx, const char * name);

Z3_ast mk_int(Z3_context ctx, int v);

Z3_ast my_mk_str_value(Z3_theory t, char const * str);

Z3_ast my_mk_str_var(Z3_theory t, char const * name);

Z3_ast my_mk_internal_string_var(Z3_theory t);

Z3_ast my_mk_nonEmpty_string_var(Z3_theory t);

Z3_ast my_mk_internal_int_var(Z3_theory t);

Z3_ast my_mk_internal_bool_var(Z3_theory t);

Z3_ast mk_internal_xor_var(Z3_theory t);

Z3_ast mk_unrollBoundVar(Z3_theory t);

Z3_ast mk_regexRepVar(Z3_theory t);

Z3_ast mk_1_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x);

Z3_ast mk_2_arg_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y);

Z3_ast my_mk_and(Z3_theory t, Z3_ast * item, int count);

Z3_ast mk_2_and(Z3_theory t, Z3_ast and1, Z3_ast and2);

Z3_ast mk_2_or(Z3_theory t, Z3_ast and1, Z3_ast and2);

Z3_ast mk_2_sub(Z3_theory t, Z3_ast ast1, Z3_ast ast2);

Z3_ast mk_2_add(Z3_theory t, Z3_ast ast1, Z3_ast ast2);

Z3_ast mk_and_fromVector(Z3_theory t, std::vector<Z3_ast> & vec);

Z3_ast mk_or_fromVector(Z3_theory t, std::vector<Z3_ast> & vec);

Z3_ast mk_length(Z3_theory t, Z3_ast n);

Z3_ast mk_unroll(Z3_theory t, Z3_ast n, Z3_ast bound);

Z3_ast mk_contains(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_ast mk_concat(Z3_theory t, Z3_ast n1, Z3_ast n2);


void print_eq_class(Z3_theory t, Z3_ast n);

void __printZ3Node(Z3_theory t, Z3_ast node);

void print_All_Eqc(Z3_theory t);

void printStrArgLen(Z3_theory t, Z3_ast node, int ll = 0);


bool isConcatFunc(Z3_theory t, Z3_ast n);

bool isConstStr(Z3_theory t, Z3_ast node);

bool isUnrollFunc(Z3_theory t, Z3_ast n);

bool isRegexStar(Z3_theory t, Z3_ast n);

bool isStr2Regex(Z3_theory t, Z3_ast n);

bool isRegexIn(Z3_theory t, Z3_ast n);

bool isRegexUnion(Z3_theory t, Z3_ast n);

bool isRegexConcat(Z3_theory t, Z3_ast n);

Z3_ast genLenValOptionsForFreeVar(Z3_theory t, Z3_ast freeVar, Z3_ast lenTesterInCbEq, std::string lenTesterValue);

Z3_ast genFreeVarOptions(Z3_theory t, Z3_ast freeVar, Z3_ast len_indicator, std::string len_valueStr, Z3_ast valTesterInCbEq,
    std::string valTesterValueStr);

T_myZ3Type getNodeType(Z3_theory t, Z3_ast n);

Z3_ast get_eqc_value(Z3_theory t, Z3_ast n, bool & hasEqcValue);

Z3_ast get_eqc_unrollFunc(Z3_theory t, Z3_ast n);

std::string getConstStrValue(Z3_theory t, Z3_ast n);

int getConstIntValue(Z3_theory t, Z3_ast n);

int getLenValue(Z3_theory t, Z3_ast n);

int getIntValue(Z3_theory t, Z3_ast n, bool & hasValue);

void checkandInit_cutVAR(Z3_theory t, Z3_ast node);

Z3_ast registerContain(Z3_theory t, Z3_ast str, Z3_ast subStr);

Z3_ast Concat(Z3_theory t, Z3_ast n1, Z3_ast n2);

void solve_concat_eq_str(Z3_theory t, Z3_ast concatAst, Z3_ast constStr);

void getconstStrAstsInNode(Z3_theory t, Z3_ast node, std::list<Z3_ast> & astList);

bool inSameEqc(Z3_theory t, Z3_ast n1, Z3_ast n2);

bool canTwoNodesEq(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_ast simplifyConcat(Z3_theory t, Z3_ast node);

void simplifyConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2, int duplicateCheck = 1);

void processUnrollEqConstStr(Z3_theory t, Z3_ast unrollFunc, Z3_ast eqcStr);

void processConcatEqUnroll(Z3_theory t, Z3_ast concat, Z3_ast unroll);

int newEqCheck(Z3_theory t, Z3_ast nn1, Z3_ast nn2);

void getConcatsInEqc(Z3_theory t, Z3_ast n, std::set<Z3_ast> & concats);

void new_eq_handler(Z3_theory t, Z3_ast nn1, Z3_ast nn2);

void cb_new_eq(Z3_theory t, Z3_ast n1, Z3_ast n2);

int haveEQLength(Z3_theory t, Z3_ast n1, Z3_ast n2);

Z3_bool cb_final_check(Z3_theory t);

std::string encodeToEscape(char c);

Z3_bool cb_reduce_eq(Z3_theory t, Z3_ast s_1, Z3_ast s_2, Z3_ast * r);

void checkInputVar(Z3_theory t, Z3_ast node);

Z3_ast collectEqNodes(Z3_theory t, Z3_ast n, std::set<Z3_ast> & eqcSet);

void cb_init_search(Z3_theory t);

Z3_bool cb_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const * args, Z3_ast * result);

void cb_push(Z3_theory t);

void cb_pop(Z3_theory t);

void cb_reset(Z3_theory t);

void cb_restart(Z3_theory t);

void cb_new_relevant(Z3_theory t, Z3_ast n);

void cb_delete(Z3_theory t);

int check(Z3_theory t);

Z3_theory mk_pa_theory(Z3_context ctx);

void throw_z3_error(Z3_context ctx, Z3_error_code c);

Z3_context mk_context_custom(Z3_config cfg);

Z3_context mk_my_context();

void classifyAstByType(Z3_theory t, Z3_ast node, std::map<Z3_ast, int> & varMap, std::map<Z3_ast, int> & concatMap, std::map<Z3_ast, int> & unrollMap);

void basicConcatAxiom(Z3_theory t, Z3_ast vNode, int line);

void getNodesInConcat(Z3_theory t, Z3_ast node, std::vector<Z3_ast> & nodeList);

Z3_ast getMostLeftNodeInConcat(Z3_theory t, Z3_ast node);

Z3_ast getMostRightNodeInConcat(Z3_theory t, Z3_ast node);

int ctxDepAnalysis(Z3_theory t, std::map<Z3_ast, int> & strVarMap, std::map<Z3_ast, int> & freeVarMap, std::map<Z3_ast, std::set<Z3_ast> > & unrollGroupMap);

Z3_ast mk_length(Z3_theory t, Z3_ast n);

void strEqLengthAxiom(Z3_theory t, Z3_ast varAst, Z3_ast strAst, int line);

void inferLenConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2);

void addAxiom(Z3_theory t, Z3_ast toAssert, int line, bool display = true);

void basicStrVarAxiom(Z3_theory t, Z3_ast vNode, int line);

void nonEmptyStrVarAxiom(Z3_theory t, Z3_ast vNode, int line);

void simplifyParent(Z3_theory t, Z3_ast nn, Z3_ast eq_str);

int canConcatEqStr(Z3_theory t, Z3_ast concat, std::string str);

int canConcatEqConcat(Z3_theory t, Z3_ast concat1, Z3_ast concat2);

void checkContainInNewEq(Z3_theory t, Z3_ast n1, Z3_ast n2);

void pa_theory_example();

bool consistCheckRegex(Z3_theory t, Z3_ast nn1, Z3_ast nn2);

void get_eqc_simpleUnroll(Z3_theory t, Z3_ast n, Z3_ast & constStr, std::set<Z3_ast> & unrollFuncSet);

void get_eqc_allUnroll(Z3_theory t, Z3_ast n, Z3_ast & constStr, std::set<Z3_ast> & unrollFuncSet);

std::string getStdRegexStr(Z3_theory t, Z3_ast regex);

Z3_ast genAssignUnrollStr2Reg(Z3_theory t, Z3_ast n, std::set<Z3_ast> & unrolls);

int getIntValue(Z3_theory t, Z3_ast n, bool & hasValue);

void genAssignUnrollReg(Z3_theory t, std::set<Z3_ast> & unrolls);

#endif

