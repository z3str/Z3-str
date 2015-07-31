#include "strTheory.h"


int tmpRegexDenoteVarCount = 0;
int unrollTesterVarCount = 0;


std::map<Z3_ast, Z3_ast> unrollVarMap;
// std::set is an ordered container, so it can be used as the key
std::map<Z3_ast, std::map<std::set<Z3_ast>, std::vector<Z3_ast> > > unrollTriesMap;
std::map<std::pair<Z3_ast, Z3_ast>, Z3_ast> concatEqUnroll_AstMap;

std::map<Z3_ast, std::set<std::string> > regexInVarRegStrMap;
std::map<std::pair<Z3_ast, std::string>, Z3_ast> regexInBoolMap;


/*
 *
 */
Z3_ast mk_regexRepVar(Z3_theory t) {
  std::stringstream ss;
  ss << tmpRegexDenoteVarCount;
  tmpRegexDenoteVarCount++;
  std::string name = "$$_regVar_" + ss.str();
  return my_mk_str_var(t, name.c_str());
}


/*
 *
 */
std::string str2RegexStr(std::string str) {
  std::string res = "";
  int len = str.size();
  for (int i = 0; i < len; i++) {
    char nc = str[i];
    // 12 special chars
    if (nc == '\\' || nc == '^' || nc == '$' || nc == '.' || nc == '|' || nc == '?'
        || nc == '*' || nc == '+' || nc == '(' || nc == ')' || nc == '[' || nc == '{') {
      res.append(1, '\\');
    }
    res.append(1, str[i]);
  }
  return res;
}


/*
 * Collect simple unroll functions (the core is str2Reg)
 * and constant string in eqc of node n
 */
void get_eqc_simpleUnroll(Z3_theory t, Z3_ast n, Z3_ast & constStr, std::set<Z3_ast> & unrollFuncSet) {
  constStr = NULL;
  unrollFuncSet.clear();
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

  Z3_ast curr = n;
  do {
    if (isConstStr(t, curr)) {
      constStr = curr;
    } else if (td->Unroll == Z3_get_app_decl(ctx, Z3_to_app(ctx, curr))) {
      Z3_ast core = Z3_get_app_arg(ctx, Z3_to_app(ctx, curr), 0);
      if (Z3_get_app_decl(ctx, Z3_to_app(ctx, core)) == td->Str2Reg) {
        if (unrollFuncSet.find(curr) == unrollFuncSet.end()) {
          unrollFuncSet.insert(curr);
        }
      }
    }
    curr = Z3_theory_get_eqc_next(t, curr);
  } while (curr != n);
}


/*
 * Collect all unroll functions
 * and constant string in eqc of node n
 */
void get_eqc_allUnroll(Z3_theory t, Z3_ast n, Z3_ast & constStr, std::set<Z3_ast> & unrollFuncSet) {
  constStr = NULL;
  unrollFuncSet.clear();
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

  Z3_ast curr = n;
  do {
    if (isConstStr(t, curr)) {
      constStr = curr;
    } else if (td->Unroll == Z3_get_app_decl(ctx, Z3_to_app(ctx, curr))) {
      if (unrollFuncSet.find(curr) == unrollFuncSet.end()) {
        unrollFuncSet.insert(curr);
      }
    }
    curr = Z3_theory_get_eqc_next(t, curr);
  } while (curr != n);
}


/*
 *
 */
std::string getStdRegexStr(Z3_theory t, Z3_ast regex) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl regexFuncDecl = Z3_get_app_decl(ctx, Z3_to_app(ctx, regex));
  if (regexFuncDecl == td->Str2Reg) {
    Z3_ast regAst = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    std::string regStr = str2RegexStr(getConstStrValue(t, regAst));
    return regStr;
  } else if (regexFuncDecl == td->RegexConcat) {
    Z3_ast reg1Ast = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    Z3_ast reg2Ast = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 1);
    std::string reg1Str = getStdRegexStr(t, reg1Ast);
    std::string reg2Str = getStdRegexStr(t, reg2Ast);
    return "(" + reg1Str + ")(" + reg2Str + ")";
  } else if (regexFuncDecl == td->RegexUnion) {
    Z3_ast reg1Ast = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    Z3_ast reg2Ast = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 1);
    std::string reg1Str = getStdRegexStr(t, reg1Ast);
    std::string reg2Str = getStdRegexStr(t, reg2Ast);
    return  "(" + reg1Str + ")|(" + reg2Str + ")";
  } else if (regexFuncDecl == td->RegexStar) {
    Z3_ast reg1Ast = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    std::string reg1Str = getStdRegexStr(t, reg1Ast);
    return  "(" + reg1Str + ")*";
  } else {
    printf("> Error: unexpected regex operation.\n");
    __debugPrint(logFile, ">> Error: unexpected regex operation.\n");
    __debugPrint(logFile, "   * [regex] ");
    printZ3Node(t, regex);
    __debugPrint(logFile, "\n");
    exit(0);
  }
}


/*
 *
 */
bool checkSimpleUnroll2eqLen(Z3_theory t, Z3_ast unrollFunc, int eqLen) {
  // "eqLen = -1" means length info is not available
  if (eqLen <= 0)
    return true;
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  if (Z3_get_app_decl(ctx, Z3_to_app(ctx, unrollFunc)) != td->Unroll)
    return true;
  Z3_ast str2RexFunc = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrollFunc), 0);
  if (Z3_get_app_decl(ctx, Z3_to_app(ctx, str2RexFunc)) != td->Str2Reg)
    return true;

#ifdef DEBUGLOG
  __debugPrint(logFile, ">> Unroll Function Consistency Check |UnrollFunc| = length? :\n");
  __debugPrint(logFile, "   - [unroll] ");
  printZ3Node(t, unrollFunc);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "   - [eqLen] %d\n", eqLen);
#endif

  std::string coreValue = getConstStrValue(t, Z3_get_app_arg(ctx, Z3_to_app(ctx, str2RexFunc), 0));
  Z3_ast toNegate = NULL;

  // -------------------------------------
  // check length
  // -------------------------------------
  int coreLen = coreValue.length();
  if (eqLen % coreLen != 0){
#ifdef DEBUGLOG
    __debugPrint(logFile, "   > [Inconsistent] Lengths is infeasible.\n");
    __debugPrint(logFile, "   *** NEGATE ***\n\n");
#endif
    toNegate = Z3_mk_not(ctx, Z3_mk_eq(ctx, mk_length(t, unrollFunc), mk_int(ctx, eqLen)));
    addAxiom(t, toNegate, __LINE__);
    return false;
  }
  return true;
}




int computeGCD(int x, int y) {
  if (x == 0) {
    return y;
  }
  while (y != 0) {
    if (x > y) {
      x = x - y;
    } else {
      y = y - x;
    }
  }
  return x;
}


int computeLCM(int a, int b) {
  int temp = computeGCD(a, b);
  return temp ? (a / temp * b) : 0;
}


std::string getUnrolledString(std::string core, int count) {
  std::string res = "";
  for (int i = 0; i < count; i++) {
    res += core;
  }
  return res;
}


/*
 *
 */
bool checkUnroll2ConstStr(Z3_theory t, Z3_ast unrollFunc, Z3_ast constStr) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::string constStrValue = getConstStrValue(t, constStr);
  Z3_ast regAst = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrollFunc), 0);
  std::string stdRegexStr = "(" + getStdRegexStr(t, regAst) + ")*";
  std::regex e(stdRegexStr);
  if (! std::regex_match (constStrValue, e)){
#ifdef DEBUGLOG
    __debugPrint(logFile, ">> [checkUnroll2ConstStr]: Not match!");
    __debugPrint(logFile, "\n   * [unroll] ");
    printZ3Node(t, unrollFunc);
    __debugPrint(logFile, "\n   * [stdRex] %s", stdRegexStr.c_str());
    __debugPrint(logFile, "\n   * [const] ");
    printZ3Node(t, constStr);
    __debugPrint(logFile, "\n   ****************")
    __debugPrint(logFile, "\n   **** NEGATE ****");
    __debugPrint(logFile, "\n   ****************\n\n")
#endif
    Z3_ast toAssert = Z3_mk_not(ctx, Z3_mk_eq(ctx, unrollFunc, constStr));
    addAxiom(t, toAssert, __LINE__);
    return false;
  }
  return true;
}


/*
 *
 */
bool consistCheckRegex(Z3_theory t, Z3_ast nn1, Z3_ast nn2) {
  Z3_ast nn1EqConst = NULL;
  Z3_ast nn2EqConst = NULL;
  std::set<Z3_ast> nn1EqSimpleUnrollFuncs;
  std::set<Z3_ast> nn2EqSimpleUnrollFuncs;
  get_eqc_simpleUnroll(t, nn1, nn1EqConst, nn1EqSimpleUnrollFuncs);
  get_eqc_simpleUnroll(t, nn2, nn2EqConst, nn2EqSimpleUnrollFuncs);
  int nn1Len = getLenValue(t, nn1);
  int nn2Len = getLenValue(t, nn2);
  int eqcLen = (nn1Len != -1) ? nn1Len : nn2Len;

#ifdef DEBUGLOG
  __debugPrint(logFile, "---------------------\n");
  __debugPrint(logFile, ">> nn1: ");
  printZ3Node(t, nn1);
  __debugPrint(logFile, "\n   * [const] ");
  printZ3Node(t, nn1EqConst);
  __debugPrint(logFile, "\n   * [unroll] ");
  for (std::set<Z3_ast>::iterator itor = nn1EqSimpleUnrollFuncs.begin(); itor != nn1EqSimpleUnrollFuncs.end(); itor++) {
    printZ3Node(t, *itor);
    __debugPrint(logFile, ", ");
  }
  __debugPrint(logFile, "\n");

  __debugPrint(logFile, ">> nn2: ");
  printZ3Node(t, nn2);
  __debugPrint(logFile, "\n   * [const] ");
  printZ3Node(t, nn2EqConst);
  __debugPrint(logFile, "\n   * [unroll] ");
  for (std::set<Z3_ast>::iterator itor = nn2EqSimpleUnrollFuncs.begin(); itor != nn2EqSimpleUnrollFuncs.end(); itor++) {
    printZ3Node(t, *itor);
    __debugPrint(logFile, ", ");
  }
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, ">> Length EQC = %d\n", eqcLen);
  __debugPrint(logFile, "---------------------\n\n");
#endif
  // ---------------------------------------------------------------------------------
  // check value
  // ---------------------------------------------------------------------------------
  bool checkRes = true;
  Z3_ast constStrAst = (nn1EqConst != NULL) ? nn1EqConst : nn2EqConst;

  if (constStrAst != NULL) {
    std::set<Z3_ast> nn1EqAllUnrollFuncs;
    std::set<Z3_ast> nn2EqAllUnrollFuncs;
    get_eqc_allUnroll(t, nn1, nn1EqConst, nn1EqAllUnrollFuncs);
    get_eqc_allUnroll(t, nn2, nn2EqConst, nn2EqAllUnrollFuncs);

    for (std::set<Z3_ast>::iterator itor = nn1EqAllUnrollFuncs.begin(); itor != nn1EqAllUnrollFuncs.end(); itor++) {
      if (!checkUnroll2ConstStr(t, *itor, constStrAst)) {
        return false;
      }
    }

    for (std::set<Z3_ast>::iterator itor = nn2EqAllUnrollFuncs.begin(); itor != nn2EqAllUnrollFuncs.end(); itor++) {
      if (!checkUnroll2ConstStr(t, *itor, constStrAst)) {
        return false;
      }
    }
  }

  // ---------------------------------------------------------------------------------
  // check length
  // e.g. (Unroll abcd $$_unr_0) = $$_regVar_1 /\ |$$_regVar_1| = 6
  //       although the inconsistency can be detected by the length constraints later,
  //       we should negate asap
  // ---------------------------------------------------------------------------------
  checkRes = true;
  if (constStrAst == NULL && eqcLen > 0) {
    for (std::set<Z3_ast>::iterator itor = nn1EqSimpleUnrollFuncs.begin(); itor != nn1EqSimpleUnrollFuncs.end(); itor++) {
      checkRes = checkSimpleUnroll2eqLen(t, *itor, eqcLen);
      if (! checkRes)
        return false;
    }
    for (std::set<Z3_ast>::iterator itor = nn2EqSimpleUnrollFuncs.begin(); itor != nn2EqSimpleUnrollFuncs.end(); itor++) {
      checkRes = checkSimpleUnroll2eqLen(t, *itor, eqcLen);
      if (! checkRes)
        return false;
    }
  }

  return true;
}


/*
 *
 */
Z3_ast my_mk_unrollTest_var(Z3_theory t, Z3_ast node) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::stringstream ss;
  ss << "$$_uRt_" << Z3_ast_to_string(ctx, node) << "_" << (unrollTesterVarCount++);
  std::string name = ss.str();
  return my_mk_str_var(t, name.c_str());
}


/*
 *
 */
Z3_ast genUnrollAssign(Z3_theory t, Z3_ast var, std::string lcmStr, Z3_ast testerVar, int l, int h) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::vector<Z3_ast> orItems;
  std::vector<Z3_ast> andItems;
  for (int i = l; i < h; i++) {
    Z3_ast testerEqAst = Z3_mk_eq(ctx, testerVar, my_mk_str_value(t, intToString(i).c_str()));
    orItems.push_back(testerEqAst);
    std::string unrollStrInstance = getUnrolledString(lcmStr, i);
    andItems.push_back(Z3_mk_eq(ctx, testerEqAst, Z3_mk_eq(ctx, var, my_mk_str_value(t, unrollStrInstance.c_str()))));
    andItems.push_back(Z3_mk_eq(ctx, testerEqAst, Z3_mk_eq(ctx, mk_length(t, var),mk_int(ctx, i * lcmStr.length()))));
  }
  Z3_ast testerEqMore = Z3_mk_eq(ctx, testerVar, my_mk_str_value(t, "more"));
  orItems.push_back(testerEqMore);
  int nextLowerLenBound = h * lcmStr.length();
  andItems.push_back(Z3_mk_eq(ctx, testerEqMore, Z3_mk_ge(ctx, mk_length(t, var), mk_int(ctx, nextLowerLenBound))));
  andItems.push_back(mk_or_fromVector(t, orItems));
  return mk_and_fromVector(t, andItems);
}


/*
 *
 */
Z3_ast genUnrollConditionalOptions(Z3_theory t, Z3_ast var, std::set<Z3_ast> unrolls, std::string lcmStr) {
  Z3_context ctx = Z3_theory_get_context(t);  int dist = lcmUnrollStep;
  std::vector<Z3_ast> litems;
  Z3_ast moreAst = my_mk_str_value(t, "more");
  Z3_ast toAssert = NULL;
  for (std::set<Z3_ast>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
    litems.push_back(Z3_mk_eq(ctx, var, *itor));
  }

  if (unrollTriesMap[var][unrolls].size() == 0) {
    unrollTriesMap[var][unrolls].push_back(my_mk_unrollTest_var(t, var));
  }

  int tries = unrollTriesMap[var][unrolls].size();
  for (int i = 0; i < tries; i++) {
    Z3_ast tester = unrollTriesMap[var][unrolls][i];
    bool testerHasValue = false;
    Z3_ast testerVal = get_eqc_value(t, tester, testerHasValue);
    if (!testerHasValue) {
      // generate make-up assertion
      int l = i * dist;
      int h = (i + 1) * dist;
      Z3_ast lImp = mk_and_fromVector(t, litems);
      Z3_ast rImp = genUnrollAssign(t, var, lcmStr, tester, l, h);
      toAssert = Z3_mk_implies(ctx, lImp, rImp);
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> Making up assignments for variable that equals to unbounded unrolls:\n");
#endif
      //addAxiom(t, toAssert, __LINE__);
      return toAssert;

      // insert [tester = "more"] to litems so that the implyL for next tester is correct
      litems.push_back(Z3_mk_eq(ctx, tester, moreAst));
    } else {
      std::string testerStr = getConstStrValue(t, testerVal);
#ifdef DEBUGLOG
      __debugPrint(logFile, ">> Tester [");
      printZ3Node(t, tester);
      __debugPrint(logFile, "] = %s\n", testerStr.c_str());
#endif
      if (testerStr == "more") {
        litems.push_back(Z3_mk_eq(ctx, tester, moreAst));
      }
    }
  }
  Z3_ast tester = my_mk_unrollTest_var(t, var);
  unrollTriesMap[var][unrolls].push_back(tester);
  int l = tries * dist;
  int h = (tries + 1) * dist;
  Z3_ast lImp = mk_and_fromVector(t, litems);
  Z3_ast rImp = genUnrollAssign(t, var, lcmStr, tester, l, h);
  toAssert = Z3_mk_implies(ctx, lImp, rImp);
#ifdef DEBUGLOG
  __debugPrint(logFile, ">> Generate assignment for variable that equals to unbounded unrolls:\n");
#endif
  return toAssert;
}


/*
 *
 */
Z3_ast genAssignUnrollStr2Reg(Z3_theory t, Z3_ast n, std::set<Z3_ast> & unrolls) {
  Z3_context ctx = Z3_theory_get_context(t);
  int lcm = 1;
  int coreValueCount = 0;
  Z3_ast oneUnroll = NULL;
  std::string oneCoreStr = "";
  for (std::set<Z3_ast>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
    Z3_ast str2RegFunc = Z3_get_app_arg(ctx, Z3_to_app(ctx, *itor), 0);
    Z3_ast coreVal = Z3_get_app_arg(ctx, Z3_to_app(ctx, str2RegFunc), 0);
    std::string coreStr = getConstStrValue(t, coreVal);
    if (oneUnroll == NULL) {
      oneUnroll = *itor;
      oneCoreStr = coreStr;
    }
    coreValueCount++;
    int core1Len = coreStr.length();
    lcm = computeLCM(lcm, core1Len);
  }
  //
  bool canHaveNonEmptyAssign = true;
  std::vector<Z3_ast> litems;
  std::string lcmStr = getUnrolledString(oneCoreStr, (lcm / oneCoreStr.length()));
  for (std::set<Z3_ast>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
    Z3_ast str2RegFunc = Z3_get_app_arg(ctx, Z3_to_app(ctx, *itor), 0);
    Z3_ast coreVal = Z3_get_app_arg(ctx, Z3_to_app(ctx, str2RegFunc), 0);
    std::string coreStr = getConstStrValue(t, coreVal);
    int core1Len = coreStr.length();
    std::string uStr = getUnrolledString(coreStr, (lcm / core1Len));
    if (uStr != lcmStr) {
      canHaveNonEmptyAssign = false;
    }
    litems.push_back(Z3_mk_eq(ctx, n, *itor));
  }

  if (canHaveNonEmptyAssign) {
    return genUnrollConditionalOptions(t, n, unrolls, lcmStr);
  } else {
    Z3_ast implyL = mk_and_fromVector(t, litems);
    Z3_ast implyR = Z3_mk_eq(ctx, n, my_mk_str_value(t, ""));
    return Z3_mk_implies(ctx, implyL, implyR);
  }
}


/*
 *
 */
void reduceVirtualRegexIn(Z3_theory t, Z3_ast var, Z3_ast regex, std::vector<Z3_ast> & items) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_func_decl regexFuncDecl = Z3_get_app_decl(ctx, Z3_to_app(ctx, regex));
  if (regexFuncDecl == td->Str2Reg) {
    // ---------------------------------------------------------
    // var \in Str2Reg(s1)
    //   ==>
    // var = s1 /\ length(var) = length(s1)
    // ---------------------------------------------------------
    Z3_ast strInside = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    items.push_back(Z3_mk_eq(ctx, var, strInside));
    items.push_back(Z3_mk_eq(ctx, mk_length(t, var), mk_length(t, strInside)));
    return;
  }
  // RegexUnion
  else if (regexFuncDecl == td->RegexUnion) {
    // ---------------------------------------------------------
    // var \in RegexUnion(r1, r2)
    //   ==>
    // (var = newVar1 \/ var = newVar2)
    // (var = newVar1 --> length(var) = length(newVar1)) /\ (var = newVar2 --> length(var) = length(newVar2))
    //  /\ (newVar1 \in r1) /\  (newVar2 \in r2)
    // ---------------------------------------------------------
    Z3_ast newVar1 = mk_regexRepVar(t);
    Z3_ast newVar2 = mk_regexRepVar(t);
    items.push_back(mk_2_or(t, Z3_mk_eq(ctx, var, newVar1), Z3_mk_eq(ctx, var, newVar2)));
    items.push_back(Z3_mk_implies(ctx, Z3_mk_eq(ctx, var, newVar1), Z3_mk_eq(ctx, mk_length(t, var), mk_length(t, newVar1))));
    items.push_back(Z3_mk_implies(ctx, Z3_mk_eq(ctx, var, newVar2), Z3_mk_eq(ctx, mk_length(t, var), mk_length(t, newVar2))));

    Z3_ast regArg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    reduceVirtualRegexIn(t, newVar1, regArg1, items);

    Z3_ast regArg2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 1);
    reduceVirtualRegexIn(t, newVar2, regArg2, items);

    return;
  }
  // RegexConcat
  else if (regexFuncDecl == td->RegexConcat) {
    // ---------------------------------------------------------
    // var \in RegexConcat(r1, r2)
    //   ==>
    //    (var = newVar1 . newVar2) /\ (length(var) = length(vewVar1 . newVar2) )
    // /\ (newVar1 \in r1) /\  (newVar2 \in r2)
    // ---------------------------------------------------------
    Z3_ast newVar1 = mk_regexRepVar(t);
    Z3_ast newVar2 = mk_regexRepVar(t);
    Z3_ast concatAst = mk_concat(t, newVar1, newVar2);
    items.push_back(Z3_mk_eq(ctx, var, concatAst));
    items.push_back(Z3_mk_eq(ctx, mk_length(t, var), mk_2_add(t, mk_length(t, newVar1), mk_length(t, newVar2))));


    Z3_ast regArg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    reduceVirtualRegexIn(t, newVar1, regArg1, items);
    Z3_ast regArg2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 1);
    reduceVirtualRegexIn(t, newVar2, regArg2, items);
    return;
  }
  // Unroll
  else if (regexFuncDecl == td->RegexStar) {
    // ---------------------------------------------------------
    // var \in Star(r1)
    //   ==>
    // var = unroll(r1, t1) /\ |var| = |unroll(r1, t1)|
    // ---------------------------------------------------------
    Z3_ast regArg = Z3_get_app_arg(ctx, Z3_to_app(ctx, regex), 0);
    Z3_ast unrollCnt = mk_unrollBoundVar(t);
    Z3_ast unrollFunc = mk_unroll(t, regArg, unrollCnt);
    items.push_back(Z3_mk_eq(ctx, var, unrollFunc));
    items.push_back(Z3_mk_eq(ctx, mk_length(t, var), mk_length(t, unrollFunc)));
    return;
  }
}

/*
 *
 */
void genAssignUnrollReg(Z3_theory t, std::set<Z3_ast> & unrolls) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::vector<Z3_ast> items;
  for (std::set<Z3_ast>::iterator itor = unrolls.begin(); itor != unrolls.end(); itor++) {
    Z3_ast unrFunc = *itor;

    Z3_ast regexInUnr = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrFunc), 0);
    Z3_ast cntInUnr = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrFunc), 1);
    items.clear();

    int low = -1;
    int high = -1;
    Z3_theory_get_bound_strlen(t, cntInUnr, low, high);

#ifdef DEBUGLOG
    __debugPrint(logFile, ">> genAssignUnrollReg: \n");
    __debugPrint(logFile, "   * [unroll] ");
    printZ3Node(t, unrFunc);
    bool cntHasValue = false;
    int cntInUnrValue = getIntValue(t, cntInUnr, cntHasValue);
    __debugPrint(logFile, "\n   * [unroll length] %d\n", getLenValue(t, unrFunc));
    __debugPrint(logFile, "   * [unroll count] %d (low = %d, high = %d)\n", cntInUnrValue, low, high);
    __debugPrint(logFile, "\n\n");
#endif

    Z3_ast toAssert = NULL;
    if (low < 0) {
      toAssert = Z3_mk_ge(ctx, cntInUnr, mk_int(ctx, 0));
    } else {
      if (unrollVarMap.find(unrFunc) == unrollVarMap.end()) {
/*
        std::vector<Z3_ast> eq0Items;
        std::vector<Z3_ast> ge1Items;

        Z3_ast newVar1 = mk_regexRepVar(t);
        Z3_ast newVar2 = mk_regexRepVar(t);
        Z3_ast concatAst = mk_concat(t, newVar1, newVar2);
        Z3_ast newCnt = mk_unrollBoundVar(t);
        Z3_ast newUnrollFunc = mk_unroll(t, regexInUnr, newCnt);

        ge1Items.push_back(Z3_mk_eq(ctx, unrFunc, concatAst));
        ge1Items.push_back(Z3_mk_eq(ctx, mk_length(t, unrFunc), mk_2_add(t, mk_length(t, newVar1), mk_length(t, newVar2))));
        ge1Items.push_back(Z3_mk_ge(ctx, mk_length(t, unrFunc), mk_length(t, newVar1)));
        ge1Items.push_back(Z3_mk_ge(ctx, mk_length(t, unrFunc), mk_length(t, newVar2)));
        reduceVirtualRegexIn(t, newVar1, regexInUnr, ge1Items);
        ge1Items.push_back(Z3_mk_eq(ctx, newVar2, newUnrollFunc));
        ge1Items.push_back(Z3_mk_eq(ctx, mk_length(t, newVar2), mk_length(t, newUnrollFunc)));
        ge1Items.push_back(Z3_mk_eq(ctx, cntInUnr, mk_2_add(t, newCnt, mk_int(ctx, 1))));
        Z3_ast elseB = mk_and_fromVector(t, ge1Items);

        eq0Items.push_back(Z3_mk_eq(ctx, unrFunc, my_mk_str_value(t, "")));
        eq0Items.push_back(Z3_mk_eq(ctx, mk_length(t, unrFunc), mk_int(ctx, 0)));
        Z3_ast thenB = mk_and_fromVector(t, eq0Items);

        toAssert = Z3_mk_ite(ctx, Z3_mk_eq(ctx, cntInUnr, mk_int(ctx, 0)), thenB, elseB);
*/

        Z3_ast newVar1 = mk_regexRepVar(t);
        Z3_ast newVar2 = mk_regexRepVar(t);
        Z3_ast concatAst = mk_concat(t, newVar1, newVar2);
        Z3_ast newCnt = mk_unrollBoundVar(t);
        Z3_ast newUnrollFunc = mk_unroll(t, regexInUnr, newCnt);

        // unroll(r1, t1) = newVar1 . newVar2
        items.push_back(Z3_mk_eq(ctx, unrFunc, concatAst));
        items.push_back(Z3_mk_eq(ctx, mk_length(t, unrFunc), mk_2_add(t, mk_length(t, newVar1), mk_length(t, newVar2))));
        items.push_back(Z3_mk_ge(ctx, mk_length(t, unrFunc), mk_length(t, newVar1)));
        items.push_back(Z3_mk_ge(ctx, mk_length(t, unrFunc), mk_length(t, newVar2)));
        // newVar1 \in r1
        reduceVirtualRegexIn(t, newVar1, regexInUnr, items);
        items.push_back(Z3_mk_eq(ctx, cntInUnr, mk_2_add(t, newCnt, mk_int(ctx, 1))));
        items.push_back(Z3_mk_eq(ctx, newVar2, newUnrollFunc));
        items.push_back(Z3_mk_eq(ctx, mk_length(t, newVar2), mk_length(t, newUnrollFunc)));
        toAssert = Z3_mk_eq(ctx, Z3_mk_ge(ctx, cntInUnr, mk_int(ctx, 1)), mk_and_fromVector(t, items));

        // option 0
        Z3_ast op0 = Z3_mk_eq(ctx, cntInUnr, mk_int(ctx, 0));
        Z3_ast ast1 = Z3_mk_eq(ctx, unrFunc, my_mk_str_value(t, ""));
        Z3_ast ast2 = Z3_mk_eq(ctx, mk_length(t, unrFunc), mk_int(ctx, 0));
        Z3_ast and1 = mk_2_and(t, ast1, ast2);

        // put together
        toAssert = mk_2_and(t, Z3_mk_eq(ctx, op0, and1), toAssert);

        unrollVarMap[unrFunc] = toAssert;
      } else {
        toAssert = unrollVarMap[unrFunc];
      }
    }
    addAxiom(t, toAssert, __LINE__);
  }
}



/*
 *
 */
void unrollStr2Reg2ConstStr(Z3_theory t, Z3_ast unrollFunc, Z3_ast eqConstStr) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast str2RegFunc = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrollFunc), 0);
  Z3_ast strInStr2RegFunc = Z3_get_app_arg(ctx, Z3_to_app(ctx, str2RegFunc), 0);
  Z3_ast oriCnt = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrollFunc), 1);

  std::string strValue = getConstStrValue(t, eqConstStr);
  std::string regStrValue = getConstStrValue(t, strInStr2RegFunc);
  int strLen = strValue.length();
  int regStrLen = regStrValue.length();
  int cnt = strLen / regStrLen;

  Z3_ast implyL = Z3_mk_eq(ctx, unrollFunc, eqConstStr);
  Z3_ast implyR1 = Z3_mk_eq(ctx, oriCnt, mk_int(ctx, cnt));
  Z3_ast implyR2 = Z3_mk_eq(ctx, mk_length(t, unrollFunc), mk_int(ctx, strLen));
  Z3_ast toAssert = Z3_mk_implies(ctx, implyL, mk_2_and(t, implyR1, implyR2));

  addAxiom(t, toAssert, __LINE__);
}



/*
 *  After cb_new_eq consistency check, unroll the unroll function as needed
 */
void processUnrollEqConstStr(Z3_theory t, Z3_ast unrollFunc, Z3_ast constStr) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  if (Z3_get_app_decl(ctx, Z3_to_app(ctx, unrollFunc)) != td->Unroll)
    return;
  if (! isConstStr(t, constStr))
    return;

  Z3_ast funcInUnroll = Z3_get_app_arg(ctx, Z3_to_app(ctx, unrollFunc), 0);
  Z3_func_decl funcInUnrollDecl = Z3_get_app_decl(ctx, Z3_to_app(ctx, funcInUnroll));
  std::string strValue = getConstStrValue(t, constStr);

#ifdef DEBUGLOG
  __debugPrint(logFile, ">> processUnrollEqConstStr: \n");
  __debugPrint(logFile, "   * [unrollFunc] ");
  printZ3Node(t, unrollFunc);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "   * [constStr] %s\n", strValue.c_str());
  __debugPrint(logFile, "\n\n");
#endif

  // quick path
  if (strValue == "") {
    return;
  }

  //
  if (funcInUnrollDecl == td->Str2Reg) {
    unrollStr2Reg2ConstStr(t, unrollFunc, constStr);
    return;
  }
}

/*
 *  arg1 . arg2 = unroll(r1, t1)
 *  -----------------------------
 *    (op-1) arg1 = "" /\ arg2 = ""
 *    (op-2) arg1 = v1 . v2  /\  v1 = unroll(r1, t2)
 *           /\  arg2 = v3 . v4  /\  v4 = unroll(r1, t3)
 *           /\  v2 . v3 = v5  /\  v5  \in r1  /\ t2 + t3 = t1 - 1
 *  -----------------------------
 */

void processConcatEqUnroll(Z3_theory t, Z3_ast concat, Z3_ast unroll) {
#ifdef DEBUGLOG
  __debugPrint(logFile, ">> processConcatEqUnroll: \n");
  __debugPrint(logFile, "   * [concat] ");
  printZ3Node(t, concat);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "   * [unroll] ");
  printZ3Node(t, unroll);
  __debugPrint(logFile, "\n\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);
  std::pair<Z3_ast, Z3_ast> key = std::make_pair(concat, unroll);
  Z3_ast toAssert = NULL;

  if (concatEqUnroll_AstMap.find(key) == concatEqUnroll_AstMap.end()) {
    Z3_ast arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat), 0);
    Z3_ast arg2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concat), 1);
    Z3_ast r1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, unroll), 0);
    Z3_ast t1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, unroll), 1);

    Z3_ast v1 = mk_regexRepVar(t);
    Z3_ast v2 = mk_regexRepVar(t);
    Z3_ast v3 = mk_regexRepVar(t);
    Z3_ast v4 = mk_regexRepVar(t);
    Z3_ast v5 = mk_regexRepVar(t);

    Z3_ast t2 = mk_unrollBoundVar(t);
    Z3_ast t3 = mk_unrollBoundVar(t);
    Z3_ast emptyStr = my_mk_str_value(t, "");

    Z3_ast unroll1 = mk_unroll(t, r1, t2);
    Z3_ast unroll2 = mk_unroll(t, r1, t3);

    Z3_ast op0 = Z3_mk_eq(ctx, t1, mk_int(ctx, 0));
    Z3_ast op1 = Z3_mk_ge(ctx, t1, mk_int(ctx, 1));

    std::vector<Z3_ast> op1Items;
    std::vector<Z3_ast> op2Items;

    op1Items.push_back(Z3_mk_eq(ctx, arg1, emptyStr));
    op1Items.push_back(Z3_mk_eq(ctx, arg2, emptyStr));
    op1Items.push_back(Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, 0)));
    op1Items.push_back(Z3_mk_eq(ctx, mk_length(t, arg2), mk_int(ctx, 0)));
    Z3_ast opAnd1 = Z3_mk_eq(ctx, op0, mk_and_fromVector(t, op1Items));

    Z3_ast v1v2 = mk_concat(t, v1, v2);
    op2Items.push_back(Z3_mk_eq(ctx, arg1, v1v2));
    op2Items.push_back(Z3_mk_eq(ctx, mk_length(t, arg1), mk_2_add(t, mk_length(t, v1), mk_length(t, v2))));
    Z3_ast v3v4 = mk_concat(t, v3, v4);
    op2Items.push_back(Z3_mk_eq(ctx, arg2, v3v4));
    op2Items.push_back(Z3_mk_eq(ctx, mk_length(t, arg2), mk_2_add(t, mk_length(t, v3), mk_length(t, v4))));

    op2Items.push_back(Z3_mk_eq(ctx, v1, unroll1));
    op2Items.push_back(Z3_mk_eq(ctx, mk_length(t, v1), mk_length(t, unroll1)));
    op2Items.push_back(Z3_mk_eq(ctx, v4, unroll2));
    op2Items.push_back(Z3_mk_eq(ctx, mk_length(t, v4), mk_length(t, unroll2)));
    Z3_ast v2v3 = mk_concat(t, v2, v3);
    op2Items.push_back(Z3_mk_eq(ctx, v5, v2v3));
    reduceVirtualRegexIn(t, v5, r1, op2Items);
    op2Items.push_back(Z3_mk_eq(ctx, mk_length(t, v5), mk_2_add(t, mk_length(t, v2), mk_length(t, v3))));
    op2Items.push_back(Z3_mk_eq(ctx, mk_2_add(t, t2, t3), mk_2_sub(t, t1, mk_int(ctx, 1))));
    Z3_ast opAnd2 = Z3_mk_eq(ctx, op1, mk_and_fromVector(t, op2Items));

    toAssert = mk_2_and(t, opAnd1, opAnd2);
    concatEqUnroll_AstMap[key] = toAssert;
  } else {
    toAssert = concatEqUnroll_AstMap[key];
  }

  addAxiom(t, toAssert, __LINE__);
}


