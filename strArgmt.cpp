#include "strTheory.h"

// backtrack-able cut information
struct T_cut
{
    int level;
    std::map<Z3_ast, int> vars;

    T_cut() {
      level = -100;
    }
};

bool avoidLoopCut = true;
bool loopDetected = false;
std::map<Z3_ast, std::stack<T_cut *> > cut_VARMap;

/*
 *
 */
void cutVarsMapCopy(std::map<Z3_ast, int> & dest, std::map<Z3_ast, int> & src) {
  std::map<Z3_ast, int>::iterator itor = src.begin();
  for (; itor != src.end(); itor++) {
    dest[itor->first] = 1;
  }
}

/*
 *
 */
void addCutInfoOneNode(Z3_ast baseNode, int slevel, Z3_ast node) {
  if (cut_VARMap.find(baseNode) == cut_VARMap.end()) {
    T_cut * varInfo = new T_cut();
    varInfo->level = slevel;
    varInfo->vars[node] = 1;
    cut_VARMap[baseNode].push(varInfo);
  } else {
    if (cut_VARMap[baseNode].empty()) {
      T_cut * varInfo = new T_cut();
      varInfo->level = slevel;
      varInfo->vars[node] = 1;
      cut_VARMap[baseNode].push(varInfo);
    } else {
      if (cut_VARMap[baseNode].top()->level < slevel) {
        T_cut * varInfo = new T_cut();
        varInfo->level = slevel;
        cutVarsMapCopy(varInfo->vars, cut_VARMap[baseNode].top()->vars);
        varInfo->vars[node] = 1;
        cut_VARMap[baseNode].push(varInfo);
      } else if (cut_VARMap[baseNode].top()->level == slevel) {
        cut_VARMap[baseNode].top()->vars[node] = 1;
      } else {
        printf("should not be here. exit %d\n", __LINE__);
        exit(0);
      }
    }
  }
}

/*
 *
 */
void addCutInfoMerge(Z3_ast destNode, int slevel, Z3_ast srcNode) {
  if (cut_VARMap.find(srcNode) == cut_VARMap.end()) {
    printf("should not be here. exit %d\n", __LINE__);
    exit(0);
  }

  if (cut_VARMap[srcNode].empty()) {
    printf("should not be here. exit %d\n", __LINE__);
    exit(0);
  }

  if (cut_VARMap.find(destNode) == cut_VARMap.end()) {
    T_cut * varInfo = new T_cut();
    varInfo->level = slevel;
    cutVarsMapCopy(varInfo->vars, cut_VARMap[srcNode].top()->vars);
    cut_VARMap[destNode].push(varInfo);
  } else {
    if (cut_VARMap[destNode].empty() || cut_VARMap[destNode].top()->level < slevel) {
      T_cut * varInfo = new T_cut();
      varInfo->level = slevel;
      cutVarsMapCopy(varInfo->vars, cut_VARMap[destNode].top()->vars);
      cutVarsMapCopy(varInfo->vars, cut_VARMap[srcNode].top()->vars);
      cut_VARMap[destNode].push(varInfo);
    } else if (cut_VARMap[destNode].top()->level == slevel) {
      cutVarsMapCopy(cut_VARMap[destNode].top()->vars, cut_VARMap[srcNode].top()->vars);
    } else {
      printf("should not be here. exit %d\n", __LINE__);
      exit(0);
    }
  }
}

/*
 *
 */
void checkandInit_cutVAR(Z3_theory t, Z3_ast node) {
  if (cut_VARMap.find(node) != cut_VARMap.end()) {
    return;
  } else {
    if (getNodeType(t, node) != my_Z3_ConstStr) {
      addCutInfoOneNode(node, -1, node);
    }
  }
}

/*
 *
 */
bool hasSelfCut(Z3_ast n1, Z3_ast n2) {
  if (cut_VARMap.find(n1) == cut_VARMap.end())
    return false;

  if (cut_VARMap.find(n2) == cut_VARMap.end())
    return false;

  if (cut_VARMap[n1].empty() || cut_VARMap[n2].empty())
    return false;

  std::map<Z3_ast, int>::iterator itor = cut_VARMap[n1].top()->vars.begin();
  for (; itor != cut_VARMap[n1].top()->vars.end(); itor++) {
    if (cut_VARMap[n2].top()->vars.find(itor->first) != cut_VARMap[n2].top()->vars.end())
      return true;
  }
  return false;
}

/*
 *
 */

void printCutVAR(Z3_theory t, Z3_ast node) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n>> CUT info of [");
  printZ3Node(t, node);
  __debugPrint(logFile, "]\n");

  if (cut_VARMap.find(node) != cut_VARMap.end()) {
    if (!cut_VARMap[node].empty()) {
      __debugPrint(logFile, "[%2d] {", cut_VARMap[node].top()->level);
      std::map<Z3_ast, int>::iterator itor = cut_VARMap[node].top()->vars.begin();
      for (; itor != cut_VARMap[node].top()->vars.end(); itor++) {
        printZ3Node(t, itor->first);
        __debugPrint(logFile, ", ");
      }
      __debugPrint(logFile, "}\n");
    } else {

    }
  }
  __debugPrint(logFile, "------------------------\n\n");
#endif
}


/*
 *
 */
void cb_pop(Z3_theory t) {
  sLevel--;
  __debugPrint(logFile, "\n*******************************************\n");
  __debugPrint(logFile, "[POP]: Level = %d", sLevel);
  __debugPrint(logFile, "\n*******************************************\n");

  std::map<Z3_ast, std::stack<T_cut *> >::iterator varItor = cut_VARMap.begin();
  while (varItor != cut_VARMap.end()) {
    while ((varItor->second.size() > 0) && (varItor->second.top()->level != 0) && (varItor->second.top()->level >= sLevel)) {
      T_cut * aCut = varItor->second.top();
      varItor->second.pop();
      delete aCut;
    }
    if (varItor->second.size() == 0)
      cut_VARMap.erase(varItor++);
    else
      varItor++;
  }
}


/*************************************************************
 * Type 1: concat(x, y) = concat(m, n)
 *         x, y, m and n all variables
 *************************************************************/
bool isConcatEqType_1(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast x = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast y = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast m = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast n = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);
  if ((!isConstStr(t, x)) && (!isConstStr(t, y)) && (!isConstStr(t, m)) && (!isConstStr(t, n)))
    return true;
  else
    return false;
}


Z3_ast inline getLengthRoot(Z3_theory t, Z3_ast node) {
  return Z3_theory_getArithEqcRoot(t, mk_length(t, node));
}

/*
 *
 */
void processConcatEqType_1(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 1  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  if (! isConcatFunc(t, concatAst1) ) {
    __debugPrint(logFile, ">> [processConcatEqType_1] concatAst1 is not a concat function %d\n", __LINE__);
    return;
  }

  if (! isConcatFunc(t, concatAst2)) {
    __debugPrint(logFile, ">> [processConcatEqType_1] concatAst2 is not a concat function %d\n", __LINE__);
    return;
  }

  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast x = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast y = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast m = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast n = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  int x_len = getLenValue(t, x);
  int y_len = getLenValue(t, y);
  int m_len = getLenValue(t, m);
  int n_len = getLenValue(t, n);

  int splitType = -1;
  if (x_len != -1 && m_len != -1) {
    if (x_len < m_len)
      splitType = 0;
    else if (x_len == m_len)
      splitType = 1;
    else
      splitType = 2;
  }

  if (splitType == -1 && y_len != -1 && n_len != -1) {
    if (y_len > n_len)
      splitType = 0;
    else if (y_len == n_len)
      splitType = 1;
    else
      splitType = 2;
  }

  __debugPrint(logFile, ">> SplitType = %d @ %d.\n\n", splitType, __LINE__);

  // ------------------------------------

  Z3_ast t1 = NULL;
  Z3_ast t2 = NULL;
  Z3_ast xorFlag = NULL;
  std::pair<Z3_ast, Z3_ast> key1(concatAst1, concatAst2);
  std::pair<Z3_ast, Z3_ast> key2(concatAst2, concatAst1);
  if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
    t1 = my_mk_nonEmpty_string_var(t);
    t2 = my_mk_nonEmpty_string_var(t);
    xorFlag = mk_internal_xor_var(t);
    checkandInit_cutVAR(t, t1);
    checkandInit_cutVAR(t, t2);
    varForBreakConcat[key1][0] = t1;
    varForBreakConcat[key1][1] = t2;
    varForBreakConcat[key1][2] = xorFlag;
  } else {
    if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
      t1 = varForBreakConcat[key1][0];
      t2 = varForBreakConcat[key1][1];
      xorFlag = varForBreakConcat[key1][2];

    } else {
      t1 = varForBreakConcat[key2][0];
      t2 = varForBreakConcat[key2][1];
      xorFlag = varForBreakConcat[key2][2];
    }
  }


  // #############################################################################
  // Begin: providing less split options when length information is available
  if (splitType == 0) {
    //--------------------------------------
    // break option 1: m cut y
    //   len(x) < len(m) || len(y) > len(n)
    //--------------------------------------
    if (!hasSelfCut(m, y)) {
      Z3_ast ax_l_items[3];
      ax_l_items[0] = Z3_mk_eq(ctx, concatAst1, concatAst2);

      Z3_ast x_t1 = mk_concat(t, x, t1);
      Z3_ast t1_n = mk_concat(t, t1, n);

      Z3_ast ax_r_items[3];
      ax_r_items[0] = Z3_mk_eq(ctx, m, x_t1);
      ax_r_items[1] = Z3_mk_eq(ctx, y, t1_n);

      if (m_len != -1 && x_len != -1) {
        ax_l_items[1] = Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len));
        ax_l_items[2] = Z3_mk_eq(ctx, mk_length(t, m), mk_int(ctx, m_len));
        ax_r_items[2] = Z3_mk_eq(ctx, mk_length(t, t1), mk_int(ctx, (m_len - x_len)));
      } else {
        ax_l_items[1] = Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len));
        ax_l_items[2] = Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, n_len));
        ax_r_items[2] = Z3_mk_eq(ctx, mk_length(t, t1), mk_int(ctx, (y_len - n_len)));
      }

      Z3_ast ax_l = Z3_mk_and(ctx, 3, ax_l_items);
      Z3_ast ax_r = Z3_mk_and(ctx, 3, ax_r_items);

      // Cut Info
      addCutInfoMerge(t1, sLevel, m);
      addCutInfoMerge(t1, sLevel, y);

      addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
    } else {
      loopDetected = true;
#ifdef DEBUGLOG
      __debugPrint(logFile, "-------------------\n");
      __debugPrint(logFile, "[AVOID Loop] Skip @ %d.\n", __LINE__);
      printCutVAR(t, m);
      printCutVAR(t, y);
      __debugPrint(logFile, "-------------------\n");
#endif
    }
  } else if (splitType == 1) {
    //--------------------------------------
    // break option 2:
    //   len(x) = len(m) || len(y) = len(n)
    //--------------------------------------
    Z3_ast ax_l1 = Z3_mk_eq(ctx, concatAst1, concatAst2);
    Z3_ast ax_l2 = mk_2_or(t, Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, m)), Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, n)));
    Z3_ast ax_l = mk_2_and(t, ax_l1, ax_l2);
    Z3_ast ax_r = mk_2_and(t, Z3_mk_eq(ctx, x, m), Z3_mk_eq(ctx, y, n));
    addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
  } else if (splitType == 2) {
    //--------------------------------------
    // break option 3:
    //   len(x) > len(m) || len(y) < len(n)
    //--------------------------------------
    if (!hasSelfCut(x, n)) {
      Z3_ast m_t2 = mk_concat(t, m, t2);
      Z3_ast t2_y = mk_concat(t, t2, y);

      Z3_ast ax_l_items[3];
      ax_l_items[0] = Z3_mk_eq(ctx, concatAst1, concatAst2);

      Z3_ast ax_r_items[3];
      ax_r_items[0] = Z3_mk_eq(ctx, x, m_t2);
      ax_r_items[1] = Z3_mk_eq(ctx, t2_y, n);

      if (m_len != -1 && x_len != -1) {
        ax_l_items[1] = Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len));
        ax_l_items[2] = Z3_mk_eq(ctx, mk_length(t, m), mk_int(ctx, m_len));
        ax_r_items[2] = Z3_mk_eq(ctx, mk_length(t, t2), mk_int(ctx, (x_len - m_len)));
      } else {
        ax_l_items[1] = Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len));
        ax_l_items[2] = Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, n_len));
        ax_r_items[2] = Z3_mk_eq(ctx, mk_length(t, t2), mk_int(ctx, (n_len - y_len)));
      }

      Z3_ast ax_l = Z3_mk_and(ctx, 3, ax_l_items);
      Z3_ast ax_r = Z3_mk_and(ctx, 3, ax_r_items);

      // Cut Info
      addCutInfoMerge(t2, sLevel, x);
      addCutInfoMerge(t2, sLevel, n);

      addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
    } else {
      loopDetected = true;
#ifdef DEBUGLOG
      __debugPrint(logFile, "-------------------\n");
      __debugPrint(logFile, "[AVOID Loop] Skip @ %d.\n", __LINE__);
      printCutVAR(t, m);
      printCutVAR(t, y);
      __debugPrint(logFile, "-------------------\n");
#endif
    }
  }
  // End: providing less split options when length information is available
  // #############################################################################
  else if (splitType == -1) {
    Z3_ast * or_item = new Z3_ast[3];
    Z3_ast * and_item = new Z3_ast[20];
    int option = 0;
    int pos = 1;

    //--------------------------------------
    // break option 1: m cut y
    //   len(x) < len(m) || len(y) > len(n)
    //--------------------------------------
    if (!avoidLoopCut || !(hasSelfCut(m, y))) {
      // break down option 1-1
      Z3_ast x_t1 = mk_concat(t, x, t1);
      Z3_ast t1_n = mk_concat(t, t1, n);
      or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, m, x_t1));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, t1_n));

      Z3_ast addItems[2];
      addItems[0] = mk_length(t, x);
      addItems[1] = mk_length(t, t1);
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, m), Z3_mk_add(ctx, 2, addItems)));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_gt(ctx, mk_length(t, m), mk_length(t, x)));

//      addItems[0] = mk_length(t, t1);
//      addItems[1] = mk_length(t, n);
//      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), Z3_mk_add(ctx, 2, addItems)));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_gt(ctx, mk_length(t, y), mk_length(t, n)));

      option++;

      // Cut Info
      addCutInfoMerge(t1, sLevel, m);
      addCutInfoMerge(t1, sLevel, y);
    } else {
      loopDetected = true;
#ifdef DEBUGLOG
      __debugPrint(logFile, "-------------------\n");
      __debugPrint(logFile, "[AVOID Loop] Skip @ %d.\n", __LINE__);
      printCutVAR(t, m);
      printCutVAR(t, y);
      __debugPrint(logFile, "-------------------\n");
#endif
    }
    //--------------------------------------
    // break option 2:
    //   x = m || y = n
    //--------------------------------------
    if (!avoidLoopCut || !(hasSelfCut(x, n))) {
      // break down option 1-2
      Z3_ast m_t2 = mk_concat(t, m, t2);
      Z3_ast t2_y = mk_concat(t, t2, y);
      or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, m_t2));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, n, t2_y));

      Z3_ast addItems[2];
      addItems[0] = mk_length(t, m);
      addItems[1] = mk_length(t, t2);
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), Z3_mk_add(ctx, 2, addItems)));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_gt(ctx, mk_length(t, x), mk_length(t, m)));

//      addItems[0] = mk_length(t, t2);
//      addItems[1] = mk_length(t, y);
//      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, n), Z3_mk_add(ctx, 2, addItems)));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_gt(ctx, mk_length(t, n), mk_length(t, y)));

      option++;

      addCutInfoMerge(t2, sLevel, x);
      addCutInfoMerge(t2, sLevel, n);
    } else {
      loopDetected = true;
#ifdef DEBUGLOG
      __debugPrint(logFile, "-------------------\n");
      __debugPrint(logFile, "[AVOID Looping Cut] Skip @ %d.\n", __LINE__);
      printCutVAR(t, x);
      printCutVAR(t, n);
      __debugPrint(logFile, "-------------------\n");
#endif
    }

    if (canTwoNodesEq(t, x, m) && canTwoNodesEq(t, y, n)) {
      or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, m));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, n));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, m)));
      and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, n)));
      option++;
    }

    if (option > 0) {
      if (option == 1) {
        and_item[0] = or_item[0];
      } else {
        and_item[0] = Z3_mk_or(ctx, option, or_item);
      }

      Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
      Z3_ast toAssert = Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR);

      addAxiom(t, toAssert, __LINE__);

    } else {
      __debugPrint(logFile, "\n[STOP @ %d] No split option found for two EQ concats\n", __LINE__);
      return;
    }
    delete[] or_item;
    delete[] and_item;
    return;
  }
}



/*************************************************************
 * Type 2: concat(x, y) = concat(m, "str")
 *************************************************************/
bool isConcatEqType_2(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if ((!isConstStr(t, v1_arg0)) && isConstStr(t, v1_arg1) && (!isConstStr(t, v2_arg0)) && (!isConstStr(t, v2_arg1))) {
    return true;
  } else if ((!isConstStr(t, v2_arg0)) && isConstStr(t, v2_arg1) && (!isConstStr(t, v1_arg0)) && (!isConstStr(t, v1_arg1))) {
    return true;
  } else {
    return false;
  }
}

/*
 *
 */
void processConcatEqType_2(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 2  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast x = NULL;
  Z3_ast y = NULL;
  Z3_ast strAst = NULL;
  Z3_ast m = NULL;

  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if (getNodeType(t, v1_arg1) == my_Z3_ConstStr && getNodeType(t, v2_arg1) != my_Z3_ConstStr) {
    m = v1_arg0;
    strAst = v1_arg1;
    x = v2_arg0;
    y = v2_arg1;
  } else {
    m = v2_arg0;
    strAst = v2_arg1;
    x = v1_arg0;
    y = v1_arg1;
  }

  std::string strValue = getConstStrValue(t, strAst);
  int x_len = getLenValue(t, x);
  int y_len = getLenValue(t, y);
  int m_len = getLenValue(t, m);
  int str_len = getLenValue(t, strAst);

  //-----------------------------------------------------------------

  Z3_ast xorFlag = NULL;
  Z3_ast temp1 = NULL;
  std::pair<Z3_ast, Z3_ast> key1(concatAst1, concatAst2);
  std::pair<Z3_ast, Z3_ast> key2(concatAst2, concatAst1);
  if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
    temp1 = my_mk_nonEmpty_string_var(t);
    xorFlag = mk_internal_xor_var(t);

    varForBreakConcat[key1][0] = temp1;
    varForBreakConcat[key1][1] = xorFlag;
  } else {
    if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
      temp1 = varForBreakConcat[key1][0];
      xorFlag = varForBreakConcat[key1][1];
    } else if (varForBreakConcat.find(key2) != varForBreakConcat.end()) {
      temp1 = varForBreakConcat[key2][0];
      xorFlag = varForBreakConcat[key2][1];
    }
  }



  int splitType = -1;
  if (x_len != -1 && m_len != -1) {
    if (x_len < m_len)
      splitType = 0;
    else if (x_len == m_len)
      splitType = 1;
    else
      splitType = 2;
  }
  if (splitType == -1 && y_len != -1 && str_len != -1) {
    if (y_len > str_len)
      splitType = 0;
    else if (y_len == str_len)
      splitType = 1;
    else
      splitType = 2;
  }

  __debugPrint(logFile, ">> SplitType = %d @ %d.\n\n", splitType, __LINE__);

  // #############################################################################
  // Begin: providing less split options when length information is available
  if (splitType == 0) {
    Z3_ast temp1_strAst = mk_concat(t, temp1, strAst);
    //--------------------------------------------------------
    // m cut y,
    //   |  x  |      y     |
    //   |    m   |   str   |
    //--------------------------------------------------------
    if (canTwoNodesEq(t, y, temp1_strAst)) {
      if (!avoidLoopCut || !(hasSelfCut(m, y))) {
        // break down option 2-1
        Z3_ast l_items[3];
        l_items[0] = Z3_mk_eq(ctx, concatAst1, concatAst2);

        Z3_ast r_items[3];
        Z3_ast x_temp1 = mk_concat(t, x, temp1);
        r_items[0] = Z3_mk_eq(ctx, m, x_temp1);
        r_items[1] = Z3_mk_eq(ctx, y, temp1_strAst);

        if (x_len != -1 && m_len != -1) {
          l_items[1] = Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len));
          l_items[2] = Z3_mk_eq(ctx, mk_length(t, m), mk_int(ctx, m_len));
          r_items[2] = Z3_mk_eq(ctx, mk_length(t, temp1), mk_int(ctx, (m_len - x_len)));
        } else {
          l_items[1] = Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len));
          l_items[2] = Z3_mk_eq(ctx, mk_length(t, strAst), mk_int(ctx, str_len));
          r_items[2] = Z3_mk_eq(ctx, mk_length(t, temp1), mk_int(ctx, (y_len - str_len)));
        }

        Z3_ast ax_l = Z3_mk_and(ctx, 3, l_items);
        Z3_ast ax_r = Z3_mk_and(ctx, 3, r_items);

        //Cut Info
        addCutInfoMerge(temp1, sLevel, y);
        addCutInfoMerge(temp1, sLevel, m);

        addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
      } else {
        loopDetected = true;
#ifdef DEBUGLOG
        __debugPrint(logFile, "-------------------\n");
        __debugPrint(logFile, "[AVOID Looping Cut] Skip @ %d.\n", __LINE__);
        printCutVAR(t, m);
        printCutVAR(t, y);
        __debugPrint(logFile, "-------------------\n");
#endif
      }
    }
  } else if (splitType == 1) {
    //--------------------------------------
    // break option 2:
    //   |   x   |    y    |
    //   |   m   |   str   |
    //--------------------------------------
    Z3_ast ax_l1 = Z3_mk_eq(ctx, concatAst1, concatAst2);
    Z3_ast ax_l2 = mk_2_or(t, Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, m)), Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, strAst)));
    Z3_ast ax_l = mk_2_and(t, ax_l1, ax_l2);
    Z3_ast ax_r = mk_2_and(t, Z3_mk_eq(ctx, x, m), Z3_mk_eq(ctx, y, strAst));
    addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
  } else if (splitType == 2) {
    //--------------------------------------------------------
    // m cut y,
    //    |   x   |  y  |
    //    | m |   str   |
    //--------------------------------------------------------
    int lenDelta = 0;
    Z3_ast l_items[3];
    int l_count = 0;
    l_items[0] = Z3_mk_eq(ctx, concatAst1, concatAst2);
    if (x_len != -1 && m_len != -1) {
      l_items[1] = Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len));
      l_items[2] = Z3_mk_eq(ctx, mk_length(t, m), mk_int(ctx, m_len));
      l_count = 3;
      lenDelta = x_len - m_len;
    } else {
      l_items[1] = Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len));
      l_count = 2;
      lenDelta = str_len - y_len;
    }
    std::string part1Str = strValue.substr(0, lenDelta);
    std::string part2Str = strValue.substr(lenDelta, strValue.size() - lenDelta);

    Z3_ast prefixStr = my_mk_str_value(t, part1Str.c_str());
    Z3_ast x_concat = mk_concat(t, m, prefixStr);
    Z3_ast cropStr = my_mk_str_value(t, part2Str.c_str());

    if (canTwoNodesEq(t, x, x_concat) && canTwoNodesEq(t, y, cropStr)) {
      Z3_ast r_items[2];
      r_items[0] = Z3_mk_eq(ctx, x, x_concat);
      r_items[1] = Z3_mk_eq(ctx, y, cropStr);
      Z3_ast ax_l = Z3_mk_and(ctx, l_count, l_items);
      Z3_ast ax_r = Z3_mk_and(ctx, 2, r_items);

      addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
    } else {
      // negate! It's impossible to split str with these lengths
      __debugPrint(logFile, "[Conflict] Negate! It's impossible to split str with these lengths @ %d.\n", __LINE__);
      Z3_ast ax_l = Z3_mk_and(ctx, l_count, l_items);
      addAxiom(t, Z3_mk_not(ctx, ax_l), __LINE__);
    }

  } else {
    // have no idea about the length
    int optionTotal = 2 + strValue.length();
    Z3_ast * or_item = new Z3_ast[optionTotal];
    Z3_ast * and_item = new Z3_ast[1 + 6 + 4 * (strValue.length() + 1)];
    int option = 0;
    int pos = 1;

    Z3_ast temp1_strAst = mk_concat(t, temp1, strAst);
    //--------------------------------------------------------
    // m cut y
    //--------------------------------------------------------
    if (canTwoNodesEq(t, y, temp1_strAst)) {
      if (!avoidLoopCut || !(hasSelfCut(m, y))) {
        // break down option 2-1
        or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
        Z3_ast x_temp1 = mk_concat(t, x, temp1);
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, m, x_temp1));
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, temp1_strAst));

        Z3_ast addItems[2];
        addItems[0] = mk_length(t, x);
        addItems[1] = mk_length(t, temp1);
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, m), Z3_mk_add(ctx, 2, addItems)));

//        addItems[0] = mk_length(t, temp1);
//        addItems[1] = mk_length(t, strAst);
//        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), Z3_mk_add(ctx, 2, addItems)));

        option++;

        //Cut Info
        addCutInfoMerge(temp1, sLevel, y);
        addCutInfoMerge(temp1, sLevel, m);
      } else {
        loopDetected = true;
#ifdef DEBUGLOG
        __debugPrint(logFile, "-------------------\n");
        __debugPrint(logFile, "[AVOID Looping Cut] Skip @ %d.\n", __LINE__);
        printCutVAR(t, m);
        printCutVAR(t, y);
        __debugPrint(logFile, "-------------------\n");
#endif
      }
    }

    for (int i = 0; i <= (int) strValue.size(); i++) {
      std::string part1Str = strValue.substr(0, i);
      std::string part2Str = strValue.substr(i, strValue.size() - i);
      Z3_ast prefixStr = my_mk_str_value(t, part1Str.c_str());
      Z3_ast x_concat = mk_concat(t, m, prefixStr);
      Z3_ast cropStr = my_mk_str_value(t, part2Str.c_str());
      if (canTwoNodesEq(t, x, x_concat) && canTwoNodesEq(t, y, cropStr)) {
        // break down option 2-2
        or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, x_concat));
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, cropStr));

//        if (part1Str.length() == 0) {
//          and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, m)));
//        } else {
//          Z3_ast addItems[2];
//          addItems[0] = mk_length(t, m);
//          addItems[1] = mk_int(ctx, part1Str.length());
//          and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), Z3_mk_add(ctx, 2, addItems)));
//        }
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, part2Str.length())));

        // adding length constraint for _ = constStr seems slowing things down.
        option++;
      }
    }

    if (option > 0) {
      if (option == 1)
        and_item[0] = or_item[0];
      else
        and_item[0] = Z3_mk_or(ctx, option, or_item);
      Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
      addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
    } else {
#ifdef DEBUGLOG
      __debugPrint(logFile, "\n[STOP @ %d] Should not split two EQ concats\n\n", __LINE__);
#endif
      return;
    }
    delete[] or_item;
    delete[] and_item;
    return;
  }
}


/*************************************************************
 * Type 3: concat(x, y) = concat("str", n)
 *************************************************************/
bool isConcatEqType_3(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if (isConstStr(t, v1_arg0) && (!isConstStr(t, v1_arg1)) && (!isConstStr(t, v2_arg0)) && (!isConstStr(t, v2_arg1))) {
    return true;
  } else if (isConstStr(t, v2_arg0) && (!isConstStr(t, v2_arg1)) && (!isConstStr(t, v1_arg0)) && (!isConstStr(t, v1_arg1))) {
    return true;
  } else {
    return false;
  }
}

/*
 *
 */

//#############################
//#  SimplifyConcatEq Type 3  #
//#---------------------------#
//concatAst1 = (Concat _!#_str3 _!#_str12)
//concatAst2 = (Concat __utma=218069774. _!#_str120)
//   ** |(Concat _!#_str3 _!#_str12)| = -1
//      ** |_!#_str3| = 7
//      ** |_!#_str12| = 13
//   ** |(Concat __utma=218069774. _!#_str120)| = -1
//      ** |"__utma=218069774."| = 17
//      ** |_!#_str120| = -1
//#############################

void processConcatEqType_3(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 3  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  Z3_ast x = NULL;
  Z3_ast y = NULL;
  Z3_ast strAst = NULL;
  Z3_ast n = NULL;

  if (getNodeType(t, v1_arg0) == my_Z3_ConstStr && getNodeType(t, v2_arg0) != my_Z3_ConstStr) {
    strAst = v1_arg0;
    n = v1_arg1;
    x = v2_arg0;
    y = v2_arg1;
  } else {
    strAst = v2_arg0;
    n = v2_arg1;
    x = v1_arg0;
    y = v1_arg1;
  }

  // -----------------------------
  // type 3:
  // x . y = str . n
  // -----------------------------
  std::string strValue = getConstStrValue(t, strAst);
  int x_len = getLenValue(t, x);
  int y_len = getLenValue(t, y);
  int str_len = getLenValue(t, strAst);
  int n_len = getLenValue(t, n);

  Z3_ast xorFlag = NULL;
  Z3_ast temp1 = NULL;
  std::pair<Z3_ast, Z3_ast> key1(concatAst1, concatAst2);
  std::pair<Z3_ast, Z3_ast> key2(concatAst2, concatAst1);
  if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
    temp1 = my_mk_nonEmpty_string_var(t);
    xorFlag = mk_internal_xor_var(t);

    varForBreakConcat[key1][0] = temp1;
    varForBreakConcat[key1][1] = xorFlag;
  } else {
    if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
      temp1 = varForBreakConcat[key1][0];
      xorFlag = varForBreakConcat[key1][1];
    } else if (varForBreakConcat.find(key2) != varForBreakConcat.end()) {
      temp1 = varForBreakConcat[key2][0];
      xorFlag = varForBreakConcat[key2][1];
    }
  }


  int splitType = -1;
  if (x_len != -1) {
    if (x_len < str_len)
      splitType = 0;
    else if (x_len == str_len)
      splitType = 1;
    else
      splitType = 2;
  }
  if (splitType == -1 && y_len != -1 && n_len != -1) {
    if (y_len > n_len)
      splitType = 0;
    else if (y_len == n_len)
      splitType = 1;
    else
      splitType = 2;
  }
  __debugPrint(logFile, ">> SplitType = %d @ %d.\n\n", splitType, __LINE__);

  // #############################################################################
  // Begin: providing less split options when length information is available
  // x . y = str. n
  if (splitType == 0) {
    //   |   x   |    y     |
    //   |  str     |   n   |
    std::vector<Z3_ast> litems;
    litems.push_back(Z3_mk_eq(ctx, concatAst1, concatAst2));
    int prefixLen = 0;
    if (x_len == -1) {
      prefixLen = str_len - (y_len - n_len);
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len)));
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, n_len)));
    } else {
      prefixLen = x_len;
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len)));
    }
    std::string prefixStr = strValue.substr(0, prefixLen);
    std::string suffixStr = strValue.substr(prefixLen, str_len - prefixLen);
    Z3_ast prefixAst = my_mk_str_value(t, prefixStr.c_str());
    Z3_ast suffixAst = my_mk_str_value(t, suffixStr.c_str());
    Z3_ast ax_l = mk_and_fromVector(t, litems);

    Z3_ast suf_n_concat = mk_concat(t, suffixAst, n);
    if (canTwoNodesEq(t, x, prefixAst) && canTwoNodesEq(t, y, suf_n_concat)) {
      Z3_ast r_items[2];
      r_items[0] = Z3_mk_eq(ctx, x, prefixAst);
      r_items[1] = Z3_mk_eq(ctx, y, suf_n_concat);
      addAxiom(t, Z3_mk_implies(ctx, ax_l, Z3_mk_and(ctx, 2, r_items)), __LINE__);
    } else {
      // negate! It's impossible to split str with these lengths
      __debugPrint(logFile, "[Conflict] Negate! It's impossible to split str with these lengths @ %d.\n", __LINE__);
      addAxiom(t, Z3_mk_not(ctx, ax_l), __LINE__);
    }
  }
  //
  else if (splitType == 1) {
    Z3_ast ax_l1 = Z3_mk_eq(ctx, concatAst1, concatAst2);
    Z3_ast ax_l2 = mk_2_or(t, Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, strAst)), Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, n)));
    Z3_ast ax_l = mk_2_and(t, ax_l1, ax_l2);
    Z3_ast ax_r = mk_2_and(t, Z3_mk_eq(ctx, x, strAst), Z3_mk_eq(ctx, y, n));
    addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
  }
  //
  else if (splitType == 2) {
    //   |   x        |    y     |
    //   |  str   |       n      |
    std::vector<Z3_ast> litems;
    litems.push_back(Z3_mk_eq(ctx, concatAst1, concatAst2));
    int tmpLen = 0;
    if (x_len == -1) {
      tmpLen = n_len - y_len;
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, y), mk_int(ctx, y_len)));
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, n), mk_int(ctx, n_len)));
    } else {
      tmpLen = x_len - str_len;
      litems.push_back(Z3_mk_eq(ctx, mk_length(t, x), mk_int(ctx, x_len)));
    }
    Z3_ast ax_l = mk_and_fromVector(t, litems);

    Z3_ast str_temp1 = mk_concat(t, strAst, temp1);
    Z3_ast temp1_y = mk_concat(t, temp1, y);
    if (canTwoNodesEq(t, x, str_temp1)) {
      if (!avoidLoopCut || !(hasSelfCut(x, n))) {
        Z3_ast r_items[3];
        r_items[0] = Z3_mk_eq(ctx, x, str_temp1);
        r_items[1] = Z3_mk_eq(ctx, n, temp1_y);
        r_items[2] = Z3_mk_eq(ctx, mk_length(t, temp1), mk_int(ctx, tmpLen));
        Z3_ast ax_r = Z3_mk_and(ctx, 3, r_items);

        //Cut Info
        addCutInfoMerge(temp1, sLevel, x);
        addCutInfoMerge(temp1, sLevel, n);

        addAxiom(t, Z3_mk_implies(ctx, ax_l, ax_r), __LINE__);
      } else {
        loopDetected = true;
#ifdef DEBUGLOG
        __debugPrint(logFile, "-------------------\n");
        __debugPrint(logFile, "[AVOID Looping Cut] Skip @ %d.\n", __LINE__);
        printCutVAR(t, x);
        printCutVAR(t, n);
        __debugPrint(logFile, "-------------------\n");
#endif
      }
    }
//    else {
//      // negate! It's impossible to split str with these lengths
//      __debugPrint(logFile, "[Conflict] Negate! It's impossible to split str with these lengths @ %d.\n", __LINE__);
//      addAxiom(t, Z3_mk_not(ctx, ax_l), __LINE__);
//    }
  }
  // we know nothing about the length.
  else {
    std::string strValue = getConstStrValue(t, strAst);
    int optionTotal = 2 + strValue.length();
    Z3_ast * or_item = new Z3_ast[optionTotal];
    int option = 0;
    Z3_ast * and_item = new Z3_ast[2 + 4 * optionTotal];
    int pos = 1;
    for (int i = 0; i <= (int) strValue.size(); i++) {
      std::string part1Str = strValue.substr(0, i);
      std::string part2Str = strValue.substr(i, strValue.size() - i);
      Z3_ast cropStr = my_mk_str_value(t, part1Str.c_str());
      Z3_ast suffixStr = my_mk_str_value(t, part2Str.c_str());
      Z3_ast y_concat = mk_concat(t, suffixStr, n);

      if (canTwoNodesEq(t, x, cropStr) && canTwoNodesEq(t, y, y_concat)) {
        // break down option 3-1
        Z3_ast x_eq_str = Z3_mk_eq(ctx, x, cropStr);
        or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], x_eq_str);
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, y_concat));

        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), mk_length(t, cropStr)));
//        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, y_concat)));

        // adding length constraint for _ = constStr seems slowing things down.
        option++;
      }
    }

    Z3_ast strAst_temp1 = mk_concat(t, strAst, temp1);

    //--------------------------------------------------------
    // x cut n
    //--------------------------------------------------------
    if (canTwoNodesEq(t, x, strAst_temp1)) {
      if (!avoidLoopCut || !(hasSelfCut(x, n))) {
        // break down option 3-2
        or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));

        Z3_ast temp1_y = mk_concat(t, temp1, y);
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, x, strAst_temp1));
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, n, temp1_y));

        Z3_ast addItems[2];
        addItems[0] = mk_length(t, strAst);
        addItems[1] = mk_length(t, temp1);
        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, x), Z3_mk_add(ctx, 2, addItems)));

//        addItems[0] = mk_length(t, temp1);
//        addItems[1] = mk_length(t, y);
//        and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, n), Z3_mk_add(ctx, 2, addItems)));

        option++;

        //--- Cut Info----
        addCutInfoMerge(temp1, sLevel, x);
        addCutInfoMerge(temp1, sLevel, n);
      } else {
        loopDetected = true;
#ifdef DEBUGLOG
        __debugPrint(logFile, "-------------------\n");
        __debugPrint(logFile, "[AVOID Loop] Skip @ %d.\n", __LINE__);
        printCutVAR(t, x);
        printCutVAR(t, n);
        __debugPrint(logFile, "-------------------\n");
#endif
      }
    }

    if (option > 0) {
      if (option == 1)
        and_item[0] = or_item[0];
      else
        and_item[0] = Z3_mk_or(ctx, option, or_item);
      Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
      addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
    } else {
#ifdef DEBUGLOG
      __debugPrint(logFile, "\n[STOP @ %d] Should not split two EQ concats\n\n", __LINE__);
#endif
      return;
    }
    delete[] or_item;
    delete[] and_item;
    return;
  }
}

/*************************************************************
 * Type 4: concat("str1", y) = concat("str2", n)
 *************************************************************/
bool isConcatEqType_4(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if (isConstStr(t, v1_arg0) && (!isConstStr(t, v1_arg1)) && isConstStr(t, v2_arg0) && (!isConstStr(t, v2_arg1))) {
    return true;
  } else {
    return false;
  }
}

/*
 *
 */
void processConcatEqType_4(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 4  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  Z3_ast str1Ast = v1_arg0;
  Z3_ast y = v1_arg1;
  Z3_ast str2Ast = v2_arg0;
  Z3_ast n = v2_arg1;
  std::string str1Value = getConstStrValue(t, str1Ast);
  std::string str2Value = getConstStrValue(t, str2Ast);

  int str1Len = str1Value.length();
  int str2Len = str2Value.length();

  int commonLen = (str1Len > str2Len) ? str2Len : str1Len;
  if (str1Value.substr(0, commonLen) != str2Value.substr(0, commonLen)) {
#ifdef DEBUGLOG
    __debugPrint(logFile, ">> [simplifyConcatEq] Conflict: ");
    printZ3Node(t, concatAst1);
    __debugPrint(logFile, " = ");
    printZ3Node(t, concatAst2);
    __debugPrint(logFile, " @ %d\n\n", __LINE__);
#endif
    Z3_ast toNegate = Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2));
    addAxiom(t, toNegate, __LINE__);
    return;
  } else {
    if (str1Len > str2Len) {
      std::string deltaStr = str1Value.substr(str2Len, str1Len - str2Len);
      Z3_ast tmpAst = mk_concat(t, my_mk_str_value(t, deltaStr.c_str()), y);
      if (!inSameEqc(t, tmpAst, n)) {
        // break down option 4-1
        Z3_ast implyR = Z3_mk_eq(ctx, n, tmpAst);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    } else if (str1Len == str2Len) {
      if (!inSameEqc(t, n, y)) {
        //break down option 4-2
        Z3_ast implyR = Z3_mk_eq(ctx, n, y);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    } else {
      std::string deltaStr = str2Value.substr(str1Len, str2Len - str1Len);
      Z3_ast tmpAst = mk_concat(t, my_mk_str_value(t, deltaStr.c_str()), n);
      if (!inSameEqc(t, y, tmpAst)) {
        //break down option 4-3
        Z3_ast implyR = Z3_mk_eq(ctx, y, tmpAst);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    }
  }
}


/*************************************************************
 *  case 5: concat(x, "str1") = concat(m, "str2")
 *************************************************************/
bool isConcatEqType_5(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if ((!isConstStr(t, v1_arg0)) && isConstStr(t, v1_arg1) && (!isConstStr(t, v2_arg0)) && isConstStr(t, v2_arg1)) {
    return true;
  } else {
    return false;
  }
}

/*
 *
 */
void processConcatEqType_5(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 5  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  Z3_ast x = v1_arg0;
  Z3_ast str1Ast = v1_arg1;
  Z3_ast m = v2_arg0;
  Z3_ast str2Ast = v2_arg1;
  std::string str1Value = getConstStrValue(t, str1Ast);
  std::string str2Value = getConstStrValue(t, str2Ast);
  int str1Len = str1Value.length();
  int str2Len = str2Value.length();

  int cLen = (str1Len > str2Len) ? str2Len : str1Len;
  if (str1Value.substr(str1Len - cLen, cLen) != str2Value.substr(str2Len - cLen, cLen)) {
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n\n>> [processConcatEqType_5] Conflict: ");
    printZ3Node(t, concatAst1);
    __debugPrint(logFile, " = ");
    printZ3Node(t, concatAst2);
    __debugPrint(logFile, " @ %d\n\n", __LINE__);
#endif
    Z3_ast toNegate = Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2));
    addAxiom(t, toNegate, __LINE__);
    return;
  } else {
    if (str1Len > str2Len) {
      std::string deltaStr = str1Value.substr(0, str1Len - str2Len);
      Z3_ast x_deltaStr = mk_concat(t, x, my_mk_str_value(t, deltaStr.c_str()));
      if (!inSameEqc(t, m, x_deltaStr)) {
        Z3_ast implyR = Z3_mk_eq(ctx, m, x_deltaStr);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    } else if (str1Len == str2Len) {
      // test
      if (!inSameEqc(t, x, m)) {
        Z3_ast implyR = Z3_mk_eq(ctx, x, m);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    } else {
      std::string deltaStr = str2Value.substr(0, str2Len - str1Len);
      Z3_ast m_deltaStr = mk_concat(t, m, my_mk_str_value(t, deltaStr.c_str()));
      if (!inSameEqc(t, x, m_deltaStr)) {
        Z3_ast implyR = Z3_mk_eq(ctx, x, m_deltaStr);
        addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
      }
    }
  }
}


/*************************************************************
 *  case 6: concat("str1", y) = concat(m, "str2")
 *************************************************************/
bool isConcatEqType_6(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  if (isConstStr(t, v1_arg0) && (!isConstStr(t, v1_arg1)) && (!isConstStr(t, v2_arg0)) && isConstStr(t, v2_arg1)) {
    return true;
  } else if (isConstStr(t, v2_arg0) && (!isConstStr(t, v2_arg1)) && (!isConstStr(t, v1_arg0)) && isConstStr(t, v1_arg1)) {
    return true;
  } else {
    return false;
  }
}

/*
 *
 */
void processConcatEqType_6(Z3_theory t, Z3_ast concatAst1, Z3_ast concatAst2) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "#############################\n");
  __debugPrint(logFile, "#  SimplifyConcatEq Type 6  #\n");
  __debugPrint(logFile, "#---------------------------#\n");
  __debugPrint(logFile, "concatAst1 = ");
  printZ3Node(t, concatAst1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "concatAst2 = ");
  printZ3Node(t, concatAst2);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst1);
  printStrArgLen(t, concatAst2);
  __debugPrint(logFile, "#############################\n");
#endif

  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst2), 1);

  Z3_ast str1Ast = NULL;
  Z3_ast y = NULL;
  Z3_ast m = NULL;
  Z3_ast str2Ast = NULL;

  if (getNodeType(t, v1_arg0) == my_Z3_ConstStr) {
    str1Ast = v1_arg0;
    y = v1_arg1;
    m = v2_arg0;
    str2Ast = v2_arg1;
  } else {
    str1Ast = v2_arg0;
    y = v2_arg1;
    m = v1_arg0;
    str2Ast = v1_arg1;
  }

  std::string str1Value = getConstStrValue(t, str1Ast);
  std::string str2Value = getConstStrValue(t, str2Ast);
  //----------------------------------------
  //(a)  |---str1---|----y----|
  //     |--m--|-----str2-----|
  //
  //(b)  |---str1---|----y----|
  //     |-----m----|--str2---|
  //
  //(c)  |---str1---|----y----|
  //     |------m------|-str2-|
  //----------------------------------------
  std::list<int> overlapLen;
  overlapLen.push_back(0);
  int str1Len = str1Value.length();
  int str2Len = str2Value.length();
  for (int i = 1; i <= str1Len && i <= str2Len; i++) {
    if (str1Value.substr(str1Len - i, i) == str2Value.substr(0, i))
      overlapLen.push_back(i);
  }

  //----------------------------------------------------------------
  Z3_ast commonVar = NULL;
  Z3_ast xorFlag = NULL;
  std::pair<Z3_ast, Z3_ast> key1(concatAst1, concatAst2);
  std::pair<Z3_ast, Z3_ast> key2(concatAst2, concatAst1);
  if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
    commonVar = my_mk_nonEmpty_string_var(t);
    xorFlag = mk_internal_xor_var(t);
    varForBreakConcat[key1][0] = commonVar;
    varForBreakConcat[key1][1] = xorFlag;
  } else {
    if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
      commonVar = varForBreakConcat[key1][0];
      xorFlag = varForBreakConcat[key1][1];
    } else {
      commonVar = varForBreakConcat[key2][0];
      xorFlag = varForBreakConcat[key2][1];
    }
  }
  Z3_ast * or_item = new Z3_ast[overlapLen.size() + 1];
  int option = 0;
  Z3_ast * and_item = new Z3_ast[1 + 4 * (overlapLen.size() + 1)];
  int pos = 1;

  if (!avoidLoopCut || !hasSelfCut(m, y)) {
    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));

    Z3_ast str1_commonVar = mk_concat(t, str1Ast, commonVar);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, m, str1_commonVar));

    Z3_ast commonVar_str2 = mk_concat(t, commonVar, str2Ast);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, y, commonVar_str2));

    //
    Z3_ast addItems[2];
    addItems[0] = mk_length(t, str1Ast);
    addItems[1] = mk_length(t, commonVar);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, m), Z3_mk_add(ctx, 2, addItems)));

//    addItems[0] = mk_length(t, commonVar);
//    addItems[1] = mk_length(t, str2Ast);
//    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), Z3_mk_add(ctx, 2, addItems)));

    option++;
  } else {
    loopDetected = true;
#ifdef DEBUGLOG
    __debugPrint(logFile, "-------------------\n");
    __debugPrint(logFile, "[AVOID Loop] Skip @ %d.\n", __LINE__);
    printCutVAR(t, m);
    printCutVAR(t, y);
    __debugPrint(logFile, "-------------------\n");
#endif
  }

  for (std::list<int>::iterator itor = overlapLen.begin(); itor != overlapLen.end(); itor++) {
    int overLen = *itor;
    std::string prefix = str1Value.substr(0, str1Len - overLen);
    std::string suffix = str2Value.substr(overLen, str2Len - overLen);
    or_item[option] = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, option));

    Z3_ast prefixAst = my_mk_str_value(t, prefix.c_str());
    Z3_ast x_eq_prefix = Z3_mk_eq(ctx, m, prefixAst);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], x_eq_prefix);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, m), mk_length(t, prefixAst)));

    // adding length constraint for _ = constStr seems slowing things down.

    Z3_ast suffixAst = my_mk_str_value(t, suffix.c_str());
    Z3_ast y_eq_surfix = Z3_mk_eq(ctx, y, suffixAst);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], y_eq_surfix);
    and_item[pos++] = Z3_mk_eq(ctx, or_item[option], Z3_mk_eq(ctx, mk_length(t, y), mk_length(t, suffixAst)));
    option++;
  }

  //  case 6: concat("str1", y) = concat(m, "str2")
  and_item[0] = Z3_mk_or(ctx, option, or_item);
  Z3_ast implyR = Z3_mk_and(ctx, pos, and_item);
  addAxiom(t, Z3_mk_implies(ctx, Z3_mk_eq(ctx, concatAst1, concatAst2), implyR), __LINE__);
  delete[] or_item;
  delete[] and_item;
}


/* ===============================================================================
 * Handle two equivalent Concats. nn1 and nn2 are two concat functions
 * ===============================================================================*/
void simplifyConcatEq(Z3_theory t, Z3_ast nn1, Z3_ast nn2, int duplicateCheck) {
  Z3_context ctx = Z3_theory_get_context(t);

  Z3_ast a1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 0);
  Z3_ast a1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn1), 1);
  Z3_ast a2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 0);
  Z3_ast a2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, nn2), 1);

  int a1_arg0_len = getLenValue(t, a1_arg0);
  int a1_arg1_len = getLenValue(t, a1_arg1);
  int a2_arg0_len = getLenValue(t, a2_arg0);
  int a2_arg1_len = getLenValue(t, a2_arg1);

#ifdef DEBUGLOG
  __debugPrint(logFile, "\n\n\n");
  __debugPrint(logFile, "***********************************************\n");
  __debugPrint(logFile, "** simplifyConcatEq:\n");
  __debugPrint(logFile, "   nn1 = ");
  printZ3Node(t, nn1);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "   nn2 = ");
  printZ3Node(t, nn2);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "-----------------------------------------------\n");
  printStrArgLen(t, nn1);
  printStrArgLen(t, nn2);
  __debugPrint(logFile, "-----------------------------------------------\n");
#endif

  inferLenConcatEq(t, nn1, nn2);

  if (a1_arg0 == a2_arg0) {
    if (! inSameEqc(t, a1_arg1, a2_arg1)) {
      Z3_ast iil = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast items[2];
      items[0] = Z3_mk_eq(ctx, a1_arg1, a2_arg1);
      items[1] = Z3_mk_eq(ctx, mk_length(t, a1_arg1), mk_length(t, a2_arg1));
      Z3_ast toAdd = Z3_mk_implies(ctx, iil, Z3_mk_and(ctx, 2, items));
      addAxiom(t, toAdd, __LINE__);
    }
    __debugPrint(logFile, ">> [simplifyConcatEq] SKIP: a1_arg0 == a2_arg0 @ %d\n\n", __LINE__);
    return;
  }

  if (a1_arg1 == a2_arg1) {
    if (! inSameEqc(t, a1_arg0, a2_arg0)) {
      Z3_ast iil = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast items[2];
      items[0] = Z3_mk_eq(ctx, a1_arg0, a2_arg0);
      items[1] = Z3_mk_eq(ctx, mk_length(t, a1_arg0), mk_length(t, a2_arg0));
      Z3_ast toAdd = Z3_mk_implies(ctx, iil, Z3_mk_and(ctx, 2, items));
      addAxiom(t, toAdd, __LINE__);
    }
    __debugPrint(logFile, ">> [simplifyConcatEq] SKIP: a1_arg1 == a2_arg1 @ %d\n\n", __LINE__);
    return;
  }

  //-----------------------------------------
  // Quick Path
  //-----------------------------------------
  if (inSameEqc(t, a1_arg0, a2_arg0)) {
    if (inSameEqc(t, a1_arg1, a2_arg1)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] SKIP: inSameEqc(a1_arg0, a2_arg0) && inSameEqc(a1_arg1, a2_arg1) @ %d\n\n", __LINE__);
      return;
    } else {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 1-1: inSameEqc(a1_arg0, a2_arg0) @ %d\n\n", __LINE__);
      Z3_ast ax_l = mk_2_and(t, Z3_mk_eq(ctx, nn1, nn2), Z3_mk_eq(ctx, a1_arg0, a2_arg0));
      Z3_ast ax_r = mk_2_and(t, Z3_mk_eq(ctx, a1_arg1, a2_arg1), Z3_mk_eq(ctx, mk_length(t, a1_arg1), mk_length(t, a2_arg1)));
      Z3_ast toAdd = Z3_mk_implies(ctx,ax_l, ax_r);
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }
  //
  else {
    if (inSameEqc(t, a1_arg1, a2_arg1)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 1-2: inSameEqc(a1_arg1, a1_arg1) @ %d\n\n", __LINE__);
      Z3_ast ax_l = mk_2_and(t, Z3_mk_eq(ctx, nn1, nn2), Z3_mk_eq(ctx, a1_arg1, a2_arg1));
      Z3_ast ax_r = mk_2_and(t, Z3_mk_eq(ctx, a1_arg0, a2_arg0), Z3_mk_eq(ctx, mk_length(t, a1_arg0), mk_length(t, a2_arg0)));
      Z3_ast toAdd = Z3_mk_implies(ctx,ax_l, ax_r);
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }

  if(a1_arg0_len != -1 && a2_arg0_len != -1 && a1_arg0_len == a2_arg0_len){
    if (! inSameEqc(t, a1_arg0, a2_arg0)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 2-1: len(nn1.arg0) == len(nn2.arg0)\n");
      Z3_ast ax_l1 = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast ax_l2 = Z3_mk_eq(ctx, mk_length(t, a1_arg0), mk_length(t, a2_arg0));
      Z3_ast ax_r1 = Z3_mk_eq(ctx, a1_arg0, a2_arg0);
      Z3_ast ax_r2 = Z3_mk_eq(ctx, a1_arg1, a2_arg1);
      Z3_ast toAdd = Z3_mk_implies(ctx, mk_2_and(t, ax_l1, ax_l2), mk_2_and(t, ax_r1, ax_r2));
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }

  if (a1_arg1_len != -1 && a2_arg1_len != -1 && a1_arg1_len == a2_arg1_len)
  {
    if (!inSameEqc(t, a1_arg1, a2_arg1)) {
      __debugPrint(logFile, ">> [simplifyConcatEq] Quick Path 2-2: len(nn1.arg1) == len(nn2.arg1)\n");
      Z3_ast ax_l1 = Z3_mk_eq(ctx, nn1, nn2);
      Z3_ast ax_l2 = Z3_mk_eq(ctx, mk_length(t, a1_arg1), mk_length(t, a2_arg1));
      Z3_ast ax_r1 = Z3_mk_eq(ctx, a1_arg0, a2_arg0);
      Z3_ast ax_r2 = Z3_mk_eq(ctx, a1_arg1, a2_arg1);
      Z3_ast toAdd = Z3_mk_implies(ctx, mk_2_and(t, ax_l1, ax_l2), mk_2_and(t, ax_r1, ax_r2));
      addAxiom(t, toAdd, __LINE__);
      return;
    }
  }

  //-----------------------------------------

  Z3_ast new_nn1 = simplifyConcat(t, nn1);
  Z3_ast new_nn2 = simplifyConcat(t, nn2);
  Z3_ast v1_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, new_nn1), 0);
  Z3_ast v1_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, new_nn1), 1);
  Z3_ast v2_arg0 = Z3_get_app_arg(ctx, Z3_to_app(ctx, new_nn2), 0);
  Z3_ast v2_arg1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, new_nn2), 1);

  // --------------------------------------------------

#ifdef DEBUGLOG
  __debugPrint(logFile, "--------------------------------------------\n");
  __debugPrint(logFile, "@ %d\n", __LINE__);
  __debugPrint(logFile, ">>> new_nn1 = ");
  printZ3Node(t, new_nn1);
  __debugPrint(logFile, "\n>>> new_nn2 = ");
  printZ3Node(t, new_nn2);
  __debugPrint(logFile, "\n");
  __debugPrint(logFile, "--------------------------------------------\n");
#endif

  if (new_nn1 == new_nn2) {
    __debugPrint(logFile, ">> Eq concats, return.\n");
    return;
  }

  if (!canTwoNodesEq(t, new_nn1, new_nn2)) {
    Z3_ast detected = Z3_mk_not(ctx, Z3_mk_eq(ctx, new_nn1, new_nn2));
    __debugPrint(logFile, "\n");
    __debugPrint(logFile, ">> Inconsistent detected in simplifyConcatEq:\n");
    addAxiom(t, detected, __LINE__);
    __debugPrint(logFile, "\n\n");
    return;
  }

  // Check whether new_nn1 and new_nn2 are still two concats

  bool n1IsConcat = isConcatFunc(t, new_nn1);
  bool n2IsConcat = isConcatFunc(t, new_nn2);
  if (!n1IsConcat && n2IsConcat) {
    __debugPrint(logFile, ">> [simplifyConcatEq] nn1_new is not a concat @ %d\n\n", __LINE__);
    if (getNodeType(t, new_nn1) == my_Z3_ConstStr)
      simplifyParent(t, new_nn2, new_nn1);
    return;
  } else if (n1IsConcat && !n2IsConcat) {
    __debugPrint(logFile, ">> [simplifyConcatEq] nn2_new is not a concat @ %d\n\n", __LINE__);
    if (getNodeType(t, new_nn2) == my_Z3_ConstStr)
      simplifyParent(t, new_nn1, new_nn2);
    return;
  }


  if (!inSameEqc(t, new_nn1, new_nn2) && (nn1 != new_nn1 || nn2 != new_nn2)) {
    int ii4 = 0;
    Z3_ast item[3];
    if (nn1 != new_nn1)
      item[ii4++] = Z3_mk_eq(ctx, nn1, new_nn1);
    if (nn2 != new_nn2)
      item[ii4++] = Z3_mk_eq(ctx, nn2, new_nn2);
    item[ii4++] = Z3_mk_eq(ctx, nn1, nn2);

    Z3_ast implyL = my_mk_and(t, item, ii4);
    Z3_ast implyR = Z3_mk_eq(ctx, new_nn1, new_nn2);
    addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
  }

  //*****************************************************
  // Start to split two Concats
  //*****************************************************
  checkandInit_cutVAR(t, v1_arg0);
  checkandInit_cutVAR(t, v1_arg1);
  checkandInit_cutVAR(t, v2_arg0);
  checkandInit_cutVAR(t, v2_arg1);

  //*************************************************************
  // case 1: concat(x, y) = concat(m, n)
  //*************************************************************
  if (isConcatEqType_1(t, new_nn1, new_nn2)) {
    processConcatEqType_1(t, new_nn1, new_nn2);
    return;
  }

  //*************************************************************
  // case 2: concat(x, y) = concat(m, "str")
  //*************************************************************
  if (isConcatEqType_2(t, new_nn1, new_nn2)) {
    processConcatEqType_2(t, new_nn1, new_nn2);
    return;
  }

  //*************************************************************
  // case 3: concat(x, y) = concat("str", n)
  //*************************************************************
  if (isConcatEqType_3(t, new_nn1, new_nn2)) {
    processConcatEqType_3(t, new_nn1, new_nn2);
    return;
  }

  //*************************************************************
  //  case 4: concat("str1", y) = concat("str2", n)
  //*************************************************************
  if (isConcatEqType_4(t, new_nn1, new_nn2)) {
    processConcatEqType_4(t, new_nn1, new_nn2);
    return;
  }

  //*************************************************************
  //  case 5: concat(x, "str1") = concat(m, "str2")
  //*************************************************************
  if (isConcatEqType_5(t, new_nn1, new_nn2)) {
    processConcatEqType_5(t, new_nn1, new_nn2);
    return;
  }
  //*************************************************************
  //  case 6: concat("str1", y) = concat(m, "str2")
  //*************************************************************
  if (isConcatEqType_6(t, new_nn1, new_nn2)) {
    processConcatEqType_6(t, new_nn1, new_nn2);
    return;
  }
}



//------------------------------------------------------------
// solve concat of pattern:
//    constStr == Concat( constrStr, xx )
//    constStr == Concat( xx, constrStr )
//------------------------------------------------------------
void solve_concat_eq_str(Z3_theory t, Z3_ast concatAst, Z3_ast constStr) {
#ifdef DEBUGLOG
  __debugPrint(logFile, "\n\n===============================\n");
  __debugPrint(logFile, "**** solve_concat_eq_str:\n");
  printZ3Node(t, concatAst);
  __debugPrint(logFile, " = ");
  printZ3Node(t, constStr);
  __debugPrint(logFile, "\n");
  printStrArgLen(t, concatAst);
  printStrArgLen(t, constStr);
  __debugPrint(logFile, "===============================\n");
#endif
  Z3_context ctx = Z3_theory_get_context(t);
  if (isConcatFunc(t, concatAst) && isConstStr(t, constStr)) {
    std::string const_str = getConstStrValue(t, constStr);
    Z3_ast a1 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst), 0);
    Z3_ast a2 = Z3_get_app_arg(ctx, Z3_to_app(ctx, concatAst), 1);

    if (const_str == "") {
#ifdef DEBUGLOG
  __debugPrint(logFile, " >> quick path ...\n");
#endif
      Z3_ast empty1 = Z3_mk_eq(ctx, a1, constStr);
      Z3_ast empty2 = Z3_mk_eq(ctx, a2, constStr);
      Z3_ast epL = Z3_mk_eq(ctx,  concatAst, constStr);
      Z3_ast epR = mk_2_and(t, empty1, empty2);
      addAxiom(t, Z3_mk_implies(ctx, epL, epR), __LINE__);
      return;
    }
    bool arg1HasEqcValue = false;
    bool arg2HasEqcValue = false;
    Z3_ast arg1 = get_eqc_value(t, a1, arg1HasEqcValue);
    Z3_ast arg2 = get_eqc_value(t, a2, arg2HasEqcValue);
    Z3_ast newConcat = NULL;
    if (arg1 != a1 || arg2 != a2) {
      int iPos = 0;
      Z3_ast item1[2];
      if (a1 != arg1)
        item1[iPos++] = Z3_mk_eq(ctx, a1, arg1);
      if (a2 != arg2)
        item1[iPos++] = Z3_mk_eq(ctx, a2, arg2);
      Z3_ast implyL1 = NULL;
      if (iPos == 1)
        implyL1 = item1[0];
      else
        implyL1 = Z3_mk_and(ctx, 2, item1);

      newConcat = mk_concat(t, arg1, arg2);

      if (newConcat != constStr) {
        Z3_ast implyR1 = Z3_mk_eq(ctx, concatAst, newConcat);
        addAxiom(t, Z3_mk_implies(ctx, implyL1, implyR1), __LINE__);
      }
    } else {
      newConcat = concatAst;
    }

    if (newConcat == constStr)
      return;

    if (!isConcatFunc(t, newConcat))
      return;

    //---------------------------------------------------------------------
    // (1) Concat(const_Str, const_Str) = const_Str
    //---------------------------------------------------------------------
    if (arg1HasEqcValue && arg2HasEqcValue) {
      std::string arg1_str = getConstStrValue(t, arg1);
      std::string arg2_str = getConstStrValue(t, arg2);
      std::string result_str = arg1_str + arg2_str;
      if (result_str != const_str) {
        // negate
        addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst, constStr)), __LINE__);
        return;
      }
    }

    //---------------------------------------------------------------------
    // (2) Concat( var, const_Str ) = const_Str
    //---------------------------------------------------------------------
    else if (!arg1HasEqcValue && arg2HasEqcValue) {
      std::string arg2_str = getConstStrValue(t, arg2);
      int resultStrLen = const_str.length();
      int arg2StrLen = arg2_str.length();
      if (resultStrLen < arg2StrLen) {
        // negate
        addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr)), __LINE__);
        return;
      } else {
        int varStrLen = resultStrLen - arg2StrLen;
        std::string firstPart = const_str.substr(0, varStrLen);
        std::string secondPart = const_str.substr(varStrLen, arg2StrLen);
        if (arg2_str != secondPart) {
          // negate
          Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr));
          addAxiom(t, negateAst, __LINE__);
          return;
        } else {
          Z3_ast tmpStrConst = my_mk_str_value(t, firstPart.c_str());
          Z3_ast implyL = Z3_mk_eq(ctx, newConcat, constStr);
          Z3_ast implyR = Z3_mk_eq(ctx, arg1, tmpStrConst);
          addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
        }
      }
    }

    //---------------------------------------------------------------------
    // (3) Concat(const_Str, var) = const_Str
    //---------------------------------------------------------------------
    else if (arg1HasEqcValue && !arg2HasEqcValue) {
      std::string arg1_str = getConstStrValue(t, arg1);
      int resultStrLen = const_str.length();
      int arg1StrLen = arg1_str.length();
      if (resultStrLen < arg1StrLen) {
        // negate
        addAxiom(t, Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr)), __LINE__);
        return;
      } else {
        int varStrLen = resultStrLen - arg1StrLen;
        std::string firstPart = const_str.substr(0, arg1StrLen);
        std::string secondPart = const_str.substr(arg1StrLen, varStrLen);
        if (arg1_str != firstPart) {
          // negate
          Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, newConcat, constStr));
          addAxiom(t, negateAst, __LINE__);
          return;
        } else {
          Z3_ast tmpStrConst = my_mk_str_value(t, secondPart.c_str());
          Z3_ast implyL = Z3_mk_eq(ctx, newConcat, constStr);
          Z3_ast implyR = Z3_mk_eq(ctx, arg2, tmpStrConst);
          addAxiom(t, Z3_mk_implies(ctx, implyL, implyR), __LINE__);
        }
      }
    }
    //---------------------------------------------------------------------
    // (4) Concat(var, var) = const_Str
    //     Only when arg1 and arg2 do not have eq constant string values
    //---------------------------------------------------------------------
    else {
      if (Concat(t, arg1, arg2) == NULL) {
        int arg1Len = getLenValue(t, arg1);
        int arg2Len = getLenValue(t, arg2);
        int concatStrLen = const_str.length();
#ifdef DEBUGLOG
        __debugPrint(logFile, "  >> Len( ");
        printZ3Node(t, concatAst);
        __debugPrint(logFile, " ) = %d\n", getLenValue(t, concatAst));
        __debugPrint(logFile, "    -> Len( ");
        printZ3Node(t, arg1);
        __debugPrint(logFile, " ) = %d\n", getLenValue(t, arg1));
        __debugPrint(logFile, "    -> Len( ");
        printZ3Node(t, arg2);
        __debugPrint(logFile, " ) = %d\n", getLenValue(t, arg2));

        __debugPrint(logFile, "  >> Len( ");
        printZ3Node(t, constStr);
        __debugPrint(logFile, " ) = %d\n\n", getLenValue(t, constStr));
#endif

        if (arg1Len != -1 || arg2Len != -1) {
          Z3_ast ax_l1 = Z3_mk_eq(ctx, concatAst, constStr);
          Z3_ast ax_l2 = NULL;

          std::string prefixStr;
          std::string suffixStr;
          if (arg1Len != -1) {
            if (arg1Len < 0) {
              __debugPrint(logFile, "[Length conflict]  arg1Len = %d, concatStrLen = %d @ %d\n", arg1Len,  concatStrLen, __LINE__);
              Z3_ast toAss1 = Z3_mk_ge(ctx, mk_length(t, arg1), mk_int(ctx, 0));
              addAxiom(t, toAss1, __LINE__);
              return;
            } else if (arg1Len > concatStrLen) {
              __debugPrint(logFile, "[Length conflict]  arg1Len = %d, concatStrLen = %d @ %d\n", arg1Len,  concatStrLen, __LINE__);
              Z3_ast toAss1 = Z3_mk_implies(ctx, ax_l1, Z3_mk_le(ctx, mk_length(t, arg1), mk_int(ctx, concatStrLen)));
              addAxiom(t, toAss1, __LINE__);
              return;
            }

            prefixStr = const_str.substr(0, arg1Len);
            suffixStr = const_str.substr(arg1Len, concatStrLen - arg1Len);
            ax_l2 = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, arg1Len));
          } else {
            // arg2's length is available
            if (arg2Len < 0) {
              __debugPrint(logFile, "[Length conflict]  arg2Len = %d, concatStrLen = %d @ %d\n", arg2Len,  concatStrLen, __LINE__);
              Z3_ast toAss1 = Z3_mk_ge(ctx, mk_length(t, arg2), mk_int(ctx, 0));
              addAxiom(t, toAss1, __LINE__);
              return;
            } else if (arg2Len > concatStrLen) {
              __debugPrint(logFile, "[Length conflict]  arg2Len = %d, concatStrLen = %d @ %d\n", arg2Len,  concatStrLen, __LINE__);
              Z3_ast toAss1 = Z3_mk_implies(ctx, ax_l1, Z3_mk_le(ctx, mk_length(t, arg2), mk_int(ctx, concatStrLen)));
              addAxiom(t, toAss1, __LINE__);
              return;
            }

            prefixStr = const_str.substr(0, concatStrLen - arg2Len);
            suffixStr = const_str.substr(concatStrLen - arg2Len, arg2Len);
            ax_l2 = Z3_mk_eq(ctx, mk_length(t, arg2), mk_int(ctx, arg2Len));
          }

          // consistency check
          if (isConcatFunc(t, arg1) && canConcatEqStr(t, arg1, prefixStr) == 0) {
            // inconsistency found, need to backtrack
            Z3_ast ax_r = Z3_mk_not(ctx, ax_l2);
            addAxiom(t, Z3_mk_implies(ctx, ax_l1, ax_r), __LINE__);
            return;
          }
          if (isConcatFunc(t, arg2) && canConcatEqStr(t, arg2, suffixStr) == 0) {
            // inconsistency found, need to backtrack
            Z3_ast ax_r = Z3_mk_not(ctx, ax_l2);
            addAxiom(t, Z3_mk_implies(ctx, ax_l1, ax_r), __LINE__);
            return;
          }

          Z3_ast r_items[3];
          r_items[0] = Z3_mk_eq(ctx, arg1, my_mk_str_value(t, prefixStr.c_str()));
          r_items[1] = Z3_mk_eq(ctx, arg2, my_mk_str_value(t, suffixStr.c_str()));
          int r_count = 2;
          if (arg1Len == -1) {
            r_items[2] = Z3_mk_eq(ctx, mk_length(t, arg1), mk_int(ctx, prefixStr.size()));
            r_count++;
          }
          else if (arg2Len == -1) {
            r_items[2] = Z3_mk_eq(ctx, mk_length(t, arg2), mk_int(ctx, suffixStr.size()));
            r_count++;
          }

          addAxiom(t, Z3_mk_implies(ctx, mk_2_and(t, ax_l1, ax_l2), Z3_mk_and(ctx, r_count, r_items)), __LINE__);
        } else {
          Z3_ast xorFlag = NULL;
          std::pair<Z3_ast, Z3_ast> key1(arg1, arg2);
          std::pair<Z3_ast, Z3_ast> key2(arg2, arg1);
          if (varForBreakConcat.find(key1) == varForBreakConcat.end() && varForBreakConcat.find(key2) == varForBreakConcat.end()) {
            xorFlag = mk_internal_xor_var(t);
            varForBreakConcat[key1][0] = xorFlag;
          } else {
            if (varForBreakConcat.find(key1) != varForBreakConcat.end()) {
              xorFlag = varForBreakConcat[key1][0];
            } else {
              xorFlag = varForBreakConcat[key2][0];
            }
          }

          int concatStrLen = const_str.length();
          int xor_pos = 0;
          int and_count = 1;
          Z3_ast * xor_items = new Z3_ast[concatStrLen + 1];
          Z3_ast * and_items = new Z3_ast[4 * (concatStrLen + 1) + 1];
          Z3_ast arg1_eq = NULL;
          Z3_ast arg2_eq = NULL;
          for (int i = 0; i < concatStrLen + 1; i++) {
            std::string prefixStr = const_str.substr(0, i);
            std::string suffixStr = const_str.substr(i, concatStrLen - i);

            // skip invalidate options
            if (isConcatFunc(t, arg1) && canConcatEqStr(t, arg1, prefixStr) == 0) {
              continue;
            }
            if (isConcatFunc(t, arg2) && canConcatEqStr(t, arg2, suffixStr) == 0) {
              continue;
            }

            Z3_ast xorAst = Z3_mk_eq(ctx, xorFlag, mk_int(ctx, xor_pos));
            xor_items[xor_pos++] = xorAst;

            Z3_ast prefixAst = my_mk_str_value(t, prefixStr.c_str());
            arg1_eq = Z3_mk_eq(ctx, arg1, prefixAst);
            and_items[and_count++] = Z3_mk_eq(ctx, xorAst, arg1_eq);

            Z3_ast suffixAst = my_mk_str_value(t, suffixStr.c_str());
            arg2_eq = Z3_mk_eq(ctx, arg2, suffixAst);
            and_items[and_count++] = Z3_mk_eq(ctx, xorAst, arg2_eq);
          }

          Z3_ast implyL = Z3_mk_eq(ctx, concatAst, constStr);
          Z3_ast implyR1 = NULL;
          if (xor_pos == 0) {
            // negate
            Z3_ast negateAst = Z3_mk_not(ctx, Z3_mk_eq(ctx, concatAst, constStr));
            addAxiom(t, negateAst, __LINE__);
          } else {
            if (xor_pos == 1) {
              and_items[0] = xor_items[0];
              implyR1 = Z3_mk_and(ctx, and_count, and_items);
            } else {
              and_items[0] = Z3_mk_or(ctx, xor_pos, xor_items);
              implyR1 = Z3_mk_and(ctx, and_count, and_items);
            }
            Z3_ast implyToAssert = Z3_mk_implies(ctx, implyL, implyR1);
            addAxiom(t, implyToAssert, __LINE__);
          }
          delete[] xor_items;
          delete[] and_items;
        }
      }
    }
  }
}


