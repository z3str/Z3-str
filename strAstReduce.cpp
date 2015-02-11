#include "strTheory.h"


bool defaultCharSet = true;

/*
 *
 */
std::string encodeToEscape(char c) {
  int idx = (unsigned char) c;
  if (0 <= idx && idx <= 255) {
    return escapeDict[idx];
  } else {
    printf("> Error: should not get here @ %d.\n", __LINE__);
    exit(0);
  }
}

/*
 *
 */
void setAlphabet() {
  if (defaultCharSet) {
    charSetSize = 256;
    charSet = new char[charSetSize];
    int idx = 0;
    // small letters
    for (int i = 97; i < 123; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // caps
    for (int i = 65; i < 91; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // numbers
    for (int i = 48; i < 58; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // printable marks - 1
    for (int i = 32; i < 48; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // printable marks - 2
    for (int i = 58; i < 65; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // printable marks - 3
    for (int i = 91; i < 97; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // printable marks - 4
    for (int i = 123; i < 127; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // non-printable - 1
    for (int i = 0; i < 32; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
    // non-printable - 2
    for (int i = 127; i < 256; i++) {
      charSet[idx] = (char) i;
      charSetLookupTable[charSet[idx]] = 1;
      idx++;
    }
  } else {
    const char setset[] = { 'a', 'b', 'c' };
    int fSize = sizeof(setset) / sizeof(char);

    charSet = new char[fSize];
    charSetSize = fSize;
    for (int i = 0; i < charSetSize; i++) {
      charSet[i] = setset[i];
      charSetLookupTable[setset[i]] = 1;
    }
  }
}



/****************************************
 *  Z3 input parser doesn't understand constant string
 *  So, we pass const string by adding a special mark "$",
 * --------------------------------------
 * "__cOnStStR__x23_x5c_x6e_x5c_x22_x53"
 ****************************************/
inline bool isValidHexDigit(char c) {
  if (('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')) {
    return true;
  }
  return false;
}

/*
 *
 */
inline int hexDigitToInt(char a) {
  if ('0' <= a && a <= '9')
    return a - '0';
  else if ('a' <= a && a <= 'f')
    return 10 + a - 'a';
  else if ('A' <= a && a <= 'F')
    return 10 + a - 'A';
  else
    return 0;
}

/*
 *
 */
inline int twoHexDigitToChar(char a, char b) {
  return (hexDigitToInt(a) * 16 + hexDigitToInt(b));
}

/*
 *
 */
std::string convertInputTrickyConstStr(std::string inputStr) {
  std::string outputStr = "";
  std::string innerStr = inputStr.substr(11, inputStr.length() - 11);
  int innerStrLen = innerStr.length();
  if (innerStrLen % 4 != 0) {
    fprintf(stdout, "> Error: Constant string conversion error. Exit.\n");
    fprintf(stdout, "         Input encoding: %s\n", inputStr.c_str());
    fflush(stdout);
    exit(0);
  }
  for (int i = 0; i < (innerStrLen / 4); i++) {
    std::string cc = innerStr.substr(i * 4, 4);
    if (cc[0] == '_' && cc[1] == 'x' && isValidHexDigit(cc[2]) && isValidHexDigit(cc[3])) {
      char dc = twoHexDigitToChar(cc[2], cc[3]);
      // Check whether the input character in the charSet
      if (charSetLookupTable.find(dc) == charSetLookupTable.end()) {
        fprintf(stdout, "> Error: Character '%s' in a constant string is not in the system alphabet.\n", encodeToEscape(dc).c_str());
        fprintf(stdout, "         Please set the character set accordingly.\n");
        fflush(stdout);
        exit(0);
      }
      outputStr = outputStr + std::string(1, dc);
    }
  }
  return outputStr;
}

/*
 *
 */
Z3_ast reduce_contains(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast reduceAst = NULL;
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    if (arg0Str.find(arg1Str) != std::string::npos)
      reduceAst = Z3_mk_true(ctx);
    else
      reduceAst = Z3_mk_false(ctx);
  } else {
    Z3_ast ts0 = my_mk_internal_string_var(t);
    Z3_ast ts1 = my_mk_internal_string_var(t);
    reduceAst = registerContain(t, args[0], args[1]);  // reduceAst = Contains(args[0], args[1])
    breakdownAssert = Z3_mk_eq(ctx, reduceAst, Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, args[1], ts1))));
  }
  return reduceAst;
}

/*
 *
 */
Z3_ast reduce_startswith(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast reduceAst = NULL;
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    if (arg0Str.length() < arg1Str.length()) {
      reduceAst = Z3_mk_false(ctx);
    } else {
      if (arg0Str.substr(0, arg1Str.length()) == arg1Str) {
        reduceAst = Z3_mk_true(ctx);
      } else {
        reduceAst = Z3_mk_false(ctx);
      }
    }
  } else {
    Z3_ast resBoolVar = my_mk_internal_bool_var(t);
    Z3_ast ts0 = my_mk_internal_string_var(t);
    Z3_ast ts1 = my_mk_internal_string_var(t);
    // boolVar = startswith(arg[0], arg[1])
    // --------------------------------------------
    std::vector<Z3_ast> innerItems;
    innerItems.push_back( Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, ts1)) );
    innerItems.push_back( Z3_mk_eq(ctx, mk_length(t, ts0), mk_length(t, args[1])) );
    innerItems.push_back( Z3_mk_ite(ctx, Z3_mk_eq(ctx, ts0, args[1]), Z3_mk_eq(ctx, resBoolVar, Z3_mk_true(ctx)), Z3_mk_eq(ctx, resBoolVar, Z3_mk_false(ctx) ) ) );
    Z3_ast then1 = mk_and_fromVector(t, innerItems);
    breakdownAssert = Z3_mk_ite(ctx, Z3_mk_ge(ctx, mk_length(t, args[0]), mk_length(t, args[1])), then1, Z3_mk_eq(ctx, resBoolVar, Z3_mk_false(ctx) ) );
    reduceAst = resBoolVar;
  }
  return reduceAst;
}

/*
 *
 */
Z3_ast reduce_endswith(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast reduceAst = NULL;
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    if (arg0Str.length() < arg1Str.length()) {
      reduceAst = Z3_mk_false(ctx);
    } else {
      if (arg0Str.substr(arg0Str.length() - arg1Str.length(), arg1Str.length()) == arg1Str) {
        reduceAst = Z3_mk_true(ctx);
      } else {
        reduceAst = Z3_mk_false(ctx);
      }
    }
  } else {
    Z3_ast resBoolVar = my_mk_internal_bool_var(t);
    Z3_ast ts0 = my_mk_internal_string_var(t);
    Z3_ast ts1 = my_mk_internal_string_var(t);
    // boolVar = endswith(arg[0], arg[1])
    // --------------------------------------------
    std::vector<Z3_ast> innerItems;
    innerItems.push_back( Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, ts1)) );
    innerItems.push_back( Z3_mk_eq(ctx, mk_length(t, ts1), mk_length(t, args[1])) );
    innerItems.push_back( Z3_mk_ite(ctx, Z3_mk_eq(ctx, ts1, args[1]), Z3_mk_eq(ctx, resBoolVar, Z3_mk_true(ctx)), Z3_mk_eq(ctx, resBoolVar, Z3_mk_false(ctx) ) ) );
    Z3_ast then1 = mk_and_fromVector(t, innerItems);
    breakdownAssert = Z3_mk_ite(ctx, Z3_mk_ge(ctx, mk_length(t, args[0]), mk_length(t, args[1])), then1, Z3_mk_eq(ctx, resBoolVar, Z3_mk_false(ctx) ) );
    reduceAst = resBoolVar;
  }
  return reduceAst;
}

/*
 *
 */
Z3_ast reduce_indexof(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    if (arg0Str.find(arg1Str) != std::string::npos) {
      int index = arg0Str.find(arg1Str);
      return mk_int(ctx, index);
    } else {
      return mk_int(ctx, -1);
    }
  } else {
    Z3_ast x1 = my_mk_internal_string_var(t);
    Z3_ast x2 = my_mk_internal_string_var(t);
    Z3_ast indexAst = my_mk_internal_int_var(t);

    std::vector<Z3_ast> items;

    //  args[0] = x1 . args[1] . x2
    Z3_ast eq1 = Z3_mk_eq(ctx, args[0], mk_concat(t, x1, mk_concat(t, args[1], x2)));
    // arg0HasArg1 = Contains(args[0], args[1])
    Z3_ast arg0HasArg1 = registerContain(t, args[0], args[1]);
    items.push_back(Z3_mk_eq(ctx, arg0HasArg1, eq1));

    Z3_ast condAst = arg0HasArg1;
    // -----------------------
    // true branch
    std::vector<Z3_ast> thenItems;
    thenItems.push_back(Z3_mk_ge(ctx, indexAst, mk_int(ctx, 0)));
    //  x1 doesn't contain args[1]
    thenItems.push_back(Z3_mk_not(ctx, mk_contains(t, x1, args[1])));
    thenItems.push_back(Z3_mk_eq(ctx, indexAst, mk_length(t, x1)));
    // args[0]  = x3 . x4 /\ |x3| = |x1| + |args[1]| - 1 /\ ! contains(x3, args[1])

    bool canSkip = false;
    if (getNodeType(t, args[1]) == my_Z3_ConstStr) {
      std::string arg1Str = getConstStrValue(t, args[1]);
      if (arg1Str.length() == 1) {
        canSkip = true;
      }
    }

    if (! canSkip) {
      Z3_ast x3 = my_mk_internal_string_var(t);
      Z3_ast x4 = my_mk_internal_string_var(t);
      Z3_ast tmpLenItems[3] = { indexAst, mk_length(t, args[1]), mk_int(ctx, -1) };
      Z3_ast tmpLen = Z3_mk_add(ctx, 3, tmpLenItems);
      thenItems.push_back(Z3_mk_eq(ctx, args[0], mk_concat(t, x3, x4)));
      thenItems.push_back(Z3_mk_eq(ctx, mk_length(t, x3), tmpLen));
      thenItems.push_back(Z3_mk_not(ctx, mk_contains(t, x3, args[1])));
    }
    // -----------------------
    // else branch
    std::vector<Z3_ast> elseItems;
    elseItems.push_back(Z3_mk_eq(ctx, indexAst, mk_int(ctx, -1)));

    items.push_back(Z3_mk_ite(ctx, condAst, mk_and_fromVector(t, thenItems), mk_and_fromVector(t, elseItems)));
    breakdownAssert = mk_and_fromVector(t, items);
    return indexAst;
  }
}


/*
 *
 */
Z3_ast reduce_indexof2(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr && getNodeType(t, args[2]) == my_Z3_Num) {
    std::string arg0 = getConstStrValue(t, args[0]);
    std::string arg1 = getConstStrValue(t, args[1]);
    int arg2Int = getConstIntValue(t, args[2]);
    if (arg2Int >= (int)arg0.length()) {
      return mk_int(ctx, -1);
    } else if (arg2Int < 0) {
      int index = arg0.find(arg1);
      return mk_int(ctx, index);
    } else {
      std::string suffixStr = arg0.substr(arg2Int, arg0.length() - arg2Int);
      if (suffixStr.find(arg1) != std::string::npos) {
        int index = suffixStr.find(arg1) + arg2Int;
        return mk_int(ctx, index);
      } else {
        return mk_int(ctx, -1);
      }
    }
  } else {
    // -------------------------------------------------------------------------------
    //   if (arg[2] >= length(arg[0]))                          // ite2
    //     resAst = -1
    //   else
    //     args[0] = prefix . suffix
    //     /\ indexAst = indexof(suffix, arg[1])
    //     /\ args[2] = len(prefix)
    //     /\ if (indexAst == -1)  resAst = indexAst            // ite3
    //        else   resAst = args[2] + indexAst
    // -------------------------------------------------------------------------------
    PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
    Z3_ast resAst = my_mk_internal_int_var(t);
    Z3_ast indexAst = my_mk_internal_int_var(t);
    Z3_ast prefix = my_mk_internal_string_var(t);
    Z3_ast suffix = my_mk_internal_string_var(t);
    Z3_ast prefixLen = mk_length(t, prefix);
    Z3_ast zeroAst = mk_int(ctx, 0);
    Z3_ast negOneAst = mk_int(ctx, -1);

    Z3_ast ite3 = Z3_mk_ite(ctx, Z3_mk_eq(ctx, indexAst, negOneAst),
                                 Z3_mk_eq(ctx, resAst, negOneAst),
                                 Z3_mk_eq(ctx, resAst, mk_2_add(t, args[2], indexAst))
                           );
    Z3_ast ite2ElseItems[4];
    ite2ElseItems[0] = Z3_mk_eq(ctx, args[0], mk_concat(t, prefix, suffix));
    ite2ElseItems[1] = Z3_mk_eq(ctx, indexAst, mk_2_arg_app(ctx, td->Indexof, suffix, args[1]));
    ite2ElseItems[2] = Z3_mk_eq(ctx, args[2], prefixLen);
    ite2ElseItems[3] = ite3;
    Z3_ast ite2Else = Z3_mk_and(ctx, 4, ite2ElseItems);

    Z3_ast ite2 = Z3_mk_ite(ctx, Z3_mk_ge(ctx, args[2], mk_length(t, args[0])),
                                 Z3_mk_eq(ctx, resAst, negOneAst),
                                 ite2Else
                           );

    Z3_ast ite1 = Z3_mk_ite(ctx, Z3_mk_lt(ctx, args[2], zeroAst),
                                 Z3_mk_eq(ctx, resAst, mk_2_arg_app(ctx, td->Indexof, args[0], args[1])),
                                 ite2
                            );
    breakdownAssert = ite1;
    return resAst;
  }
}

/*
 *
 */
Z3_ast reduce_lastindexof(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    if (arg0Str.rfind(arg1Str) != std::string::npos) {
      int index = arg0Str.rfind(arg1Str);
      return mk_int(ctx, index);
    } else {
      return mk_int(ctx, -1);
    }
  } else {
    Z3_ast x1 = my_mk_internal_string_var(t);
    Z3_ast x2 = my_mk_internal_string_var(t);
    Z3_ast indexAst = my_mk_internal_int_var(t);
    std::vector<Z3_ast> items;

    // args[0] = x1 . args[1] . x2
    Z3_ast eq1 = Z3_mk_eq(ctx, args[0], mk_concat(t, x1, mk_concat(t, args[1], x2)));
    Z3_ast arg0HasArg1 = registerContain(t, args[0], args[1]);  // arg0HasArg1 = Contains(args[0], args[1])
    items.push_back(Z3_mk_eq(ctx, arg0HasArg1, eq1));


    Z3_ast condAst = arg0HasArg1;
    //----------------------------
    // true branch
    std::vector<Z3_ast> thenItems;
    thenItems.push_back(Z3_mk_ge(ctx, indexAst, mk_int(ctx, 0)));
    //  args[0] = x1 . args[1] . x2
    //  x1 doesn't contain args[1]
    thenItems.push_back(Z3_mk_not(ctx, mk_contains(t, x2, args[1])));
    thenItems.push_back(Z3_mk_eq(ctx, indexAst, mk_length(t, x1)));

    bool canSkip = false;
    if (getNodeType(t, args[1]) == my_Z3_ConstStr) {
      std::string arg1Str = getConstStrValue(t, args[1]);
      if (arg1Str.length() == 1) {
        canSkip = true;
      }
    }

    if (!canSkip) {
      // args[0]  = x3 . x4 /\ |x3| = |x1| + 1 /\ ! contains(x4, args[1])
      Z3_ast x3 = my_mk_internal_string_var(t);
      Z3_ast x4 = my_mk_internal_string_var(t);
      Z3_ast tmpLenItems[2] = { indexAst, mk_int(ctx, 1) };
      Z3_ast tmpLen = Z3_mk_add(ctx, 2, tmpLenItems);
      thenItems.push_back(Z3_mk_eq(ctx, args[0], mk_concat(t, x3, x4)));
      thenItems.push_back(Z3_mk_eq(ctx, mk_length(t, x3), tmpLen));
      thenItems.push_back(Z3_mk_not(ctx, mk_contains(t, x4, args[1])));
    }
    //----------------------------
    // else branch
    std::vector<Z3_ast> elseItems;
    elseItems.push_back(Z3_mk_eq(ctx, indexAst, mk_int(ctx, -1)));

    items.push_back(Z3_mk_ite(ctx, condAst, mk_and_fromVector(t, thenItems), mk_and_fromVector(t, elseItems)));

    breakdownAssert = mk_and_fromVector(t, items);

    return indexAst;
  }
}


/*
 *
 */
Z3_ast reduce_charAt(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  __debugPrint(logFile, "%d, %d | %d", getNodeType(t, args[0]), getNodeType(t, args[1]), my_Z3_Num);
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_Num) {
    __debugPrint(logFile, "quick path\n");
    std::string arg0Str = getConstStrValue(t, args[0]);
    int arg1Int = getConstIntValue(t, args[1]);
    std::string resStr;
    if (0 <= arg1Int && arg1Int <= (int) arg0Str.length()) {
      resStr.push_back(arg0Str.c_str()[arg1Int]);
    } else {
      resStr = "";
    }
    return my_mk_str_value(t, resStr.c_str());
  } else {

    Z3_ast ts0 = my_mk_internal_string_var(t);
    Z3_ast ts1 = my_mk_internal_string_var(t);
    Z3_ast ts2 = my_mk_internal_string_var(t);

    Z3_ast cond = mk_2_and(t, Z3_mk_ge(ctx, args[1], mk_int(ctx, 0)), Z3_mk_lt(ctx, args[1], mk_length(t, args[0])));

    Z3_ast and_item[3];
    and_item[0] = Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, ts1, ts2)));
    and_item[1] = Z3_mk_eq(ctx, args[1], mk_length(t, ts0));
    and_item[2] = Z3_mk_eq(ctx, mk_length(t, ts1), mk_int(ctx, 1));
    Z3_ast thenBranch = Z3_mk_and(ctx, 3, and_item);
    Z3_ast elseBranch = Z3_mk_eq(ctx, ts1, my_mk_str_value(t, ""));
    breakdownAssert = Z3_mk_ite(ctx, cond, thenBranch, elseBranch);
    return ts1;
  }
}


/*
 *
 */
Z3_ast reduce_replace(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  if (getNodeType(t, args[0]) == my_Z3_ConstStr && getNodeType(t, args[1]) == my_Z3_ConstStr && getNodeType(t, args[2]) == my_Z3_ConstStr) {
    std::string arg0Str = getConstStrValue(t, args[0]);
    std::string arg1Str = getConstStrValue(t, args[1]);
    std::string arg2Str = getConstStrValue(t, args[2]);
    if (arg0Str.find(arg1Str) != std::string::npos) {
      int index1 = arg0Str.find(arg1Str);
      int index2 = index1 + arg1Str.length();
      std::string substr0 = arg0Str.substr(0, index1);
      std::string substr2 = arg0Str.substr(index2);
      std::string replaced = substr0 + arg2Str + substr2;
      return my_mk_str_value(t, replaced.c_str());
    } else {
      return args[0];
    }
  } else {
    Z3_ast x1 = my_mk_internal_string_var(t);
    Z3_ast x2 = my_mk_internal_string_var(t);
    Z3_ast x3 = my_mk_internal_string_var(t);
    Z3_ast result = my_mk_internal_string_var(t);

    int pos = 0;
    Z3_ast and_items[3];
    // args[0] = x1 . x2. x3
    and_items[pos++] = Z3_mk_eq(ctx, args[0], mk_concat(t, x1, mk_concat(t, x2, x3)));
    // ! contains (x1, args[1])
    and_items[pos++] = Z3_mk_not(ctx, mk_contains(t, x1, args[1]));
    // IF (x2 == args[1]) THEN result = x1 . args[2] . x3
    //                    ELSE result = x1 . x2 . x3
    and_items[pos++] = Z3_mk_ite(ctx, Z3_mk_eq(ctx, x2, args[1]),
                                      Z3_mk_eq(ctx, result, mk_concat(t, x1, mk_concat(t, args[2], x3))),
                                      Z3_mk_eq(ctx, result, mk_concat(t, x1, mk_concat(t, x2, x3))));
    breakdownAssert = Z3_mk_and(ctx, pos, and_items);
    return result;
  }
}


/*
 *
 */
Z3_ast reduce_subStr(Z3_theory t, Z3_ast const args[], Z3_ast & breakdownAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast ts0 = my_mk_internal_string_var(t);
  Z3_ast ts1 = my_mk_internal_string_var(t);
  Z3_ast ts2 = my_mk_internal_string_var(t);
  Z3_ast and_item[4];
  and_item[0] = Z3_mk_eq(ctx, args[0], mk_concat(t, ts0, mk_concat(t, ts1, ts2)));
  and_item[1] = Z3_mk_eq(ctx, args[1], mk_length(t, ts0));
  and_item[2] = Z3_mk_eq(ctx, args[2], mk_length(t, ts1));
  breakdownAssert = Z3_mk_and(ctx, 3, and_item);
  return ts1;
}


/*
 *
 */
Z3_ast reduce_str2regex(Z3_theory t, Z3_func_decl d, Z3_ast const args[], Z3_ast & extraAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  Z3_ast converted = mk_1_arg_app(ctx, d, args[0]);
  return converted;
}


/*
 *
 */
Z3_ast reduce_regexStar(Z3_theory t, Z3_ast const args[], Z3_ast & extraAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_app arg1_func_app = Z3_to_app(ctx, args[0]);
  Z3_func_decl funcDecl = Z3_get_app_decl(ctx, arg1_func_app);
  if (funcDecl == td->RegexStar)
    return args[0];
  else
    return NULL;
}


/*
 *
 */
Z3_ast reduce_regexConcat(Z3_theory t, Z3_ast const args[], Z3_ast & extraAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_app arg0_func_app = Z3_to_app(ctx, args[0]);
  Z3_app arg1_func_app = Z3_to_app(ctx, args[1]);
  Z3_func_decl arg0_funcDecl = Z3_get_app_decl(ctx, arg0_func_app);
  Z3_func_decl arg1_funcDecl = Z3_get_app_decl(ctx, arg1_func_app);
  if (arg0_funcDecl == td->Str2Reg && arg1_funcDecl == td->Str2Reg) {
    Z3_ast arg0Str  = Z3_get_app_arg(ctx, arg0_func_app, 0);
    Z3_ast arg1Str  = Z3_get_app_arg(ctx, arg1_func_app, 0);
    Z3_ast comb = mk_concat(t, arg0Str, arg1Str);
    return mk_1_arg_app(ctx, td->Str2Reg, comb);
  }
  return NULL;
}


/*
 *
 */
Z3_ast reduce_regexDigit(Z3_theory t, Z3_ast const args[], Z3_ast & extraAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  int c = 57;
  std::string cStr;
  cStr.push_back((char)c);
  Z3_ast res = mk_1_arg_app(ctx, td->Str2Reg, my_mk_str_value(t, cStr.c_str()));
  c = c - 1;
  for (; c >= 48; c--) {
    cStr.clear();
    cStr.push_back((char)c);
    res = mk_2_arg_app(ctx, td->RegexUnion, mk_1_arg_app(ctx, td->Str2Reg, my_mk_str_value(t, cStr.c_str())), res);
  }
  return res;
}




/*
 *
 */
Z3_ast reduce_regexIn(Z3_theory t, Z3_ast const args[], Z3_ast & extraAssert) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);
  Z3_app arg1_func_app = Z3_to_app(ctx, args[1]);
  Z3_func_decl funcDecl = Z3_get_app_decl(ctx, arg1_func_app);
  // quick path:
  // >> if RegexIn(T4_4, (Str2Reg #)) --> "T4_4 = #" is enough
  if (funcDecl == td->Str2Reg) {
    return Z3_mk_eq(ctx, args[0], Z3_get_app_arg(ctx, arg1_func_app, 0));
  }
  // ----------------------------------------------------
  else {
    Z3_ast rhs = NULL;
    Z3_ast resBoolVar = my_mk_internal_bool_var(t);
    std::string regexStr = getStdRegexStr(t, args[1]);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> RegexIn(");
    printZ3Node(t, args[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, args[1]);
    __debugPrint(logFile, ")\n --> \n");
    printZ3Node(t, args[0]);
    __debugPrint(logFile, "  \\in  %s\n\n", regexStr.c_str());
#endif


    std::pair<Z3_ast, std::string> key1 = std::make_pair(args[0], regexStr);
    if (regexInBoolMap.find(key1) == regexInBoolMap.end()) {
      regexInVarRegStrMap[args[0]].insert(regexStr);
      regexInBoolMap[key1] = resBoolVar;
    }

    // -------------------------------------
    // regexConcat
    if (funcDecl == td->RegexConcat) {
      Z3_ast var1 = mk_regexRepVar(t);
      Z3_ast var2 = mk_regexRepVar(t);
      rhs = mk_concat(t, var1, var2);

      Z3_ast regex1 = Z3_get_app_arg(ctx, arg1_func_app, 0);
      Z3_ast regex2 = Z3_get_app_arg(ctx, arg1_func_app, 1);
      Z3_ast var1InRegex1 = mk_2_arg_app(ctx, td->RegexIn, var1, regex1);
      Z3_ast var2InRegex2 = mk_2_arg_app(ctx, td->RegexIn, var2, regex2);
      std::vector<Z3_ast> items;
      items.push_back(var1InRegex1);
      items.push_back(var2InRegex2);
      items.push_back(Z3_mk_eq(ctx, resBoolVar, Z3_mk_eq(ctx, args[0], rhs)));
      extraAssert = mk_and_fromVector(t, items);
      return resBoolVar;
    }
    // -------------------------------------
    // regexUnion
    else if (funcDecl == td->RegexUnion) {
      Z3_ast var1 = mk_regexRepVar(t);
      Z3_ast var2 = mk_regexRepVar(t);
      Z3_ast orVar = mk_2_or(t, Z3_mk_eq(ctx, args[0], var1), Z3_mk_eq(ctx, args[0], var2));

      Z3_ast regex1 = Z3_get_app_arg(ctx, arg1_func_app, 0);
      Z3_ast regex2 = Z3_get_app_arg(ctx, arg1_func_app, 1);
      Z3_ast var1InRegex1 = mk_2_arg_app(ctx, td->RegexIn, var1, regex1);
      Z3_ast var2InRegex2 = mk_2_arg_app(ctx, td->RegexIn, var2, regex2);

      std::vector<Z3_ast> items;
      items.push_back(var1InRegex1);
      items.push_back(var2InRegex2);
      items.push_back(Z3_mk_eq(ctx, resBoolVar, orVar));
      extraAssert = mk_and_fromVector(t, items);
      return resBoolVar;
    }
    // -------------------------------------
    // regexStar
    else if (funcDecl == td->RegexStar) {
      Z3_ast regex1 = Z3_get_app_arg(ctx, arg1_func_app, 0);
      Z3_ast unrollCnt = mk_unrollBoundVar(t);
      Z3_ast unrollFunc = mk_unroll(t, regex1, unrollCnt);
      std::vector<Z3_ast> items;
      items.push_back(Z3_mk_eq(ctx, resBoolVar, Z3_mk_eq(ctx, args[0], unrollFunc)));
      items.push_back(Z3_mk_eq(ctx, Z3_mk_eq(ctx, unrollCnt, mk_int(ctx, 0)), Z3_mk_eq(ctx, unrollFunc, my_mk_str_value(t, ""))));
      extraAssert = mk_and_fromVector(t, items);
      return resBoolVar;
    }
    // -------------------------------------
    // error
    else {
      printf("> Error: Unknown Regex Operator @ %d", __LINE__);
      exit(0);
      return NULL;
    }
  }
}


/*
 *
 */
Z3_bool cb_reduce_app(Z3_theory t, Z3_func_decl d, unsigned n, Z3_ast const * args, Z3_ast * result) {
  Z3_context ctx = Z3_theory_get_context(t);
  PATheoryData * td = (PATheoryData*) Z3_theory_get_ext_data(t);

  // Convert the tricky "string" representation to string constant
  int convertedFlag = 0;
  Z3_ast * convertedArgs = new Z3_ast[n];
  for (int i = 0; i < (int) n; i++) {
    std::string symbolStr = std::string(Z3_ast_to_string(ctx, args[i]));
    if (symbolStr.length() >= 11 && symbolStr.substr(0, 11) == "__cOnStStR_") {
      convertedFlag = 1;
      convertedArgs[i] = my_mk_str_value(t, convertInputTrickyConstStr(symbolStr).c_str());
    } else {
      convertedArgs[i] = args[i];
    }
  }

  //---------------------------------
  // reduce app: Concat
  //---------------------------------
  if (d == td->Concat) {
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Concat(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")\n\n");
#endif
    *result = mk_concat(t, convertedArgs[0], convertedArgs[1]);

    delete[] convertedArgs;
    return Z3_TRUE;
  }
  //---------------------------------
  // reduce app: Length
  //---------------------------------
  if (d == td->Length) {
    if (getNodeType(t, convertedArgs[0]) == my_Z3_ConstStr) {
      int size = getConstStrValue(t, convertedArgs[0]).size();
      *result = mk_int(ctx, size);
#ifdef DEBUGLOG
      __debugPrint(logFile, "\n>> cb_reduce_app(): Length( ");
      printZ3Node(t, convertedArgs[0]);
      __debugPrint(logFile, " ) = ");
      __debugPrint(logFile, "%d\n\n", size);
#endif
      delete[] convertedArgs;
      return Z3_TRUE;
    } else {
      if (convertedFlag == 1) {
        *result = mk_1_arg_app(ctx, d, convertedArgs[0]);
        delete[] convertedArgs;
        return Z3_TRUE;
      } else {
        delete[] convertedArgs;
        return Z3_FALSE;
      }
    }
  }

  //---------------------------------
  // reduce app: SubString
  //---------------------------------
  if (d == td->SubString) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_subStr(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n");
    __debugPrint(logFile, "\n>> cb_reduce_app(): SubString( ");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[2]);
    __debugPrint(logFile, ")  =>  ");
    printZ3Node(t, *result);
    __debugPrint(logFile, "\n-- ADD(@%d, Level %d):\n", __LINE__, sLevel);
    printZ3Node(t, breakDownAst);
    __debugPrint(logFile, "\n\n");
#endif
    Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: Contains
  //------------------------------------------
  if (d == td->Contains) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_contains(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Contains(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    // when quick path is taken, breakDownAst == NULL;
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: StartsWith
  //------------------------------------------
  if (d == td->StartsWith) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_startswith(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): StartsWith(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, " )");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    __debugPrint(logFile, "\n\n");
#endif
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: EndsWith
  //------------------------------------------
  if (d == td->EndsWith) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_endswith(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): EndsWith(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: Indexof
  //------------------------------------------
  if (d == td->Indexof) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_indexof(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Indexof(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    // when quick path is taken, breakDownAst == NULL;
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: Indexof
  //------------------------------------------
  if (d == td->Indexof2) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_indexof2(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Indexof2(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[2]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    // when quick path is taken, breakDownAst == NULL;
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }


  //------------------------------------------
  // Reduce app: LastIndexof
  //------------------------------------------
  if (d == td->LastIndexof) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_lastindexof(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): LastIndexof(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    // when quick path is taken, breakDownAst == NULL;
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: CharAt
  //------------------------------------------
  if (d == td->CharAt) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_charAt(t, convertedArgs, breakDownAst);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): charAt(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif

    // when quick path is taken, breakDownAst == NULL;
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: Replace
  //------------------------------------------
  if (d == td->Replace) {
    Z3_ast breakDownAst = NULL;
    *result = reduce_replace(t, convertedArgs, breakDownAst);
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Replace(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[2]);
    __debugPrint(logFile, ")");
    __debugPrint(logFile, "  =>  ");
    printZ3Node(t, *result);
    if( breakDownAst != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, breakDownAst);
    }
    __debugPrint(logFile, "\n\n");
#endif
    if (breakDownAst != NULL)
      Z3_assert_cnstr(ctx, breakDownAst);
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: Str2Reg
  //------------------------------------------
  if (d == td->Str2Reg) {
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): Str2Reg(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ")\n");
#endif

    if (!isConstStr(t, convertedArgs[0])) {
      printf("> Error: the argument of Str2Reg function should be a constant string.\n");
      printf("         (Str2Reg %s)\n", Z3_ast_to_string(ctx, convertedArgs[0]));
      exit(0);
    }

    Z3_ast otherAssert = NULL;
    *result = reduce_str2regex(t, d, convertedArgs, otherAssert);

#ifdef DEBUGLOG
    if( otherAssert != NULL )
    {
      __debugPrint(logFile, "-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, otherAssert);
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
#endif

    if (otherAssert != NULL) {
      Z3_assert_cnstr(ctx, otherAssert);
    }
    delete[] convertedArgs;
    return Z3_TRUE;
  }

  //------------------------------------------
  // Reduce app: RegexConcat
  //------------------------------------------
  if (d == td->RegexConcat) {
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): RegexConcat(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ")\n");
#endif

    Z3_ast otherAssert = NULL;
    Z3_ast tmpRes = reduce_regexConcat(t, convertedArgs, otherAssert);
    delete[] convertedArgs;

#ifdef DEBUGLOG
    if (tmpRes != NULL) {
      __debugPrint(logFile, "   --------------> ");
      printZ3Node(t, tmpRes);
      __debugPrint(logFile, "\n");
    }
    __debugPrint(logFile, "\n");
#endif

    if (tmpRes == NULL) {
      return Z3_FALSE;
    } else {
      *result = tmpRes;
      return Z3_TRUE;
    }
  }

  //------------------------------------------
  // Reduce app: RegexIn
  //------------------------------------------
  if (d == td->RegexIn) {
    Z3_ast otherAssert = NULL;
    Z3_ast tmpRes = NULL;
    tmpRes = reduce_regexIn(t, convertedArgs, otherAssert);

#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): RegexIn(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ", ");
    printZ3Node(t, convertedArgs[1]);
    __debugPrint(logFile, ") ==> ");
    printZ3Node(t, tmpRes);
    __debugPrint(logFile, "\n");
    if( otherAssert != NULL )
    {
      __debugPrint(logFile, "-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, otherAssert);
    }
    __debugPrint(logFile, "\n\n");
#endif

    delete[] convertedArgs;

    if (tmpRes != NULL) {
      if (otherAssert != NULL) {
        Z3_assert_cnstr(ctx, otherAssert);
      }
      *result = tmpRes;
      return Z3_TRUE;
    }
    return Z3_FALSE;
  }
  //------------------------------------------
  // Reduce app: RegexStar
  //------------------------------------------
  if (d == td->RegexStar) {
    Z3_ast otherAssert = NULL;
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): RegexStar(");
    printZ3Node(t, convertedArgs[0]);
    __debugPrint(logFile, ") --> ");
#endif
    *result = reduce_regexStar(t, convertedArgs, otherAssert);
    delete[] convertedArgs;

#ifdef DEBUGLOG
    printZ3Node(t, *result);
    if( otherAssert != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, otherAssert);
    }
    __debugPrint(logFile, "\n\n");
#endif

    if (*result != NULL) {
      if (otherAssert != NULL) {
        Z3_assert_cnstr(ctx, otherAssert);
      }
      return Z3_TRUE;
    }
    return Z3_FALSE;
  }

  if (d == td->RegexDigit) {
    Z3_ast otherAssert = NULL;
#ifdef DEBUGLOG
    __debugPrint(logFile, "\n>> cb_reduce_app(): RegexDigit\n");
#endif

    *result = reduce_regexDigit(t, convertedArgs, otherAssert);
    delete[] convertedArgs;

#ifdef DEBUGLOG
    printZ3Node(t, *result);
    if( otherAssert != NULL )
    {
      __debugPrint(logFile, "\n-- ADD(@%d): \n", __LINE__);
      printZ3Node(t, otherAssert);
    }
    __debugPrint(logFile, "\n\n");
#endif
    if (*result != NULL) {
      if (otherAssert != NULL) {
        Z3_assert_cnstr(ctx, otherAssert);
      }
      return Z3_TRUE;
    }
    return Z3_FALSE;
  }


  delete[] convertedArgs;
  return Z3_FALSE; // failed to simplify
}


/*
 *
 */
Z3_bool cb_reduce_eq(Z3_theory t, Z3_ast s1, Z3_ast s2, Z3_ast * r) {
  Z3_context ctx = Z3_theory_get_context(t);
  std::string s1_str = std::string(Z3_ast_to_string(ctx, s1));
  std::string s2_str = std::string(Z3_ast_to_string(ctx, s2));
  Z3_ast s1_new = s1;
  Z3_ast s2_new = s2;

  // Convert the tricky "string" representation to string constant
  if (s1_str.length() >= 11 && s1_str.substr(0, 11) == "__cOnStStR_")
    s1_new = my_mk_str_value(t, convertInputTrickyConstStr(s1_str).c_str());
  if (s2_str.length() >= 11 && s2_str.substr(0, 11) == "__cOnStStR_")
    s2_new = my_mk_str_value(t, convertInputTrickyConstStr(s2_str).c_str());

  if (s2_new != s2 || s1_new != s1) {
    *r = Z3_mk_eq(ctx, s1_new, s2_new);

    __debugPrint(logFile, "\n>> cb_reduce_eq: ");
    printZ3Node(t, *r);
    __debugPrint(logFile, "\n\n");

    return Z3_TRUE;
  } else {
    return Z3_FALSE;
  }
}
