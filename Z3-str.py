#!/usr/bin/env python

from __future__ import division
import sys
import getopt
import time
import os
import subprocess
import signal
from subprocess import Popen, PIPE


# "solver" should point to the binary built. 
# e.g. "/home/z3-str/str" or "/home/work/tool/z3/myStrTheory/str"
solver = ""
# Before sovling the constraints, Z3-str has to properly encodes inputs as intermediated 
# format. (E.g. "\n" and "\t" should be encoded). Variable "tmpEncodingDir" where the intermediated
# inputs are saved
tmpEncodingDir = "/tmp/z3_str_convert"
clearTempFile = 1
checkAnswer = 1
tmpStrVarCnt = 0
#=================================================================== 

encodeDict = {
  '\x00' : '_x00',  '\x01' : '_x01',  '\x02' : '_x02',  '\x03' : '_x03',  
  '\x04' : '_x04',  '\x05' : '_x05',  '\x06' : '_x06',  '\x07' : '_x07',  
  '\x08' : '_x08',  '\x09' : '_x09',  '\x0a' : '_x0a',  '\x0b' : '_x0b',  
  '\x0c' : '_x0c',  '\x0d' : '_x0d',  '\x0e' : '_x0e',  '\x0f' : '_x0f',  
  '\x10' : '_x10',  '\x11' : '_x11',  '\x12' : '_x12',  '\x13' : '_x13',  
  '\x14' : '_x14',  '\x15' : '_x15',  '\x16' : '_x16',  '\x17' : '_x17',  
  '\x18' : '_x18',  '\x19' : '_x19',  '\x1a' : '_x1a',  '\x1b' : '_x1b',  
  '\x1c' : '_x1c',  '\x1d' : '_x1d',  '\x1e' : '_x1e',  '\x1f' : '_x1f',  
  '\x20' : '_x20',  '\x21' : '_x21',  '\x22' : '_x22',  '\x23' : '_x23',  
  '\x24' : '_x24',  '\x25' : '_x25',  '\x26' : '_x26',  '\x27' : '_x27',  
  '\x28' : '_x28',  '\x29' : '_x29',  '\x2a' : '_x2a',  '\x2b' : '_x2b',  
  '\x2c' : '_x2c',  '\x2d' : '_x2d',  '\x2e' : '_x2e',  '\x2f' : '_x2f',  
  '\x30' : '_x30',  '\x31' : '_x31',  '\x32' : '_x32',  '\x33' : '_x33',  
  '\x34' : '_x34',  '\x35' : '_x35',  '\x36' : '_x36',  '\x37' : '_x37',  
  '\x38' : '_x38',  '\x39' : '_x39',  '\x3a' : '_x3a',  '\x3b' : '_x3b',  
  '\x3c' : '_x3c',  '\x3d' : '_x3d',  '\x3e' : '_x3e',  '\x3f' : '_x3f',  
  '\x40' : '_x40',  '\x41' : '_x41',  '\x42' : '_x42',  '\x43' : '_x43',  
  '\x44' : '_x44',  '\x45' : '_x45',  '\x46' : '_x46',  '\x47' : '_x47',  
  '\x48' : '_x48',  '\x49' : '_x49',  '\x4a' : '_x4a',  '\x4b' : '_x4b',  
  '\x4c' : '_x4c',  '\x4d' : '_x4d',  '\x4e' : '_x4e',  '\x4f' : '_x4f',  
  '\x50' : '_x50',  '\x51' : '_x51',  '\x52' : '_x52',  '\x53' : '_x53',  
  '\x54' : '_x54',  '\x55' : '_x55',  '\x56' : '_x56',  '\x57' : '_x57',  
  '\x58' : '_x58',  '\x59' : '_x59',  '\x5a' : '_x5a',  '\x5b' : '_x5b',  
  '\x5c' : '_x5c',  '\x5d' : '_x5d',  '\x5e' : '_x5e',  '\x5f' : '_x5f',  
  '\x60' : '_x60',  '\x61' : '_x61',  '\x62' : '_x62',  '\x63' : '_x63',  
  '\x64' : '_x64',  '\x65' : '_x65',  '\x66' : '_x66',  '\x67' : '_x67',  
  '\x68' : '_x68',  '\x69' : '_x69',  '\x6a' : '_x6a',  '\x6b' : '_x6b',  
  '\x6c' : '_x6c',  '\x6d' : '_x6d',  '\x6e' : '_x6e',  '\x6f' : '_x6f',  
  '\x70' : '_x70',  '\x71' : '_x71',  '\x72' : '_x72',  '\x73' : '_x73',  
  '\x74' : '_x74',  '\x75' : '_x75',  '\x76' : '_x76',  '\x77' : '_x77',  
  '\x78' : '_x78',  '\x79' : '_x79',  '\x7a' : '_x7a',  '\x7b' : '_x7b',  
  '\x7c' : '_x7c',  '\x7d' : '_x7d',  '\x7e' : '_x7e',  '\x7f' : '_x7f',  
  '\x80' : '_x80',  '\x81' : '_x81',  '\x82' : '_x82',  '\x83' : '_x83',  
  '\x84' : '_x84',  '\x85' : '_x85',  '\x86' : '_x86',  '\x87' : '_x87',  
  '\x88' : '_x88',  '\x89' : '_x89',  '\x8a' : '_x8a',  '\x8b' : '_x8b',  
  '\x8c' : '_x8c',  '\x8d' : '_x8d',  '\x8e' : '_x8e',  '\x8f' : '_x8f',  
  '\x90' : '_x90',  '\x91' : '_x91',  '\x92' : '_x92',  '\x93' : '_x93',  
  '\x94' : '_x94',  '\x95' : '_x95',  '\x96' : '_x96',  '\x97' : '_x97',  
  '\x98' : '_x98',  '\x99' : '_x99',  '\x9a' : '_x9a',  '\x9b' : '_x9b',  
  '\x9c' : '_x9c',  '\x9d' : '_x9d',  '\x9e' : '_x9e',  '\x9f' : '_x9f',  
  '\xa0' : '_xa0',  '\xa1' : '_xa1',  '\xa2' : '_xa2',  '\xa3' : '_xa3',  
  '\xa4' : '_xa4',  '\xa5' : '_xa5',  '\xa6' : '_xa6',  '\xa7' : '_xa7',  
  '\xa8' : '_xa8',  '\xa9' : '_xa9',  '\xaa' : '_xaa',  '\xab' : '_xab',  
  '\xac' : '_xac',  '\xad' : '_xad',  '\xae' : '_xae',  '\xaf' : '_xaf',  
  '\xb0' : '_xb0',  '\xb1' : '_xb1',  '\xb2' : '_xb2',  '\xb3' : '_xb3',  
  '\xb4' : '_xb4',  '\xb5' : '_xb5',  '\xb6' : '_xb6',  '\xb7' : '_xb7',  
  '\xb8' : '_xb8',  '\xb9' : '_xb9',  '\xba' : '_xba',  '\xbb' : '_xbb',  
  '\xbc' : '_xbc',  '\xbd' : '_xbd',  '\xbe' : '_xbe',  '\xbf' : '_xbf',  
  '\xc0' : '_xc0',  '\xc1' : '_xc1',  '\xc2' : '_xc2',  '\xc3' : '_xc3',  
  '\xc4' : '_xc4',  '\xc5' : '_xc5',  '\xc6' : '_xc6',  '\xc7' : '_xc7',  
  '\xc8' : '_xc8',  '\xc9' : '_xc9',  '\xca' : '_xca',  '\xcb' : '_xcb',  
  '\xcc' : '_xcc',  '\xcd' : '_xcd',  '\xce' : '_xce',  '\xcf' : '_xcf',  
  '\xd0' : '_xd0',  '\xd1' : '_xd1',  '\xd2' : '_xd2',  '\xd3' : '_xd3',  
  '\xd4' : '_xd4',  '\xd5' : '_xd5',  '\xd6' : '_xd6',  '\xd7' : '_xd7',  
  '\xd8' : '_xd8',  '\xd9' : '_xd9',  '\xda' : '_xda',  '\xdb' : '_xdb',  
  '\xdc' : '_xdc',  '\xdd' : '_xdd',  '\xde' : '_xde',  '\xdf' : '_xdf',  
  '\xe0' : '_xe0',  '\xe1' : '_xe1',  '\xe2' : '_xe2',  '\xe3' : '_xe3',  
  '\xe4' : '_xe4',  '\xe5' : '_xe5',  '\xe6' : '_xe6',  '\xe7' : '_xe7',  
  '\xe8' : '_xe8',  '\xe9' : '_xe9',  '\xea' : '_xea',  '\xeb' : '_xeb',  
  '\xec' : '_xec',  '\xed' : '_xed',  '\xee' : '_xee',  '\xef' : '_xef',  
  '\xf0' : '_xf0',  '\xf1' : '_xf1',  '\xf2' : '_xf2',  '\xf3' : '_xf3',  
  '\xf4' : '_xf4',  '\xf5' : '_xf5',  '\xf6' : '_xf6',  '\xf7' : '_xf7',  
  '\xf8' : '_xf8',  '\xf9' : '_xf9',  '\xfa' : '_xfa',  '\xfb' : '_xfb',  
  '\xfc' : '_xfc',  '\xfd' : '_xfd',  '\xfe' : '_xfe',  '\xff' : '_xff', 
}
  

varTypeDict = {}
varSolution = {}
fileContent = ""
pool = []

def encodeConstStr(constStr):
  try:
    constStr = constStr.decode('string_escape')      
  except ValueError, e:
    print "Error: %s in \"%s\"" % (e, constStr)
    print "Exit..."
    sys.exit(1) 
  
  p = 0
  result = ""
  while p < len(constStr):
    cc = encodeDict[ constStr[p] ]
    result = result + cc
    p += 1
  result = "__cOnStStR_" + result
  return result


def collectType(tt):
  global varTypeDict
  tt = ' '.join(tt.split())
  varName = tt[0:tt.find(' ')].strip()
  varType = tt[tt.find(' ') + 1: ].strip()
  varTypeDict[varName] = varType  
  
  

def convert(org_file, convertedOriginalFile):  
  global varTypeDict
  global fileContent

  declared_string_var = []
  declared_string_const = []
  converted_cstr = ""  
  
  f_o = open(org_file, 'r')    
  fileContent = f_o.read()  
  f_o.close()
  
  linesInFile = fileContent.split("\n")  
  
  regexStarCount = 0
  
  for line in linesInFile:    
    line = line.strip();
    line = line.replace('\t', ' ')
    if line == "":
      continue
    elif line.startswith(';'):
      continue
    elif line.startswith('%'):
      continue
    elif line.startswith('//'):
      continue
    elif line.find("get-model") != -1:
      continue
    elif line.find("set-option") != -1:
      continue
    elif line.find("declare-variable") != -1:    
      declared_string_var.append(line.replace('declare-variable', 'declare-const'))
      # collect types of variables
      tt = line[1:-1].lstrip()
      tt = tt[tt.find("declare-variable") + 16:].strip()      
      collectType(tt)
      continue
    
    elif line.find("declare-const") != -1:
      # collect types of variables
      tt = line[1:-1].lstrip()
      tt = tt[tt.find("declare-const") + 13:].strip()
      collectType(tt)
      
    
    elif line.find("declare-fun") != -1 :
      # collect types of variables
      tt = line[1:-1].lstrip()
      tt = tt[tt.find("declare-fun") + 11:].strip()
      tt = tt[:tt.find('(')] + tt[tt.find(')') + 1:]
      collectType(tt)
      
    
    # ------------------------------------
    # start: processing const string
    p1 = -1
    while True:
      p1 = line.find('\"', p1 + 1);
      if p1 == -1:
        break;
      
      # exclude the case "...\"..."
      p2 = p1 + 1
      while p2 < len(line):
        if line[p2] == "\\":
          if p2 + 1 < len(line) and (line[p2 + 1] == "\"" or line[p2 + 1] == "\\"):
            p2 = p2 + 2
            continue
        elif line[p2] == "\"":
          break
        p2 = p2 + 1
   
      if p2  >= len(line):
        print('input format error!\n')
        print line
        return "eRrOr"     
      
      old_s = line[p1: p2 + 1]
      encoded_s = encodeConstStr( old_s[1 : len(old_s) - 1] )      
      line = line.replace(old_s, encoded_s)
      
      if encoded_s not in declared_string_const:
        declared_string_const.append(encoded_s)
      p1 = p2
      
    # -----------------------------
    # end: processing const string
    converted_cstr = converted_cstr + line + '\n'
  
  
  output_str = ""
  for strv in declared_string_var:
    output_str = output_str + strv + "\n"  
  output_str = output_str + '\n'
  for str_const in declared_string_const:
    output_str = output_str + '(declare-const ' + str_const + ' String)\n'    
  output_str = output_str + '\n'
  output_str = output_str + converted_cstr
  # -------------------------------------
  f_n = open(convertedOriginalFile, 'w')
  f_n.write(output_str)        
  f_n.close()  
  

def processOutput(output):
  global varSolution
  
  if output.find("(error ") != -1:
    res = ""
    ll = output.split("\n")
    for line in ll:
      if line.strip().startswith("(error "):
        res = res + line + "\n"
    return res, 1
  elif output.find("> Error:") != -1:
    return output, 1

  lines = output.split("\n")
  result = []

  for line in lines:
    if line.strip() == "":
      continue
    elif line.startswith('$$'):
      continue
    elif line.startswith('unique-value!'):
      continue    
    elif line.startswith('**************') or line.startswith('>> ') or line.startswith('--------------'):
      result.append(line)
      result.append("\n")
      continue    
    elif line.find(" -> ") != -1:   
      result.append(line)
      result.append("\n")
      
      fields = line.split(" -> ")
      varSec = fields[0].split(":")
      varName = varSec[0].strip()
      varType = varSec[1].strip()
      value = fields[1].strip()
      varSolution[varName] = value
  return ''.join(result), 0


def isInt(s):
    try: 
        int(s)
        return True
    except ValueError:
        return False


def genSimpValue(vType, vValue):
  if vType.lower() == "string":
    return vValue    
  elif vType.lower() == "bool":
    if vValue == "true":
      return "true"
    else:
      return "false"
  elif vType.lower() == "int":
    intv = int(vValue)
    if intv < 0:
      return "(- 0 %d" % (-intv) + ")"
    else:
      return "%d" % intv
  elif vType == "real":
    realv = float(eval(vValue))
    res = ""
    if realv < 0.0:
      res = "(- 0.0 %g" % (-realv) + ")"
    else:
      res = "%g" % realv
    if isInt(res):
      res = res + ".0"
    return res
  else:
    return vValue



def isArrayType(typeStr):
  if typeStr.find("(array ") != -1:
    return True
  if typeStr.find(" array ") != -1:
    return True
  return False



def topLevelSplit(strVal, c):
  strVal = strVal.strip() 
  res = []
  parenthesis = []
  openQuote = False
  idx = 0
  while idx < len(strVal):
    if (strVal[idx] == c) and (len(parenthesis) == 0) and (not openQuote):
      res.append(strVal[:idx].strip())
      strVal = strVal[idx + 1 : ].strip()
      idx = 0  # start over. Should skip idx++
      continue 
    elif strVal[idx] == "\"":
      if idx == 0:
        openQuote = not openQuote
      else:
        if strVal[idx - 1] != "\\":
          openQuote = not openQuote
    elif (not openQuote) and (strVal[idx] == "(") or (strVal[idx] == "["):
      parenthesis.append(strVal[idx])
    elif (not openQuote) and (strVal[idx] == ")"):
      if parenthesis[len(parenthesis) - 1] == "(":
        parenthesis.pop()
    elif (not openQuote) and (strVal[idx] == "]"):
      if parenthesis[len(parenthesis) - 1] == "[":
        parenthesis.pop()
      
    idx = idx + 1
    
  res.append(strVal)
  return res
  


def getArrayType(vType):
  if not (vType[0] == "(" and vType[len(vType) - 1] == ")"):
    print "Array Type Error in Solution Parsing - 0: " + vType
    sys.exit()
    
  vType = vType[1 : -1].strip()  
  if not vType.startswith("array"):
    print "Array Type Error in Solution Parsing - 1: " + vType
    sys.exit()

  newAsserts = []
  res = topLevelSplit(vType[5:], " ")  
  if len(res) != 2:
    print "Array Type Error in Solution Parsing - 2: " + vType
    sys.exit()
  return (res[0], res[1])



def flatIdxValValues(assign, vList, resList):
  if not (assign.startswith("[") and assign.endswith("]")):
    print "Array value error in solution parsing - 0: " + assign
    sys.exit()

  vaList = topLevelSplit(assign[1 : -1], ",") 

  for kv in vaList:
    res = topLevelSplit(kv, ":")
    tmpList = vList[:] # make a copy
    tmpList.append(res[0])
    # value is an array, dig further
    if res[1].startswith("["):
      flatIdxValValues(res[1], tmpList, resList)
    else:
      tmpList.append(res[1])
      resList.append(tmpList)



def flatIdxValTypes(vType):
  idxKeyTypeList = []
  (idxType, valType) = getArrayType(vType)
  
  if isArrayType(idxType):
    print "Array typed index is not supported yet. Exit"
    sys.exit()
  
  idxKeyTypeList.append(idxType)
  while isArrayType(valType):
    (idxType, valType) = getArrayType(valType)
    idxKeyTypeList.append(idxType)    
  idxKeyTypeList.append(valType)
  
  return idxKeyTypeList


  
def genArrayVal(vType, aName, aValue):
  global tmpStrVarCnt
  newAsserts = []
  
  idxKeyTypeList = flatIdxValTypes(vType)
  idxValValueList = []
  flatIdxValValues(aValue, [], idxValValueList)
  
  for vv in idxValValueList:
    if len(idxKeyTypeList) != len(vv):
      print "Error: array idxVal inconsistent."
      print "       flatIdxValType  = " + str(idxKeyTypeList)
      print "       flatIdxValValue = " + str(vv) + "]\n"
      sys.exit()
    cnt = len(idxKeyTypeList) - 1
    select = aName
    for i in range(cnt):
      t = idxKeyTypeList[i]
      v = vv[i]
      if t == "string":
        tmpVar = "SeLeCt_IdX_StR_%d" % tmpStrVarCnt
        tmpStrVarCnt = tmpStrVarCnt + 1
        newAsserts.append("(declare-fun " + tmpVar + " () String)\n" + "(assert (= " + tmpVar + " " + v + ") )\n")
        select = "(select " + select + " " + tmpVar + ")"
      else:
        select = "(select " + select + " " + genSimpValue(t, v) + ")"
    res = "(assert (= " + select + " " + genSimpValue(idxKeyTypeList[cnt], vv[cnt]) + ") )\n"
    newAsserts.append(res)
  return newAsserts



def genSolAsserts():
  global varTypeDict
  global varSolution
  result = []
  newSortValueDeclare = {}
  for name, value in varSolution.items():
    varType = varTypeDict[name]
    if isArrayType(varType):
      assertsList = genArrayVal(varType, name, value)
      for asst in assertsList:
        result.append(asst)
    else:      
      if not varType.lower() in {"int": 0, "real": 0, "string": 0, "bool": 0}.keys():
        newSortValueDeclare[value] = varType      
      result.append("( assert (= " + name + " " + genSimpValue(varType, value) + ") )\n")
  extraDeclare = ""
  for name in newSortValueDeclare.keys():
    extraDeclare += '( declare-const  ' + name + '  ' + newSortValueDeclare[name] + ' )\n' 
  res = ''.join(result)
  return extraDeclare + '\n' + res
  
  


def printUseage():
  print 'USAGE: '
  print '  Z3-str.py -f <inputfile>\n'  
  print '\n'
  
      

if __name__ == '__main__':
  argv = sys.argv[1:]
  inputFile = '';  
  allowLoopCut = 0
  modifyFreeLen = 0
  freeVarMaxLen = 0
  global child_pid
  
  try:
    opts, args = getopt.getopt(argv,"hf:")
  except getopt.GetoptError:
    printUseage()
    sys.exit()
  for opt, arg in opts:
    if opt == '-h':      
      printUseage()
      sys.exit()
    elif opt in ("-f"):
      inputFile = arg
    
      
  if inputFile == '':
    printUseage()
    sys.exit()
  
  if not os.path.exists(inputFile):
    print "Error: Input file does not exist: \"" + inputFile + "\""    
    exit(0)
  
  convertDir = tmpEncodingDir;
  if not os.path.exists(convertDir):
    os.makedirs(convertDir)
  
  fileName = os.path.basename(inputFile);    
  convertedOriginalFile = os.path.join(convertDir, fileName)   
  
  rr = convert(inputFile, convertedOriginalFile)
  if rr == "eRrOr":
    exit(0)
    
  try:
    start = time.time() 
    paras = [solver, "-f", convertedOriginalFile]
     
    # --------------------------------------------------  
    # Solve the origial constraints.
    #   > SAT, verify the ansert
    #   > UNSAT/UNKNOWN, report
    # --------------------------------------------------
    
    start_time = time.time()
    
    proc = subprocess.Popen(paras, stdout=PIPE, stderr=PIPE)
    child_pid = proc.pid
    (output, error) = proc.communicate()
    
    wallT1 = time.time() - start_time
    
    if error != "":
      print error
      print "Exit..."
      sys.exit(0)
    
    outStr, hasError = processOutput(output)
    
    if hasError == 1:      
      sys.stdout.write(outStr)
      print "> Exit"
      sys.exit(0)
    
    
    if checkAnswer != 1:
      print outStr
      sys.exit(0)
    
    # Remove the temp file of the encoding of the original input
    if clearTempFile == 1:
      if os.path.exists(convertedOriginalFile):
        os.remove(convertedOriginalFile)
    
    # --------------------------------------------------
    # Result parsing
    #  - If SAT, assert the solutions as additional constraints to verify the answer
    #    ** Verificaiton OK:   print "* v-ok"
    #    ** Verification FAIL: print "* v-fail" together with "UNKNOWN"
    #  - If UNSAT/UNKNOWN
    # --------------------------------------------------
    if outStr.find("String!val!") != -1:
      print "* v-fail"
      print "************************"
      print ">> UNKNOWN  (1)"
      print "************************" 
      sys.stdout.write(">> etime(s) = %f\n\n" % wallT1)  
    elif outStr.find(">> SAT") != -1: 
      if outStr.find("(error ") != -1:
        outStr = outStr.replace(">> SAT", "").replace("************************\n", "").replace("------------------------\n", "").replace("\n\n", "\n")
        print "Error:\n------------------------\n" + outStr + "\n"
      else:
        ii = fileContent.find("(check-sat)")    
        solutionAssert = genSolAsserts()
        newInputStr = fileContent[ :ii - 1] + "\n\n\n" + solutionAssert + "\n\n" + fileContent[ii:]
        verifyInputFilename = tmpEncodingDir + "/verify_" + fileName
        convertedVerifyInputFilename = tmpEncodingDir + "/verify_conv_" + fileName 
        f_n = open(verifyInputFilename, 'w')
        f_n.write(newInputStr)        
        f_n.close()
        
        convert(verifyInputFilename, convertedVerifyInputFilename)
        paras = [solver, "-f", convertedVerifyInputFilename]
        
        # run the solver again, check the solution.
        start_time2 = time.time()
        err1 = subprocess.check_output(paras, );
        wallT2 = time.time() - start_time2
        if err1.find(">> SAT") != -1:
          if err1.find("(error ") != -1:
            err1 = err1.replace(">> SAT", "").replace("************************\n", "").replace("------------------------\n", "").replace("\n\n", "\n")
            print "ERROR: Solution Verification Syntax\n------------------------\n" + err1 + "\n"
          else:
            print "* v-ok" 
            sys.stdout.write(outStr + ">> etime(s) = %f\n\n" % (wallT1 + wallT2))  
        else:
          print "* v-fail"
          print "************************"
          print ">> UNKNOWN (2)"
          print "************************"
          print ">> etime(s) = %f" % (wallT1 + wallT2)
        if clearTempFile == 1:
          if os.path.exists(verifyInputFilename):
            os.remove(verifyInputFilename)
          if os.path.exists(convertedVerifyInputFilename):
            os.remove(convertedVerifyInputFilename)
    else:      
      sys.stdout.write(outStr + ">> etime(s) = %f\n\n" % wallT1)  
      
  except KeyboardInterrupt:
    os.kill(child_pid, signal.SIGTERM)
    #print "Interrupted by keyborad"
    
    
  
