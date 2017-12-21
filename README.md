
#### Z3-str2 is not actively maintained anymore. 

#### Please see [https://sites.google.com/site/z3strsolver/](https://sites.google.com/site/z3strsolver/) for z3str3 and latest versions.

___

Z3-str2 is a string theory plug-in built on the powerful Z3 SMT solver.

Z3-str2 treats strings as a primitive type, thus avoiding the inherent limitations 
observed in many existing solvers that encode strings in terms of other primitives.


# Documentations:

Please refer to [https://sites.google.com/site/z3strsolver/](https://sites.google.com/site/z3strsolver/)



# Installation

## Linux

1. Check out the latest version of Z3-str2 from the git repo.


2. Download [the source code of Z3 4.1.1](http://z3.codeplex.com/releases/view/95640)
   
  MD5 SUM: ```c0c2367e4de05614a80b3f62480c23db  z3-src-4.1.1.zip```


3. Unzip "z3-src-4.1.1.zip" and patch the original Z3. Z3-str2 will work with the modified Z3 core. Suppose the folder name after unzipping is "z3".
     *  $ cp z3.patch z3/
     *  $ cd z3
     *  $ patch -p0 < z3.patch
   

4. In the top level folder of Z3 Build the modifed version of Z3
   * $ autoconf
   * $ ./configure
   * $ make
   * $ make a
   
   
5. Build  Z3-str2
   * Modify variable "Z3_path" in the Z3-str2 Makefile to indicate the patched Z3 location.

      $ make

       
6. Setup Z3-str2 driver script
   * In "Z3-str2.py", change the value of the variable "solver" to point to the 
     Z3-str2 binary "str" just built
 
 
7. Run Z3-str2
   *  ```Z3-str2.py -f <inputFile>```, e.g 

      $./Z3-str2.py -f tests/concat-002


## Mac OS
0. Install "autoconf", "dos2unix", "gcc"
   * $ brew install autoconf
   * $ brew install dos2unix
   * $ brew install gcc --without-multilib
 
1. Check out the latest version of Z3-str2 from the git repo.


2. Download [the source code of Z3 4.1.1](http://z3.codeplex.com/releases/view/95640)
   
  MD5 SUM: ```c0c2367e4de05614a80b3f62480c23db  z3-src-4.1.1.zip```


3. Unzip "z3-src-4.1.1.zip" and patch the original Z3. Z3-str2 will work with the modified Z3 core. Suppose the folder name after unzipping is "z3".
     *  $ cp z3.patch z3/
     *  $ cd z3
     *  $ patch -p0 < z3.patch
   

4. In the top level folder of Z3 Build the modifed version of Z3
   * $ autoconf
   * $ CXX=g++-5 CC=gcc-5 ./configure
   * $ CXX=g++-5 CC=gcc-5 make
   * $ make a
   
   
5. Build  Z3-str2
   * Modify variable "Z3_path" in the Z3-str2 Makefile to indicate the patched Z3 location.

      $ make

       
6. Setup Z3-str2 driver script
   * In "Z3-str2.py", change the value of the variable "solver" to point to the 
     Z3-str2 binary "str" just built
 
 
7. Run Z3-str2
   *  ```Z3-str2.py -f <inputFile>```, e.g 

      $./Z3-str2.py -f tests/concat-002



## Cygwin
Assume we are using cygwin version 2.873 (64 bit)

0. Install cygwin with the following additional packages
   * "autoconf 2.5" in "Devel"
   * "dos2unix" in "Untils"
   * "gcc-g++: GNU Compiler Collectoin" in "Devel" 
   * "make: The GNU version of the 'make' utility"
   * "patch" in "Devel"
   * "python: Python language interpreter" in "Python"


1. Build Z3 without patching
   * Download z3 4.1.1   
     http://z3.codeplex.com/downloads/get/500120

    * Untar  
      suppose the z3 src folder is "/home/hi/z3/z3"
 
    * Patch        
        $ patch -p0 < z3.patch  
        patching file lib/api_user_theory.cpp  
        patching file lib/buffer.h  
        patching file lib/debug.h  
        patching file lib/ref_vector.h  
        patching file lib/smt_enode.h  
        patching file lib/theory_arith_core.h  
        patching file lib/theory_arith.h  
        patching file lib/user_smt_theory.cpp  
        patching file lib/user_smt_theory.h  
        patching file lib/z3_api.h  

    *  autoconf          
        $ autoconf-2.69

        
    * configure  
        $ ./configure  
        checking for dos2unix... /usr/bin/dos2unix  
        checking for g++... g++  
        checking whether the C++ compiler works... yes  
        checking for C++ compiler default output file name... a.exe  
        checking for suffix of executables... .exe  
        checking whether we are cross compiling... no  
        checking for suffix of object files... o  
        checking whether we are using the GNU C++ compiler... yes  
        checking whether g++ accepts -g... yes  
        checking whether make sets $(MAKE)... no  
        <b>configure: error: Unknown host platform: CYGWIN_NT-6.1</b>

    
    * modify configure  
        host_os=`uname -s`  
        host_os="Linux"

      
    * make          
        It's fine to have warnings like "warning: -fPIC ignored for target (all code is position independent)"  

      
    * make a
    
    
2. Build Z3-str
    * Specify Z3 path in Makefile, e.g  
        Z3_path = /home/hi/z3/z3

    
    * make
      
    * Specify z3str binary in wrapper "Z3-str.py", e.g  
        solver = "/home/hi/z3/str/str.exe"

      
    * test  
        hi@hi-vm ~/z3/str      
        $ ./Z3-str.py -f tests/concat-001  
        \* v-ok  
        \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*  
        \>\> SAT  
        \-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-\-  
        y1 : string -> "aaaaaaao"  
        y2 : string -> "y"  
        x : string -> "teaaaaaaaosty"  
        \*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*\*  
        \>\> etime(s) = 0.100061
