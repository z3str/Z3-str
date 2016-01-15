default: all

# -------------------------------------------------------------------
# Change the path to the patched Z3 4.1.1 accordingly
# The directory indicated by this path should contain "lib" and "bin"
# e.g. "/home/z3_src_4.1.1"
# -------------------------------------------------------------------
Z3_path = 

JUNK = str
SOURCE = *.cpp
INCLUDE = $(Z3_path)/lib
LIB = $(Z3_path)/bin/external

ifeq ($(shell uname -s), Darwin)
	CXX = g++-5
        FLAG = -O3 -std=c++11 -fopenmp
        LDFLAG = -lz3 -Wall
else
	CXX = g++
        FLAG = -O3 -std=c++11 -fopenmp -static
        LDFLAG = -lz3 -lrt -Wall -ldl
endif

all: $(SOURCE)
	@echo ">> Z3 Source Dir: "$(Z3_path)
	@echo ""
	$(CXX) $(FLAG) -I$(INCLUDE) -L$(LIB) $(SOURCE) $(LDFLAG) -o str
	@echo ""
	
clean:
	rm -f $(JUNK)
