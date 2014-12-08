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

all: $(SOURCE)
	@echo ">> Z3 Source Dir: "$(Z3_path)
	@echo ""
	g++ -O3 -std=c++11 -fopenmp -static -I$(INCLUDE) -L$(LIB) $(SOURCE) -lz3 -lrt -o str -Wall
	@echo ""
	
clean:
	rm -f $(JUNK)
