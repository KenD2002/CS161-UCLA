CC = g++
CFLAGS = -O3 -fomit-frame-pointer -D NDEBUG -static -Wall #-fno-strict-aliasing

EXEC_FILE = rsat

EXEC_FILES = rsat\
	     rsat.exe\

SOLVER_SRC = manager.cpp\
	     parse_input.cpp\
	     utils.cpp\
	     watched_list.cpp\
	     solver.cpp\
	     heap.cpp\
	     mem_alloc.cpp\
	     main.cpp\
	     kb_management.cpp\
	     experimental_code.cpp\

SOLVER_OBJS=$(SOLVER_SRC:.cpp=.o)

HEADERS = flags.h constants.h structures.h

.PHONY: clean all

rsat: solver.o
	$(CC) $(CFLAGS) $(SOLVER_OBJS) -o $(EXEC_FILE)

main.o: main.cpp
	$(CC) $(CFLAGS) -c main.cpp

solver.o: $(SOLVER_SRC) $(HEADERS)
	$(CC) $(CFLAGS) -c $(SOLVER_SRC) 

all: rsat

clean: 
	rm -f *.o $(EXEC_FILES)