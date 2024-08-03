/*
 *
 * parse_input.cpp: This file contains functions related to input parsing.
 * All functions are only used during the initial phase of the solver's execution.
 *
 * The following functions are in this file:
 * - read_cnf
 * - read_line
 * - sort_literals
 * - parse_int
 * - enqueue
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <assert.h>
#include <math.h>

#include "flags.h"
#include "constants.h"
#include "structures.h"

extern my_manager* my_m;

/*
 * Sort literals in arr based on their indices.
 * This function is intended to be used for sorting
 * literals of input clauses. Just perform selection sort
 * as most clauses are very short.
 * Note how the literals are still represented as a normal integer
 * (as opposed on my_lit data type).
 *
 */
void sort_literals(int* arr,int size)
{
  //for each position
  for(int i=0;i<size-1;i++){
    int cur_lit = arr[i];
    int best = var_ind(cur_lit);
    int best_index = i;

    for(int j=i+1;j<size;j++){
      int lit = arr[j];
      if(var_ind(lit)<best){
	best = var_ind(lit);
	best_index = j;
      }
    }//end for j

    //at this point, we found the fit for spot i
    //swap
    int temp = arr[i];
    arr[i] = arr[best_index];
    arr[best_index] = temp;
  }
}

/*
 * Parse an integer from the string *in. 
 * Also update *in to skip the parsed integer.
 *
 */
int parse_int(char** in)
{
  int val = 0;
  char neg = 0;
  
  //skipping white space
  while(**in==' ' || **in=='\t'){
    (*in)++;
  }

  //deal with any leading sign
  if(**in=='-'){
    neg = 1;
    (*in)++;
  }else if(**in=='+'){
    (*in)++;
  }

  if(**in < '0' || **in > '9'){
    printf("Parse error: unexpected character %c\n",**in);
    exit(1);
  }

  //read the number part
  while(**in >= '0' && **in <= '9'){
    val = val*10 + (**in - '0');
    (*in)++;
  }//end while

  return (neg?-val:val);
}

/* 
 * Reads a line into the array line. 
 * Signals an error in case the
 * line fills the array completely (too long). 
 */
void read_line(char *line,unsigned long *i, FILE *ifp) 
{
  ++*i;
  fgets(line,MAX_LINE_LEN,ifp);
  if (line[MAX_LINE_LEN-1]=='\0') {
    printf("Line %lu exceeds max length of %d!\n",*i,MAX_LINE_LEN-2);
    exit(1);
  }
}

/*
 * Put l in the implication queue (assign).
 * This is intended to be used when a unit implication is 
 * discovered during input reading (a unit clause in the input, for example).
 *
 * These enqueued literals will be processed once we finish reading input.
 *
 */
void enqueue(my_lit l)
{ 
  my_var v = var(l);
  my_m->status[v] = l;
  my_m->level[v] = 1;
  my_m->reason[v] = NULL;
  undo(my_m->imp,v);
  my_m->assign[my_m->stack_offset++] = l;   
}

/*
 * Read the CNF formula from file fname and initialize the 
 * manager appropriately.
 *
 */
void read_cnf(char* fname)
{
  //my_m is our main data structure that will be used throughout the execution
  my_m = (my_manager*)calloc(1,sizeof(my_manager));
  
  my_manager* m = my_m;

  FILE *ifp;
  unsigned long i= 0;
  
  //line is a buffer for reading input
  char line[MAX_LINE_LEN]; 
  line[MAX_LINE_LEN-1] = '\n';
  int literals[MAX_CLAUSE_LEN];
  char c; 
  
  int cc,vc;
  int cur_clause_index = 0;

  if((ifp=fopen(fname,"r"))==NULL){
    printf("\nCannot open file: %s\n",fname);
    exit(1);
  }

  //main parsing loop
  while((c=getc(ifp))!=EOF){
    if(isspace(c)) continue; //skip any space at the beginning of the line
    else ungetc(c,ifp);
   
    if(c=='c' || c== '0'){
      //comment
      read_line(line,&i,ifp);
    }else if(c=='p'){
      //preamble line
      read_line(line,&i,ifp);
      if(sscanf(line,"p cnf %d %d",&vc,&cc)==2){
	m->original_clauses = (my_clause**)calloc(cc,sizeof(my_clause*));
	m->vc = vc;
	m->cc = cc;
	//m->cc is not finalized yet (we may skip clauses)
	//we have enough information to initialize most part of the manager
	init_manager();
      }else{
	printf("Unknown line %lu: %s",i,line);
	exit(0);
      }
    }else if((c=='-') || (isdigit(c) > 0)){
      //this line represents a clause
      int j=0;
      read_line(line,&i,ifp);
      char* to_read = line;
      char skip_clause = 0;
      
      //parse integers until we reach 0.
      while(1){
	int parse_lit = parse_int(&to_read);
	
	if(parse_lit==0){
	  //end of clause, break.
	  literals[j] = 0;
	  break;
	}//end if

	//check to make sure 
	//parse_lit is not set or resolved.
	//if it is, take the appropriate action.
	
	int var_index = (parse_lit<0?-parse_lit:parse_lit);		
	my_lit status = m->status[var_index];
	char is_set = 0; //0 for free, 1 for true, -1 for false.	

	if(status==0){
	  //this literal is free
	  is_set = 0;	  
	}else{
	  //this literal is set to true or false.
	  if(parse_lit<0){
	    is_set = (status==plit(var_index)?-1:1);
	  }else{
	    is_set = (status==plit(var_index)?1:-1);//v->pliteral->status;
	  }
	}

	if(is_set==1){
	  //this clause is already satisfied.
	  //skip the clause.
	  skip_clause = 1;
	  break;
	}

	if(is_set==-1){
	  //this literal is already falsified.
	  //skip this literal.
	  continue;
	}

	literals[j++] = parse_lit;
	
      }//end while(1)
      
      
      if(j==MAX_CLAUSE_LEN-1 && literals[j]!=0){
	//this line is too long
	printf("Clause at line %lu exceeds maximum length\n",i);
	exit(0);
      }

      //check for duplicated literals
      int k=0;
      int n=0;
      int duplicate_literals_count = 0;

      //j is the size (not including the trailing 0 of the current clause
      sort_literals(literals,j);
      
      if(!skip_clause){

	while(k<=j) {
	  //checks 
	  char duplicate_literal = 0;
	  for(int x=0; x<k; x++) {
	    
	    if(literals[x]==literals[k]) { 
	      // duplicate literals in same clause
	      duplicate_literal = 1;
	      ++duplicate_literals_count;
	      break;
	    }
	    else if(abs(literals[x])==abs(literals[k])) {
	      // literal and its negation in same clause 
	      skip_clause=1;
	      goto add_clause;
	    }
	  }//end for x
	  
	  if(duplicate_literal==0) {
	    //cnf->clauses[clause_index][k] = literals[k];
	    literals[n++] = literals[k++];
	  }
	  else {
	    //literals[k] can be discarded
	    k++;
	  }
	}//end while k<j

      }//endif !skip_clause	
      
      //now, we want to check if this clause is actually a unit clause or not
      if(n==2){
	//this clause is not sat and is unit (after removing any duplicate literals)
	int var_index = (literals[0]<0?-literals[0]:literals[0]);
	my_lit l;

	if(literals[0]<0){
	  l = nlit(var_index);
	}else{
	  l = plit(var_index);
	}

	my_lit* status = my_m->status;

	if(resolved(l)<0){
	  //this literal has already been resolved
	  //unsatisfiable
	  m->ok = 0;
	}
		
	if(m->status[var_index]==0){
	  //this literal is free, enqueue it
	  m->level[var_index] = 1;
	  m->reason[var_index] = NULL;
	  enqueue(l);
	}
	
	//there is no need to add this clause to the knowledge base
	skip_clause=1;
      }else if(n==1){
	//this is an empty clause.
	m->ok=0;
      }

    add_clause:
      
      if(!skip_clause){
	//n is now the size of this clause (including the ending 0)
	//n-1 is the real size of the clause
	//printf("init clause %d\n",cur_clause_index);
	init_clause(literals,cur_clause_index,n-1);
	cur_clause_index++;
      }
      
    }else if(c=='%'){
      //end of input indicator
      break;
    }else{
      read_line(line,&i,ifp);
      printf("Unknown line %lu: %s",i,line);
      exit(0);
    }//end if else c==?
  }//end while not eof

  //set the number of original clauses
  m->cc = cur_clause_index;       //original value.
  m->cur_cc = cur_clause_index;   //current value. Initially, they are the same.

  m->original_clauses_array_len = cur_clause_index;
  if(cur_clause_index!=cc){
    //some clauses were skipped
    m->original_clauses = (my_clause**)realloc(m->original_clauses,cur_clause_index*sizeof(my_clause*));
  }
  
  //close the input file pointer
  fclose(ifp);
}
