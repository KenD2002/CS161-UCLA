/*
 * watched_list.cpp: This file contains functions related
 * to the implementation of the watched literal scheme.
 * 
 * The following functions are in this file:
 * - double_watched_len
 * - half_watched_len
 * - add_watched_clause
 * - remove_watched_clause
 * - init_watched_literals
 * - declare_watched_literals
 * 
 * (printing and debuggin)
 * - print_watched_list
 * - check_watched_list_of_lit
 * - check_watched_list
 * - fully_watched
 * - check_watched_literal_completeness
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <math.h>
#include <string.h>

#include "flags.h"
#include "structures.h"
#include "constants.h"
#include <assert.h>

extern my_manager* my_m;

/*
 * Double the capacity of the watched list at index 'index'.
 *
 */
void double_watched_len(int index)
{
  int old_len = my_m->watched_len[index];
  int new_len = 2*old_len;

  my_clause** arr = (my_clause**)calloc(new_len,sizeof(my_clause*));
  my_clause** old = my_m->watched[index];

  for(int i=0;i<old_len;i++){
    arr[i] = old[i];
  }

  free(old);
  my_m->watched[index] = arr;
  my_m->watched_len[index] = new_len;
}

/*
 * Invariant: the watched array is filled at most 1/4 of its current capacity.
 * Half the capacity of the watched list at index 'index'.
 */
void half_watched_len(int index)
{
  int size = my_m->watched_size[index];
  if(size==1){return;}

  int new_len = my_m->watched_len[index]/2;  
  
  my_clause** arr = (my_clause**)calloc(new_len,sizeof(my_clause*));
  my_clause** old = my_m->watched[index];
  
  for(int i=0;i<size;i++){
    arr[i] = old[i];
  }

  free(old);
  my_m->watched[index] = arr;
  my_m->watched_len[index] = new_len;
}

/*
 * Add a clause to the list of watched clauses for literal l.
 * It is required that the literal be in either the 0 or 1 position of clause->literals.
 *
 */
void add_watched_clause(my_lit l,my_clause* clause)
{
  int ind = watched_index(l);
  int size = my_m->watched_size[ind];
  int len = my_m->watched_len[ind];
  
  if(len<=size){
    double_watched_len(ind);
  }
  
  my_clause** wl = my_m->watched[ind];
  wl[my_m->watched_size[ind]++] = clause;
    
}//end function add_watched_clause

/* 
 * Remove the clause from the list of clauses being watched by literal l.
 * It is required that literal be in either the 0 or 1 position of clause->literals.
 */
void remove_watched_clause(my_lit l,my_clause* clause) 
{
  if(clause->size<=1){
    //sanity check
    printf("Trying to remove from watched list of [%d] clause:",lit_index(l));print_clause(clause);
    exit(0);
  }

  int index = watched_index(l);
  int size = my_m->watched_size[index];
  my_clause** clauses = my_m->watched[index];

  int j = 0;
  int i;
  for(i=0;clause!=clauses[i];i++){;}
  
  j = i;
  i++;

  for(;i<size;i++){
    clauses[j++] = clauses[i];
  }

  my_m->watched_size[index]--;

  if(my_m->watched_size[index]<my_m->watched_len[index]/4){
    half_watched_len(index);
  }
}//end function remove watched

/*
 * Initialize watched lists for original set of clauses.
 */
void init_watched_literals()
{
  my_clause*** watched = my_m->watched;
  int* watched_len = my_m->watched_len;
  int size = 2*my_m->vc;

  //for each literal
  //allocate initial space for its watched list
  for(int i=0; i<size; i++) {	      
    watched[i] = (my_clause**)calloc(1,sizeof(my_clause*));
    watched_len[i] = 1;
  }//end for i
  
  my_clause** clauses = my_m->original_clauses;
  size = my_m->cc;

  //the two watched literals per clause are the first two in the list of literals
  //for each clause
  for(int j=0; j<size; j++) {
    my_clause* c = clauses[j];
    declare_watched_literals(c);
  }//end for j

}


/*
 * Assume that the first two literals in the clause are the ones
 * to be watched.
 * 
 */
void declare_watched_literals(my_clause* c)
{
  void add_watched_clause(my_lit,my_clause*);

  if(c->size<2){
    printf("Attempting to declare watched list on a unit clause:");
    print_clause(c);
    exit(0);
  }
  
  my_lit* lits = c->lits;
  
  add_watched_clause(lits[0],c);
  add_watched_clause(lits[1],c);
}

/*
 * Debuggin utility:
 * Print the watched list of literal l.
 *
 */
void print_watched_list(my_lit l)
{
  int index = watched_index(l);
  my_clause** list = my_m->watched[index];
  int size = my_m->watched_size[index];
  
  printf("\nWatched list of literal [%d]\n",lit_index(l));
  for(int i=0;i<size;i++){
    printf("%d) index:%d :",i,list[i]->index);
    print_clause(list[i]);		
  }
}

/*
 * Debuggin utility:
 * Check the watched list of literal l for any corruption.
 *
 */
void check_watched_list_of_lit(my_lit l,char check_binary)
{
  int ind = watched_index(l);	

  int size = my_m->watched_size[ind];
  for(int i=0;i<size;i++){
    my_clause* cur = my_m->watched[ind][i];
    if(cur->lits[0]!=l && cur->lits[1]!=l){
      printf("Watched list of literal [%d] is corrupted\n",lit_index(l));
      printf("Clause [index %d]\n",cur->index);
      print_clause(cur);
      printf("appears in the watched list of literal %d\n",lit_index(l));
      exit(0);
    }	 
  }

  for(int i=0;i<size;i++){
    for(int j=i+1;j<size;j++){
      if(my_m->watched[ind][i]==my_m->watched[ind][j]){
	printf("Decision = %"i64d" | conf = %"i64d"\n",my_m->decisions,my_m->conflicts);
	printf("Duplicate watched clause (index = %d) found in the list of literal %d\n",my_m->watched[ind][i]->index,lit_index(l));
	printf("Duplications found at indices %d and %d\n",i,j);
	print_clause(my_m->watched[ind][i]);
	exit(0);
      }		
    }	
  }

  if(check_binary){
    my_lit* status = my_m->status;
    for(int i=0;i<size;i++){
      my_clause* cur = my_m->watched[ind][i];
      if(cur->size==2){
	      
	if((free_lit(cur->lits[0]) && !unresolved(cur->lits[1])) || (free_lit(cur->lits[1]) && !unresolved(cur->lits[0]))){
	  print_location();
	  printf("Corrupted binary clause [index=%d]:\n",cur->index);
	  print_clause(cur);
	  exit(0);
	}
	      
      }
    }
  }

}

/* 
 * Debuggin utility:
 * Check the watch lists of all literals for corruption.
 * 
 */
void check_watched_list(char check_binary)
{
  int size = my_m->vc;
  for(int i=0;i<size;i++){
    my_lit p = plit(i+1);
    my_lit n = nlit(i+1);

    check_watched_list_of_lit(p,check_binary);
    check_watched_list_of_lit(n,check_binary);
  }
}

/*
 * Debuggin utility:
 * Return 1 iff c is in the watched lists of both
 * c->lits[0] and c->lits[1].
 *
 */
char fully_watched(my_clause* c)
{
  my_lit l0 = c->lits[0];
  my_lit l1 = c->lits[1];
  
  my_clause** wl = my_m->watched[watched_index(l0)];
  int size = my_m->watched_size[watched_index(l0)];
  char found = 0;

  //for each watched clause of l0.
  for(int i=0;i<size;i++){
    my_clause* cur = wl[i];
    
    if(cur==c){
      found = 1;
      break;
    }    
  }

  if(!found){return 0;}

  wl = my_m->watched[watched_index(l1)];
  size = my_m->watched_size[watched_index(l1)];

  found = 0;
  //for each watched cluase of l1
  for(int i=0;i<size;i++){
    my_clause* cur = wl[i];
    
    if(cur==c){
      found = 1;
      break;
    }    
  }

  return found;
}

/*
 * Debuggin utility:
 * Alarm if some clauses are not fully watched
 */
void check_watched_literal_completeness()
{
  //original clauses
  my_clause** oc = my_m->original_clauses;
  int size = my_m->cur_cc;
  for(int i=0;i<size;i++){
    my_clause* cur = oc[i];

    if(!fully_watched(cur)){
      print_location();
      printf("Clause not fully watched!:");
      print_clause(cur);
      printf("==================================\n");
      printf("Watched lists\n");
      printf("==================================\n");
      print_watched_list(cur->lits[0]);
      printf("**************************\n\n");
      print_watched_list(cur->lits[1]);
      exit(0);
    }
  }
}
