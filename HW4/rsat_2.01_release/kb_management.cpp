/*
 * kb_management.cpp: This file contains functions related to 
 * the management of the knowledge base (clauses).
 * 
 * The following functions are in this file:
 * - add_conflict_clause
 * - remove_clause
 * - satisfied
 * - simplify_kb
 * - simplify_original_kb
 * - sort_clauses_by_scores
 * - locked
 * - reduce_kb
 *
 * (debugging)
 * - check_sorted_clause_array
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <iostream>
#include <assert.h>
#include <math.h>

#include "flags.h"
#include "structures.h"
#include "constants.h"

extern my_manager* my_m;

/*
 * Addd the current confict clause (my_m->conflict_clause) to the knowledge base
 *
 */
void add_conflict_clause()
{
  my_clause *cdc = my_m->conflict_clause;
  int size = cdc->size;
  int* levels = my_m->level;

  assert(size>1);
  
  my_lit* lits = cdc->lits;
  
  int assertion_level = my_m->assertion_level;
  char found = 0;
  
  //in this loop, we also want to make sure that the second literal in the clause
  //is falsified at the assertion level to make the 2-watched literal invariant hold.
  for(int i=0;i<size;i++){
    my_lit l = lits[i];
    my_var v = var(l);
    
    increment_literal_score(l);
    
    if(!found && levels[v]==assertion_level){
      //swap this literal with literal[1]
      my_lit temp = lits[1];
      lits[1] = lits[i];
      lits[i] = temp;
      found = 1;
    }
    
  }//end for i

  //add it to the appropriate watched lists
  declare_watched_literals(cdc);
  
  if(my_m->cur_cdc_count>=my_m->learned_clauses_array_len){
    double_learned_clauses_array();
  }
  
  my_m->learned_clauses[my_m->cur_cdc_count] = cdc;
  my_m->learned_clause_scores[my_m->cur_cdc_count] = 0;
  
  //set clause index
  cdc->index = my_m->cur_cdc_count;
  
  //update stats
  my_m->cur_cdc_count++;
  my_m->cdc_count++;
  my_m->cur_cdl_count+= size;
  my_m->cdl_count += size;
  
  increment_clause_score(cdc);
}//end function add_conflict_clause


/*
 * Remove this clause from the reason array.
 * Remove this clause from any watched list.
 * Free this clause.
 *
 */
void remove_clause(my_clause* c)
{
  my_clause** reason = my_m->reason;
  my_var v0 = var(c->lits[0]);
  my_var v1 = var(c->lits[1]);
  
  if(reason[v0]==c){
    reason[v0] = NULL;
  }else if(reason[v1]==c){
    reason[v1] = NULL;
  }

  remove_watched_clause(c->lits[0],c);
  remove_watched_clause(c->lits[1],c);

  free(c->lits);
  free(c);
}

/*
 * Return 1 if this clause is satisfied by some literals at level 1 (topmost).
 * (returning 1 means this clause can be removed from the knowledge base)
 */
char satisfied(my_clause* c)
{
  my_lit* lits = c->lits;
  my_lit* status = my_m->status;

  for(int i=0;i<c->size;i++){
    if(set(lits[i])>0){
      //this clause is satisfied
      return 1;
    }//end if
  }//end for i

  return 0;
}

/*
 * This function should be called after BCP at the topmost level (level 1).
 * It removes all learned clauses in the knowledge base that are satisfied at the topmost level.
 *
 */
void simplify_kb()
{
  if(!my_m->simplify_learned_kb){return;}
  
  int size = my_m->cur_cdc_count;

  if(size==0){return;}

  int removed_lits = 0;
  int j=0;
  my_clause** clauses = my_m->learned_clauses;
  double* score = my_m->learned_clause_scores;
  
  //for each learned clause
  for(int i=0;i<size;i++){
    my_clause* c = clauses[i];
    if(satisfied(c)){
      removed_lits += c->size;
      remove_clause(c);
    }else{
      clauses[i]->index = j;
      score[j] = score[i];
      clauses[j++] = clauses[i];
    }
  }

  my_m->cur_cdc_count = j;
  my_m->cur_cdl_count -= removed_lits;
  
  my_m->kb_simplification_count++;

  my_m->num_conflicts_for_next_simplify = my_m->conflicts+my_m->next_simplify_increment;

  //as of 6/6/07, the code below does not really do anything
  //as my_m->next_simplify_increment is currently 0.
  double removed_ratio = ((double)(size-my_m->cur_cdc_count))/size;

  if(removed_ratio<0.01){
    my_m->next_simplify_increment = (int)(my_m->next_simplify_increment*1.1);
  }else{
    my_m->next_simplify_increment = (int)(my_m->next_simplify_increment*0.9);;
  }
  
  my_m->simplify_learned_kb = 0;

}//end function simplify_kb

/*
 * Same as simplify_kb but for original clauses.
 *
 */
void simplify_original_kb()
{  
  if(!my_m->simplify_orig_kb){return;}

  int size = my_m->cur_cc;
  int removed_lits = 0;
  int j = 0;
  my_clause** clauses = my_m->original_clauses;

  for(int i=0;i<size;i++){
    my_clause* c = clauses[i];
    
    if(satisfied(c)){
      removed_lits += c->size;
      remove_clause(c);
    }else{
      clauses[j++] = clauses[i];
    }
  }//end for i
  
  my_m->cur_cc = j;
  my_m->cur_lit_count -= removed_lits;

  //memory usage optimization
  if(j<my_m->original_clauses_array_len*0.75){
    my_m->original_clauses = (my_clause**)realloc(my_m->original_clauses,sizeof(my_clause*)*j);
    my_m->original_clauses_array_len = j;
  } 
  
  my_m->simplify_orig_kb = 0;
}

/*
 * Debugging utility:
 * Check to make sure arr is sorted correctly.
 *
 */
void check_sorted_clause_array(my_clause** arr,double* score,int size)
{
  for(int i=0;i<size;i++){
    if(arr[i]!=NULL){
      if(arr[i]->index != i){
	printf("Sorted clause array corrupted: arr[%d]->index = %d\n",i,arr[i]->index);
	exit(0);
      }
    }

    if(i<size-1){
      if(score[i] > score[i+1]){
	printf("Sorted clause array corrupted: score[%d](%.4f) > score[%d](%.4f)\n",i,score[i],i+1,score[i+1]);
	exit(0);
      }
    }
  }//end for i
}

/*
 * Sort clauses in _arr by their scores in _score in ascending order.
 * size is the length of _arr and _score.
 * The sorting algorithm used is merge sort.
 * This implementation is *not* recursive as we want to minimize the memory overhead.
 * 
 * As a result, size has to be a power of 2. See how it is used in reduce_kb.
 *
 */
void sort_clauses_by_scores(my_clause*** _arr,double** _score,int size)
{    
  my_clause** arr = *_arr;
  double* score = *_score;
  my_clause** target = (my_clause**)calloc(size,sizeof(my_clause*));
  double* starget = (double*)calloc(size,sizeof(double));
  
  //assume size = 2^k for some integer k.
  int i = 0;
  
  //loop until finish
  for(;;i++){
 
    int block_size = (int)(pow(2,i));

    if(block_size>size/2){
      break;
    }
    
    int lindex = 0;
    int rindex = block_size;
    
    int l = 0;
    int r = 0;

    //for each position in the target array
    for(int j=0;j<size;j++){

      if(l==block_size && r==block_size){
	lindex += block_size;
	rindex += block_size;
	l = 0;
	r = 0;
	
	double s1 = score[lindex];
	double s2 = score[rindex];

	if(s1<s2){
	  target[j] = arr[lindex];
	  starget[j] = score[lindex];

	  lindex++;
	  l++;
	}else{
	  target[j] = arr[rindex];
	  starget[j] = score[rindex];	  

	  rindex++;
	  r++;
	}

      }else if(l==block_size){
	target[j] = arr[rindex];
	starget[j] = score[rindex];
	
	rindex++;
	r++;
      }else if(r==block_size){
	target[j] = arr[lindex];
	starget[j] = score[lindex];
		  
	lindex++;
	l++;
      }else{
	//both l and r are not empty
	double s1 = score[lindex];
	double s2 = score[rindex];

	if(s1<s2){
	  target[j] = arr[lindex];
	  starget[j] = score[lindex];
  
	  lindex++;
	  l++;
	}else{
	  target[j] = arr[rindex];
	  starget[j] = score[rindex];
	  
	  rindex++;
	  r++;
	}//endif else s1<s2
      }//endif else l==block_size && r==block_size
      
      if(target[j]!=NULL){
	target[j]->index = j;
      }
      
    }//end for j
    
    //done filling up target array
    my_clause** temp = target;
    target = arr;
    arr = temp;

    double* stemp = starget;
    starget = score;
    score = stemp;
    
  }//end for i

  *_arr = arr;
  *_score = score;

  free(target);
  free(starget);
}//end function sort clauses by scores

/*
 * Return 1 iff c is a reason for some literal.
 *
 */
char locked(my_clause* c)
{
  if(c->size<=1){
    return 1;
  }
  
  my_clause** reason = my_m->reason;

  my_clause* reason1 = reason[var(c->lits[0])];
  my_clause* reason2 = reason[var(c->lits[1])];

  return (reason1==c || reason2==c);
}

/*
 * Attempt to remove approximately half the learned clauses from the knowledge base.
 * 
 */
void reduce_kb()
{  
  int i;
  int num_learned_clauses = my_m->cur_cdc_count;

  if(num_learned_clauses<=0){
    return;
  }

  //after this point we can assume that num_learned_clauses is at least 1  
  double extra_lim = (double)(my_m->clause_score_inc)/num_learned_clauses;
  
  //sort the learned clauses by their activities
  double lg = log2(num_learned_clauses);
  int new_size = (int)lg;

  if(lg!=(int)lg){
    new_size = (int)(ceil(lg));
  }

  new_size = (int)(pow(2,new_size));
  
  my_clause** arr = (my_clause**)calloc(new_size,sizeof(my_clause*));
  double* score_arr = (double*)calloc(new_size,sizeof(double));

  for(int i=0;i<num_learned_clauses;i++){
    arr[i] = my_m->learned_clauses[i];
    score_arr[i] = my_m->learned_clause_scores[i];
  }
  
  for(int i=num_learned_clauses;i<new_size;i++){
    arr[i] = NULL;
    score_arr[i] = -100;
  }
  
  sort_clauses_by_scores(&arr,&score_arr,new_size);

  int kk = 0;
  for(int i=new_size-num_learned_clauses;i<new_size;i++){
    my_m->learned_clauses[kk] = arr[i];
    my_m->learned_clause_scores[kk] = score_arr[i];
    kk++;
  }//end for i

  free(arr);
  free(score_arr);

  //finish sorting 

  my_clause** clause_array = my_m->learned_clauses;
  double* score = my_m->learned_clause_scores;

  int removed_lits = 0;
  int j = 0;
  
  //iterate through the first half of the sorted array
  //and remove every clause possible
  for(i=0;i<num_learned_clauses/2;i++){

    char binary = 0;

    if(clause_array[i]->size <= 2){
      binary = 1;
    }

    if(!locked(clause_array[i]) && !binary){
      //remove it
      removed_lits += clause_array[i]->size;
      remove_clause(clause_array[i]);
    }else{      
      clause_array[i]->index = j;
      score[j] = score[i];
      clause_array[j++] = clause_array[i];
    }
  }//end for i=j
  
  //iterate through the second half of the sorted array
  //and remove clauses whose scores are low enough.
  for(;i<num_learned_clauses;i++){
    my_clause* cur = clause_array[i];

    char binary = 0;

    if(clause_array[i]->size <= 2){
      binary = 1;
    }

    if(!locked(cur) && ( score[i] < extra_lim) && !binary){
      //remove it
      removed_lits += clause_array[i]->size;
      remove_clause(clause_array[i]);
    }else{
      clause_array[i]->index = j;
      score[j] = score[i];
      clause_array[j++] = clause_array[i];
    }
  }//end for i

  my_m->cur_cdc_count = j;
  my_m->cur_cdl_count -= removed_lits;
  my_m->kb_reduction_count++;

  my_m->max_learned_clauses *= MAX_LEARNED_CLAUSES_MULTIPLIER;
}
