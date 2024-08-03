/*
 * manager.cpp: This file contains functions related to
 * the main my_manager structure used during the execution of the solver.
 * 
 * The following functions are in this file:
 * - init_clause
 * - init_manager
 * - finish_up_init_manager
 * - free_manager
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <math.h>
#include <time.h>
#include <string.h>

#include "flags.h"
#include "structures.h"
#include "constants.h"

#include <assert.h>  //must be defined after flags.h for NDEBUG to work

extern my_manager* my_m;

/*
 * Create a my_clause structure that contains literals in
 * 'literals' array. Initialize it with 'index' and put it in
 * the array of original clauses.
 *
 */
void init_clause(int* literals,int index,int size)
{
  my_manager* m = my_m;

  my_clause* temp = (my_clause*)calloc(1,sizeof(my_clause));  
  
  m->original_clauses[index] = temp;

  my_clause* cur = m->original_clauses[index];
  cur->size = size;
  cur->index = -(index+1);  //index of original clauses are negative (starting from -1)

  cur->lits = (my_lit*)calloc(size,sizeof(my_lit));

  my_m->cur_lit_count += size;
  for(int i=0; i < size; i++) {
    cur->lits[i] = lit_from_int(literals[i]);    
  }//end for i

}//end function init_clause

/*
 * Initialize my_manager my_m (the global variable).
 *
 */
void init_manager()
{
  my_manager* m = my_m;

  //decisions start at 2 since:
  //level 1: is for literals implied by the knowledge base (backbones).
  //level 0: is reserved to indicate variable is not implied 
  m->decision_level = 1;
  m->max_decision_level = 0;
  m->decisions = 0;
  m->conflicts = 0;
  m->cdc_count = 0;
  m->cdl_count = 0;
  m->cur_cdl_count = 0;
  m->cur_cdc_count = 0;
  m->cur_cc = 0;
  m->cur_lit_count = 0;
  m->original_clauses_count = 0;
  m->conflict_level = 0;  
  m->restart = 0;
  m->next_restart_conflict = LUBY_UNIT;
  m->stack_offset = 0;
  m->ok = 1;

  //m->vc is already set in read_cnf
  int vc = m->vc;

  //The size is 2*vc because every literal may be put on the stack (in an extreme case).
  m->assign = (my_lit*)calloc(2*vc,sizeof(my_lit));
  m->assign_top = m->assign;
    
  int init_decision_lit_size = (vc>VC_THRESHOLD?vc/10:vc);
  
  //allocate this conservatively
  m->decision_lit = (my_lit**)calloc(init_decision_lit_size,sizeof(my_lit*));
  m->decision_lit[1] = m->assign;
  m->decision_lit_size = init_decision_lit_size;
    
  //Allocating various arrays for variables
  m->level = (int*)calloc(vc+1,sizeof(int));  //my_var-indexed
  m->status = (my_lit*)calloc(vc+1,sizeof(my_lit)); //my_var-indexed
  m->reason = (my_clause**)calloc(vc+1,sizeof(my_clause*)); //my_var-indexed
  m->score = (double*)calloc(vc+1,sizeof(double)); //my_var-indexed
  
  m->var_order_heap = (heap*)calloc(1,sizeof(heap));
  init_heap(m->var_order_heap,vc);
  
  m->saved = (my_lit*)calloc(vc+1,sizeof(my_lit));
    
#if(VERIFY_SOLUTION)
  m->solution_stack = (my_lit*)calloc(vc,sizeof(my_lit));
  m->solution_stack_top = m->solution_stack;
#endif
  
  m->learned_clauses = (my_clause**)calloc(1,sizeof(my_clause*));
  m->learned_clauses_array_len = 1;
  
  m->imp = (implication_queue*)calloc(1,sizeof(implication_queue));
  init_heap(m->imp,vc);

  m->learned_clause_scores = (double*)calloc(1,sizeof(double));   
  int init_stack_and_save_size = vc/100;
  init_stack_and_save_size = (init_stack_and_save_size<10?10:init_stack_and_save_size);
  
  int init_cdc_size = vc/100;
  init_cdc_size = (init_cdc_size<100?100:init_cdc_size);
    
  m->cdc = (my_lit*)calloc(init_cdc_size,sizeof(my_lit));
  m->cdc_size = init_cdc_size;
  m->seen = NULL;   //allocation done in derive_conflict_clause. var-indexed
  m->stack = (my_lit*)calloc(init_stack_and_save_size,sizeof(my_lit));
  m->stack_size = init_stack_and_save_size;
  m->save = (int*)calloc(init_stack_and_save_size,sizeof(int));
  m->save_size = init_stack_and_save_size;
  
  //one slot for each literal
  m->watched = (my_clause***)calloc(2*vc,sizeof(my_clause**));
  m->watched_size = (int*)calloc(2*vc,sizeof(int));
  m->watched_len = (int*)calloc(2*vc,sizeof(int));
  
  //finishing up initialization
  m->score_inc = 1;
  m->score_inc_factor = 1/SCORE_INC_PARAM;
  
  m->kb_reduction_count = 0;
  m->clause_score_inc = 1;
  
  m->kb_simplification_count = 0;
  m->num_conflicts_for_next_simplify = 0;
  m->next_simplify_increment = NEXT_SIMPLIFY_INCREMENT;
  m->simplify_orig_kb = 0;
  m->simplify_learned_kb = 0;

  m->random_seed = INIT_RANDOM_SEED; 
  
  m->luby_unit = LUBY_UNIT;

  //these are in terms of number of conflicts
  m->save_progress = 0;  //start with no progress saving
  m->on_th = INIT_ON_TH;
  m->off_th = INIT_OFF_TH;
  m->on_th_inc = INIT_ON_TH_INC;
  m->off_th_inc = INIT_OFF_TH_INC;
  m->next_sp_switch = m->on_th;
}//end function init_manager

/*
 * Finish up the initialization of my_m.
 * This is intended to be called after read_cnf finishes.
 *
 * Also call process_unit_literal_queue to apply unit propagation
 * on the implications found so far.
 * 
 * Return 1 iff no conflict is found.
 */
char finish_up_init_manager()
{ 
  init_watched_literals();
  
  int n = my_m->vc;
  int seed = (int)my_m->random_seed;
  //rprintf("Random seed = %d\n",seed);
  srand(seed);
  
  for(int i=1; i<=n; i++){
    insert(my_m->var_order_heap,i);
  }//end for i

  char result = process_unit_literal_queue();
  
  if(!result){
    //inconsistency found at top level, return 0
    return 0;
  }
  
  simplify_original_kb();
  my_m->max_learned_clauses = my_m->cur_cc/3;  
  
  return 1;
}

/*
 * Free all memory related to my_m.
 *
 */
void free_manager()
{
  my_clause** clauses = my_m->original_clauses;
  int size = my_m->cur_cc;
  //free original clauses.
  for(int j=0; j<size; j++) {
    my_clause* clause = clauses[j];
    free(clause->lits);
    free(clause);
  }
  
  free(my_m->original_clauses); /* this takes care of freeing individual clause structures */

  clauses = my_m->learned_clauses;
  size = my_m->cur_cdc_count;
  //free learned clauses
  for(int j=0; j<size; j++) {
    my_clause* clause = clauses[j];
    if(clause!=NULL){
      free(clause->lits);
      free(clause);
    }
  }
  
  free(my_m->learned_clauses); /* this takes care of freeing individual clause structures */

  size = my_m->vc*2;
  my_clause*** watched = my_m->watched;
  for(int i=0;i<size;i++){
    my_clause** w = watched[i];
    free(w);
  }

  free(my_m->watched);
  free(my_m->watched_len);
  free(my_m->watched_size);

  free(my_m->cdc);
  free(my_m->assign);
  free(my_m->decision_lit);
  free(my_m->score);
  free(my_m->reason);
  free(my_m->status);
  free(my_m->level);

  if(my_m->seen!=NULL){
    free(my_m->seen);
  }
  
  free(my_m->saved);

#if(VERIFY_SOLUTION)
  free(my_m->solution_stack);
#endif
  
  free(my_m->stack);
  free(my_m->save);
  
  free_heap(my_m->var_order_heap);
  free(my_m->var_order_heap);
  
  free(my_m->learned_clause_scores);
  
  free_heap(my_m->imp);
  free(my_m->imp);
  
  free(my_m);
}//end function free_manager
