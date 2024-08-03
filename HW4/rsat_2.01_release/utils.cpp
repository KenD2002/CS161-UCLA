/*
 * utils.cpp: This files contains debugging utility,
 * some printing functions, and some array resizing functions.
 * 
 * The following functions are in this file:
 * - print_progress_header
 * - print_progress_footer
 * - print_progress
 * - check_pure
 * - print_clause
 * - print_location
 * - print_stats
 * - double_stack_len
 * - double_save_len
 * - double_cdc_len
 * - double_learned_clauses_array
 * - double_decision_lit_len
 * - half_decision_lit_len
 * - save_solution
 * - save_solution_to_file
 * - print_solution
 * - subsumed_clause
 * - verify_solution
 * - check_assignment_stack
 * - check_var_in_heap
 *
 */
#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <string.h>

#include "flags.h"
#include "structures.h"
#include "constants.h"

extern my_manager* my_m;

/*
 * Print the header of progress message.
 *
 */
void print_progress_header()
{
  if(!my_m->verbose){return;}
  rprintf("+----+-----------------+------------------+----------------------------------+---------------------------+---------+-----------+\n");
  rprintf("| %-2s | %-15s | %-16s | %-32s | %-25s | %-7s | %-9s |\n","Re","Conflicts","Original","Learned","Decisions"," Time","KB");
  rprintf("| %2s | %7s %7s | %7s %8s | %7s %7s %8s %7s | %7s %10s %6s | %7s | %4s %4s |\n","st","Max","Actual","Clauses","Literals","Max","Clauses","Literals","LPC","Total","Per Sec","C/D","","Red.","Sim.");
  rprintf("+----+-----------------+------------------+----------------------------------+---------------------------+---------+-----------+\n");
}

/*
 * Print the footer of the progress footer.
 *
 */
void print_progress_footer()
{
  if(!my_m->verbose){return;}
  rprintf("+----+-----------------+------------------+----------------------------------+---------------------------+---------+-----------+\n");
}

/*
 * Print a progress message.
 *
 */
void print_progress()
{
  if(!my_m->verbose){return;}
  extern clock_t start_time,end_time;
  
  //perform various calculations to obtain various interesting stats.
  my_manager* m = my_m;
  
  end_time = clock();  
  double time_used = (end_time - start_time)/(double)CLOCKS_PER_SEC;
  int64 cur_decisions = m->decisions - my_m->previous_decision_count;
  int64 cur_conflicts = m->conflicts - my_m->previous_conflicts;

  int cur_reduce_kb = 0;

  cur_reduce_kb = m->kb_reduction_count - my_m->previous_reduce_kb_count;

  int cur_simplify_kb = 0;
  cur_simplify_kb = m->kb_simplification_count - my_m->previous_simplify_kb_count;

  
  my_m->previous_decision_count = m->decisions;
  my_m->previous_conflicts = m->conflicts;

  my_m->previous_reduce_kb_count = m->kb_reduction_count;

  my_m->previous_simplify_kb_count = m->kb_simplification_count;

  int unit_clause_learned = my_m->decision_lit[2]-my_m->decision_lit[1];
  unit_clause_learned -= my_m->base_unit_clause_learned;

  start_time = end_time;
  
  //print the message
  rprintf("| %2d | %7"i64d" %7"i64d" | %7"i64d" %8"i64d" | %7d %7"i64d" %8"i64d" %7.1f | %7"i64d" %10.2f %6.3f | %7.3f | %4d %4d |\n",
	  m->restart,
	  m->next_restart_conflict,
	  m->conflicts,
	  m->cur_cc,
	  m->cur_lit_count,
	  (int)m->max_learned_clauses,
	  m->cur_cdc_count,
	  m->cur_cdl_count,
	  ((double)m->cur_cdl_count/m->cur_cdc_count),
	  cur_decisions,
	  (double)cur_decisions/time_used,
	  (double)cur_conflicts/cur_decisions,
	  time_used,
	  cur_reduce_kb,
	  cur_simplify_kb
	  );
}

/*
 * Debugging utililty:
 * Print a clause. Each literal is annotated with its current status 
 * and level of assignment.
 *
 */
void print_clause(my_clause* c)
{
  if(c==NULL){printf("(NULL)\n"); return;}
  
  int size = c->size;
  my_lit* lits = c->lits;
  my_lit* status = my_m->status;
  int* level = my_m->level;
  
  printf("(");
  for(int i=0;i<size;i++){
    my_var v = var(lits[i]);
    printf("%d%s(%d), ",lit_index(lits[i]),(status[v]==0?"":(status[v]==lits[i]?"s":"r")),level[v]);
  }//end for i
  printf(")\n\n");
}

/*
 * Debugging utility:
 * Print the current numbers of decisions and conflicts 
 * experienced by the solver.
 *
 */
void print_location()
{
  printf("Dec=%"i64d",Conf=%"i64d"\n",my_m->decisions,my_m->conflicts);
}

/*
 * Print execution statistics.
 * Intended to be called at the end of the execution.
 *
 */
void print_stats()
{
  rprintf("CNF stats: (%d vars, %"i64d" clauses)\n",my_m->vc,my_m->cc);
  rprintf("Decisions: %"i64d"\n",my_m->decisions);
  rprintf("Conflicts: %"i64d"\n",my_m->conflicts);
}//end function print_stats

/*
 * Debugging utility:
 * Check if any literal in the problem is pure (its negation does not appear).
 *
 */
void check_pure()
{
  int* lit_count = (int*)calloc(my_m->vc*2,sizeof(int));

  for(int i=0;i<my_m->cur_cc;i++){

    my_clause* c= my_m->original_clauses[i];

    for(int j=0;j<c->size;j++){
      my_lit l = c->lits[j];
      lit_count[watched_index(l)]++;
    }
  }//end for i

  for(int i=1;i<=my_m->vc;i++){
    my_lit p = plit(i);
    my_lit n = nlit(i);
    
    if(my_m->status[i]!=0){continue;}

    if(lit_count[watched_index(p)]==0){
      if(lit_count[watched_index(p)]==0){
	printf("var [%d] was eliminated\n",i);
      }else{
	printf("var [%d] is pure (-)\n",i);
      }
    }else if(lit_count[watched_index(n)]==0){
      printf("var [%d] is pure (+)\n",i);
    }
  }

  free(lit_count);
}

/*
 * Save the current assignments in the 
 * assignment stack to a file.
 *
 */
void save_solution_to_file()
{
  char* fname = "solution.txt";
  FILE* out;

  if(!(out=fopen(fname,"w"))){
    printf("Cannot open file: %s\n",fname);
    exit(0);
  }

  my_lit* stack = my_m->assign;
  my_lit* top = my_m->assign_top;

  while(stack<top){
    fprintf(out,"%d\n",lit_index(*stack));
    stack++;
  }

  fclose(out);
}

///////////////////////////////
// array size utils
///////////////////////////////

/*
 * Allocate a new array with capacity 2*cap for unit_size data.
 * Copy the first cap entries from old_arr to the new array.
 * Free old_arr, set *cap to the length of the new array.
 * Then return the pointer to the new array.
 *
 */
void* double_array_len(void* old_arr,int* cap,size_t unit_size)
{
  int old_len = *cap;
  int new_len = 2*old_len;
  void* new_arr = (void*)calloc(new_len,unit_size);
  
  memcpy(new_arr,old_arr,old_len*unit_size);
  
  *cap = new_len;
  free(old_arr);
  return new_arr;
}

void double_stack_len()
{
  my_lit* stack = my_m->stack;
  my_m->stack = (my_lit*)double_array_len(stack,&my_m->stack_size,sizeof(my_lit));

  return;
  
  int old_len = my_m->stack_size;
  int new_len = old_len*2;
  my_lit* old_stack = my_m->stack;
  my_lit* new_stack = (my_lit*)calloc(new_len,sizeof(my_lit));
  
  for(int i=0;i<old_len;i++){
    new_stack[i] = old_stack[i];
  }

  free(old_stack);
  my_m->stack = new_stack;
  my_m->stack_size = new_len;
}

void double_save_len()
{
  int* save = my_m->save;
  my_m->save = (int*)double_array_len(save,&my_m->save_size,sizeof(int));

  return;
  
  int old_len = my_m->save_size;
  int new_len = old_len*2;
  int* old_save = my_m->save;
  int* new_save = (int*)calloc(new_len,sizeof(int));
  
  for(int i=0;i<old_len;i++){
    new_save[i] = old_save[i];
  }

  free(old_save);
  my_m->save = new_save;
  my_m->save_size = new_len;
}

void double_cdc_len()
{
  my_lit* cdc = my_m->cdc;
  my_m->cdc = (my_lit*)double_array_len(cdc,&my_m->cdc_size,sizeof(my_lit));

  return;
  
  int old_len = my_m->cdc_size;
  int new_len = old_len*2;
  my_lit* old_cdc = my_m->cdc;
  my_lit* new_cdc = (my_lit*)calloc(new_len,sizeof(my_lit));
  
  for(int i=0;i<old_len;i++){
    new_cdc[i] = old_cdc[i];
  }

  free(old_cdc);
  my_m->cdc = new_cdc;
  my_m->cdc_size = new_len;  
}


/*
 * Double the capacity of the decision_lit array.
 *
 */
void double_decision_lit_len()
{
  my_lit** dec_lit = my_m->decision_lit;
  my_m->decision_lit = (my_lit**)double_array_len(dec_lit,&my_m->decision_lit_size,sizeof(my_lit*));

  int old_len = my_m->decision_lit_size;
  int new_len = old_len*2;
  my_lit** arr = (my_lit**)calloc(new_len,sizeof(my_lit*));
  my_lit** old = my_m->decision_lit;

  
  for(int i=0;i<old_len;i++){
    arr[i] = old[i];
  }

  free(old);
  my_m->decision_lit = arr;
  my_m->decision_lit_size = new_len;
}

/*
 * Assume at most only 1/4 of the array is in-use.
 * Half the capacity of the decision_lit array.
 *
 */
void half_decision_lit_len()
{
  int old_len = my_m->decision_lit_size;
  if(old_len==1){return;}
  int new_len = old_len/2;
  
  my_lit** arr = (my_lit**)calloc(new_len,sizeof(my_lit*));
  my_lit** old = my_m->decision_lit;

  for(int i=0;i<new_len;i++){
    arr[i] = old[i];
  }

  free(old);
  my_m->decision_lit = arr;
  my_m->decision_lit_size = new_len;
}

/*
 * Double the length of the learned clauses array.
 * This function also double the length of the array
 * that keeps the scores of learned clauses.
 *
 */
void double_learned_clauses_array()
{
  int old_len = my_m->learned_clauses_array_len;
  int new_len = 2*old_len;
  my_clause** arr = (my_clause**)calloc(new_len,sizeof(my_clause*));
  my_clause** old = my_m->learned_clauses;

  double* new_score_arr = (double*)calloc(new_len,sizeof(double));
  double* old_score_arr = my_m->learned_clause_scores;
  
  for(int i=0;i<old_len;i++){
    arr[i] = old[i];
    new_score_arr[i] = old_score_arr[i];
  }

  free(old);
  free(old_score_arr);
  my_m->learned_clause_scores = new_score_arr;
  my_m->learned_clauses = arr;
  my_m->learned_clauses_array_len = new_len;
}

/**************************************************************************
 *
 * Solution related utilities
 *
 **************************************************************************/

#if(VERIFY_SOLUTION)
/* copies the set literals from the assignment stack to the
 * solution stack.
 */
void save_solution()
{
  my_lit* stack = my_m->assign;
  while(stack < my_m->assign_top){
    *(my_m->solution_stack_top++) = *stack++;
  }
}
#endif//endif verify solution

/* 
 * Prints the current solution 
 * from the assignment stack.
 */
void print_solution()
{
  int size = my_m->vc;
  printf("v ");
  for(int i=0;i<size;i++){    
    printf("%d ",lit_index(my_m->assign[i]));
  }
  printf("0\n");
}

/******************************************************************************
 *      debugging utilities
******************************************************************************/

#if(VERIFY_SOLUTION)

/*
 * Return 1 iff clause c is currently satisfied.
 * 
 */
char subsumed_clause(my_clause* c)
{
  my_lit* lits = c->lits;
  my_lit lit;
  int size = c->size;
  my_lit* status = my_m->status;
  for(int i=0;i<size;i++){
    lit = lits[i];
    if(status[var(lit)]==lit){
      return 1;
    }
  }
  
  return 0;
}

/*
 * Debugging utility:
 * Check if the solution in the solution stack 
 * is correct or not.
 *
 */
char verify_solution()
{
    int count=0;
    
    //set all literals in solution
    my_lit* stack = my_m->solution_stack;
    int saved_num_decisions = my_m->decisions;
    int saved_max_dec_level = my_m->max_decision_level;
    my_lit* status = my_m->status;

    while(stack < my_m->solution_stack_top) {

      my_lit lit = *stack++;

      if(status[var(lit)]==neg(lit)){
	printf("\nerror: Inconsistency 1: %d",lit_index(lit));
	return 0;
      }

      if(status[var(lit)]==0){
	if(!set_decision(lit)){
	  printf("\nerror: Inconsistency 2: %d",lit_index(lit));
	  return 0;
	}
	else ++count;
      }
    }
    
    //check all clauses are either subsumed or isolated
    for(int i=0; i<my_m->cur_cc; i++) {
      my_clause* clause = my_m->original_clauses[i];
      //struct clause clause = manager->clauses[i];
      if(!subsumed_clause(clause)) { //clause not subsumed!
	
	print_clause(clause);
	printf("\nerror: clause %d not subsumed and not isolated",clause->index);
	return 0;
	    
      }
    }
    //done
    while(count--) undo_decide_literal();
    my_m->decisions = saved_num_decisions;
    my_m->max_decision_level = saved_max_dec_level;
    return 1;
}
#endif//endif verify solution

/* 
 * Debugging utility:
 * Ensures the followings:
 *
 * 1) every literal appears at most once on assignment stack
 * 2) every true literal appears on the stack
 * 3) every literal appearing on the stack is set to true.
 *
 *
 */
void check_assignment_stack()
{
  my_lit* stack = my_m->assign;
  my_lit* end = my_m->assign_top;
  my_lit* status = my_m->status;
  int dec_level = my_m->decision_level;

  while(stack<end){
    my_lit l = *stack;
    
    if(free_lit(l)){
      printf("Free literal [%d] appears on stack\n",lit_index(l));
      exit(0);
    }

    if(my_m->level[var(l)]>dec_level){
      printf("Literal decision corrupted [lit %d at level %d] dec level is %d\n",lit_index(l),my_m->level[var(l)],dec_level);
      exit(0);
    }

    my_lit* stack2 = stack+1;
    //check for duplication
    while(stack2<end){
      if(*stack2==l){
	printf("[%d] appears twice on stack\n",lit_index(l));
	printf("Appears first at position %d and again at position %d\n",stack-my_m->assign,stack2-my_m->assign);
	exit(0);
      }
      stack2++;
    }//end while stack2<end
    
    stack++;
  }//end while
  
  //making sure all set literals are on stack!
  int size = my_m->vc;
  for(int i=1;i<=size;i++){
    my_lit val = status[i];
    if(val==0){
      printf("Variable %d is not set.\n",i);
      continue;
    }
    
    //check to make sure val is on stack
    my_lit* stack = my_m->assign;
    char found = 0;
    
    while(stack<end){
      if(*stack==val){
	found = 1;
	break;
      }
      stack++;
    }//end while
    
    if(!found){
      printf("Set literal [%d] (level=%d) does not appear on stack\n",lit_index(val),my_m->level[i]);
    }
  }//end for i
}

/*
 * Debugging utility:
 * Check to make sure all free variables are in the variable heap!
 *
 */
void check_var_in_heap()
{
  int size = my_m->vc;
  for(int i=1;i<=size;i++){
    if(!my_m->status[i]){
      //var not set
      int ind = my_m->var_order_heap->indices[i];

      if(ind==0){
	printf("Something is wrong. Variable [%d] is not set [s=%d,l=%d], however, it is not in the heap.\n",i,lit_index(my_m->status[i]),my_m->level[i]);
	exit(0);
      }
    }
  }//end for i
}
