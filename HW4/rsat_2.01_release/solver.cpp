/* 
 * solver.cpp: The file that contains all the core functions for a SAT solver.
 * We intend to make this file as self-contained as possible including any 
 * low-level function that are unnecessary to the main execution flow.
 * 
 * The following functions are in this file:
 * - solve (the main solving function)
 * - select_variable
 * - set_decision
 * - bcp (unit propagation)
 * - backtrack
 * - analyze_conflict 
 * - derive_conflict_clause
 * - removable (helper for derive_conflict_clause)
 * - assert_conflict_clause
 * - get_luby (for restarting)
 * - process_unit_literal_queue
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
clock_t start_time,end_time;

#if(TIME_OUT)
extern double time_out;  //time out limit
extern clock_t start_t;  //the starting time of the solver
#endif

/*
 * Return the ith number of the luby sequence.
 * This function is called to determine the restarting schedule.
 *
 */
int get_luby(int i)
{
  if(i==1){return my_m->luby_unit;}  
  double k = log2(i+1);
  
  if(k==round(k)){
    return (int)(pow(2,k-1))*my_m->luby_unit;
  }else{
    k = (int)floor(k);
    return get_luby(i-(int)pow(2,k)+1);
  }
}//end function get luby

/*
 * Helper function for derive_conflict_clause.
 * Used to perform conflict clause minimization.
 * Return 1 if literal l can be removed from the current
 * conflict clause (in cdc) without introducing any new
 * literal.
 *
 * minl is a simple hash function which could quickly tell
 * us that l cannot be removed.
 * 
 *
 * stack contains the literals yet to be resolved away.
 * save contains the indices of variables on the stack.
 *
 * The main idea for this function is the keep resolving away literals 
 * on the stack until none is left. If at the end of the process,
 * no new literal is introduced, the literal can be removed.
 * Otherwise, the literal cannot be removed.
 *
 * This process of conflict minimization is really a partial implementation
 * of the AllUIP approach. We perform additional resolutions on all literals 
 * at lower level of see if the contribution from each level can be represented
 * with fewer literals or not.
 */
inline char removable(my_lit l,unsigned int minl)
{  
  //this seen array currently contains a 1-flag for each literal in the conflict clause.
  char* seen = my_m->seen;
  my_lit* stack = my_m->stack;
  int stack_index = 0;
  int stack_size = my_m->stack_size;
  int* save = my_m->save;
  int save_size = my_m->save_size;
  int size = 0;
  my_clause** reasons = my_m->reason;
  int* levels = my_m->level;
  
  //initially, the stack contains only the literal in question
  stack[stack_index++] = l;
  
  //main while loop
  //loop until all literals on the stack have been resolved away.
  while(stack_index>0){
    stack_index--;
    
    //pop a literal from the stack
    my_lit cur = stack[stack_index];
    my_var cur_v = var(cur);
    //inspect its reason
    my_clause* reason = reasons[cur_v];

    my_lit* lits = reason->lits;
    int rsize = reason->size;    
    int begin = 1;

    //for each literal in the reason
    for(int i=begin;i<rsize;i++){     
      my_lit cur_lit = lits[i];
      my_var index = var(cur_lit); //the variable index of this literal
      int level = levels[index];

      //if seen[index]==1, this literal already involved in the conflict analysis. 
      //if seen[index]==0, this literal is not in the conflict. But, perhaps, all its antecedents are involved. We need to keep on looking.

      if(!seen[index]&& level != 1){

	//At this point, we know this literal is not directly in the conflict analysis (because seen is 0).
	//Here we check if this literal's antecedents are all be involved in the conflict analysis.
	//if this literal is a decision literal (the else case below), too bad. It does not even have any antecedent. Return false.
	//if (1<< (this literal's level)) & minl == 0 (also the else case), it means (guarantees) no literal of the level were present in the conflict analysis.
	//this just implies that this current literal (cur_lit) can never satisfy the condition above, return false.	
	//otherwise, this literal MAY have all antecedent present in the conflict analysis, push it on the stack for further inspection.
	if( (reasons[index]!=NULL) && ((1<< (level)) & minl)){
	  //this literal is promising, push it on the stack and remember it in save array.
	  seen[index] = 1;
	  
	  if(stack_index>=stack_size){
	    double_stack_len();
	    stack_size = my_m->stack_size;
	    stack = my_m->stack;
	  }

	  if(size>=save_size){
	    double_save_len();
	    save_size = my_m->save_size;
	    save = my_m->save;
	  }

	  stack[stack_index++] = cur_lit;
	  save[size++] = index;
	}else{
	  //this literal, l, is NOT removable
	  //since l is not removable, we need to clean up all the seen entries
	  //that we set in this function call.
	  for(int j=0;j<size;j++){
	    seen[save[j]] = 0;
	  }

	  return 0;
	}//end if else

      }//end if !seen
    }//end for i
  }//end while
  
  //at this point, the literal l can be removed from the conflict clause.
  //Note how we do not clean up the seen array in this case. This is because
  //we know all those set entries have antecedents that meet the removing criteria.
  //We can simply remember this information so that future calls to this function
  //have a chance to do less work.

  return 1;
}//end function removable

/*
 * Derive an asserting conflict clause.
 * conf is the conflicting clause.
 * clevel is the level of the conflict.
 * *alevel must be set to the assertion level upon return.
 *
 * The idea is to keep resolving literals (at clevel) that are involved in 
 * the conflict by their reasons until we only have 1 literal 
 * at the level of the conflict left.
 *
 */
int derive_conflict_clause(my_clause* conf,int clevel,int* alevel)
{
  //number of literals at clevel.
  int num_lits_at_clevel = 0;
  my_lit next_lit = 0;
  my_lit* next_on_stack = my_m->assign_top;
  
  my_m->seen = (char*)calloc(my_m->vc+1,sizeof(char));
  char* seen = my_m->seen;

  int assertion_level = 1;
  my_m->assertion_level = 1;
  
  my_m->cdc_index = 0;  
  my_lit* cdc = my_m->cdc;
  int cdc_size = my_m->cdc_size;
  
  int* levels = my_m->level;
  my_clause** reasons = my_m->reason;

  //save a place for the asserted literal. We will fill this spot later.
  cdc[my_m->cdc_index++] = 0;
  
  if(clevel<=1){
    //conflict is fatal, because it occurs at level 1 (top)    
    cdc[0] = 0;
    cdc[1] = 0;
    free(my_m->seen);
    my_m->seen = NULL;

    *alevel = 0;

    return 0;
  }

  //as long as we have more literals to resolve
  do{

    //debugging code
    if(conf==NULL){      
      print_location();
      printf("Inside derive conflict clause [%"i64d"]\n",my_m->conflicts);
      printf("Reason of literal [%d] is NULL\n",lit_index(next_lit));
      printf("Decision literal of level %d is [%d], # lits at clevel = %d\n",clevel,lit_index(*(my_m->decision_lit[clevel])),num_lits_at_clevel);
      exit(0);
    }
    
    int size = conf->size;			
    my_lit* lits = conf->lits;    
    int begin = (next_lit==0?0:1);
    
    //usually, we want to skip the first literal in the clause because
    //it is the literal we are resolving on. The only exception is the very first clause.
    for(int i=begin;i<size;i++){
    
      //for each literal in clause conf
      //inspect each literal and decide whether
      //1) to put it in the learned clause OR
      //2) to resolve on it in the future
      my_lit cur_lit = lits[i];      
      int index = var(cur_lit); //variable index of the current literal
      int level = levels[index];
      
      //we can skip this literal if
      // 1) we have seen it before
      // 2) it is falsified at level 1 (we can always resolve away such literal by our top-level implication)
      if(!seen[index] && (level > 1)){
	//if we have not seen this variable
	//mark it seen and increase its score
	seen[index] = 1;
	increment_literal_score(cur_lit);  //increase scores of those involve in the conflict
	
	//there are 2 possible actions here
	// 1) if the literal is falsified at clevel, we must keep on resolving it.
	//    In this case, just increment num_lits_at_clevel is enough.
	// 2) if the literal is falsified at a lower level, we must add it to the conflict clause.
	if(level==clevel){
	  //this literal's value was set at clevel
	  num_lits_at_clevel++;

	}else{
	  //this literal's value was set before clevel
	  //add it to the conflict clause	
	  if(my_m->cdc_index>=cdc_size){
	    double_cdc_len();
	    cdc_size = my_m->cdc_size;
	    cdc = my_m->cdc;
	  }
	  
	  //put it in the cdc array
	  cdc[my_m->cdc_index++] = cur_lit;
	  
	}//end if else
      }//end if seen
    }//end for i
    //finish inspecting the current clause
    
    //now, we must find the next variable on stack that is involved in this conflict.
    //a variable is involved if it's seen entry is set to 1.
    while(1){
      next_on_stack--;
      assert(next_on_stack>=my_m->assign);

      int index = var(*next_on_stack);
      
      if(seen[index]){
	break;
      }
    }//end while 1
    
    next_lit = *next_on_stack;      //next_lit is now the next literal in the stack that is involved in the conflict
    my_var next_var = var(next_lit);
    seen[next_var] = 0;  //mark next_lit not seen, because we exclude it from the learned clause
    num_lits_at_clevel--; //coz we just expanded on next_lit
        
    //set conf to be the reason of next_lit
    if(reasons[next_var]!=NULL){
      conf = reasons[next_var];

      if(conf->index>=0){
	//only bump the activity of those clauses learned
	increment_clause_score(conf);
      }

    }else{
      //this should happen only if num_lits_at_clevel==0
      //we should be out of the loop next
      conf = NULL;
    }

  }while(num_lits_at_clevel>0);

  //now, we can put the asserted literal in the first position of the conflict clause.
  cdc[0] = neg(next_lit);
  seen[var(next_lit)] = 1;

  //end main conflict clause derivation
  
  
  //begin conflict clause mininimization
  int size = my_m->cdc_index;
  int i=size,j=size;

  unsigned int minl = 0;

  //first, compute a hash value for the literals in the cdc array
  //The ith bit of minl is 1 if some literal in the cdc array is falsified
  //at a level L such that l%32 == i.
  for (i = 1; i<size; i++){
    my_lit cur = cdc[i];
    int level = levels[var(cur)];
    minl |= 1 << (level & 31);       
  } 

  int start = 1;
  
  for (i = j = start; i < size; i++){
    my_lit cur = cdc[i];
    my_var cur_v = var(cur);
    
    //only retain this literal if either it is a decision literal or if it cannot be removed.
    //otherwise, we skip it (nothing to do in this case).
    if((reasons[cur_v]==NULL) || !removable(cur,minl)){
      int level = levels[cur_v];
      
      if(level>assertion_level){ 
	assertion_level = level; 
      }
      
      cdc[j++] = cdc[i];
    }
  }//end for i=j=X

  *alevel = assertion_level;  

  int final_size = size-(i-j);
  
  free(seen);
  my_m->seen = NULL;

  //i-j is the number of literals in the conflict clause skipped by the minimization step
  return final_size; //return the size of the conflict clause

}//end derive_conflict_clause

/*
 * Analyze the current conflict (from conflicting_clause) at clevel.
 * At the end, set my_m->conflict_clause to the derived conflict clause
 * and set my_m->assertion_level to the corresponding assertion level 
 * and set my_m->conflict_level to be clevel.
 * 
 * Another side-effect of this is to determine whether to turn progress saving
 * on or off. This is determined based on the value of my_m->next_sp_switch.
 */
void analyze_conflict(my_clause* conflicting_clause,int clevel)
{
  //control progress saving here.
  if(my_m->conflicts>=my_m->next_sp_switch){
    //flip the status of save_progress
    my_m->save_progress = 1-my_m->save_progress;
        
    //update threshold values
    int inc = 0;
    if(my_m->save_progress){
      //OFF==>ON
      my_m->on_th += my_m->on_th_inc;    
      inc = my_m->off_th;
    }else{
      //ON==>OFF
      my_m->off_th += my_m->off_th_inc;
      inc = my_m->on_th;
    }
    
    //schedule the next switch
    my_m->next_sp_switch += inc;
  }
  //done switching progress saving

  //begin conflict analysis
  
  my_m->conflict_level = clevel;
  ++my_m->conflicts;

  int assertion_level = 0;
  
  //derive an asserting conflict clause
  int size = derive_conflict_clause(conflicting_clause,clevel,&assertion_level);
  my_m->assertion_level = assertion_level;

  if(size>0){
    //a normal conflict clause
    //put it in a clause structure, initialize it and return.
    my_clause* conflict_clause = (my_clause*)calloc(1,sizeof(my_clause));
    my_lit* lits = (my_lit*)calloc(size,sizeof(my_lit));
    my_lit* cdc = my_m->cdc;
    
      
    for(int i=0;i<size;i++){
      lits[i] = cdc[i];
    }
    
    conflict_clause->size = size;
    conflict_clause->index = 1;
    conflict_clause->lits = lits;
    
    my_m->conflict_clause = conflict_clause;           
  }else{
    //size==0, this problem is UNSAT.
    //set assertion level to 0, the main solving function will take care of this.
    my_m->assertion_level=0;
    my_m->conflict_clause = NULL;
  }
  
}//end function analyze_conflict

/* 
 * Undo all literals at level above and including level.
 * After returning from this function, the decision level 
 * should be dest-1. Hence, the subsequent decision will be
 * made at level dest--the last level erased.
 * 
 */
void backtrack(int dest)
{
  //check this, otherwise, erase level will erase assignments of previous levels
  if(my_m->decision_level<dest){
    //this may happen if the solver tries to restart while at level 1 (top).
    return;
  }
  
  my_lit* target = my_m->decision_lit[dest];
  my_lit* stack = my_m->assign_top;
  int* level = my_m->level;
  my_lit* status = my_m->status;
  my_clause** reason = my_m->reason;
  my_lit* saved = my_m->saved;
  
  //for each assignment on the stack down to level dest.
  while(stack>target){

    stack--;
    my_lit l = *(stack);   
    my_var v = var(l);
    
    if(my_m->save_progress==1){
      //consider saving progress
      char relate = 0; 
      //even though by default, we save all assignments,
      //it is possible to be more selective in what we save.
      
      if(relate==0){
	//save progress
	saved[v] = l;
	
      }else if(relate==1){
	saved[v] = 0;
	
      }else if(relate==-1){
	//flip
	saved[v] = neg(l);
      }//end if else relate==0,1,-1
      
    }
    
    //reset various fields.
    reason[v] = NULL;
    level[v] = 0;
    status[v] = 0;
    //put the variable back in the variable heap.
    undo(my_m->var_order_heap,v);      
  }//end main while loop
  
  my_m->assign_top = stack;
  my_m->decision_level = dest-1; //restore the decision level so that the next decision is made at level dest.  
}//end function backtrack

/*
 * Apply unit propagation to all literals currently on the assignment stack.
 * This function is intended to be called after we finish reading the input file.
 *
 * Return 1 iff a conflict is found.
 */
char process_unit_literal_queue()
{
  //check the implication queue to see if there is any enqueued implication.
  my_var v = dequeue(my_m->imp);

  if(v!=0){
    //if there is, call bcp.
    my_m->simplify_orig_kb = 1;
    my_m->simplify_learned_kb = 1;
    my_m->stack_offset--;
    int res = bcp(my_m->status[v]);    
    my_m->stack_offset = 0;
    return res;
  }
  
  //no enqueued implication, return 1.
  return 1;
}//end function process unit literal queue

/*
 * Perform unit propagation starting at the assignment of literal l.
 * Return 1 if no conflict arises, otherwise return 0.
 *
 * In case of conflict, call analyze_conflict before returning.
 */
char bcp(my_lit l)
{
  //last points to the most recent implication on the assignment stack.
  my_lit* last = my_m->assign_top;
  int* level = my_m->level;
  my_lit* status = my_m->status;
  my_clause** reason = my_m->reason;
  my_clause*** watched = my_m->watched;
  int* watched_size = my_m->watched_size;  
  int slevel = level[var(l)];
  implication_queue* q = my_m->imp;
  
  //put this literal (l) into the priority queue
  undo(q,var(l));

  *(last++) = l;

  status[var(l)] = l;
  
  //usually, stack_offset is 0. It could be > 0 only at the first call 
  //to bcp when we implications enqueued in the assignment stack (see process_unit_literal_queue).
  //stack_offset has compensated for *(last++) above
  last += my_m->stack_offset;

  my_var v;
  
  //keep dequeuing variable from the implication queue
  while((v=dequeue(q))!=0){
    my_lit lit = status[v];
    my_lit neg_lit = neg(lit);
    int wi = watched_index(neg_lit); //wi is the array index of neg_lit
    //since neg_lit is now false, we need to traverse its watched list.
    
    //the watched list of neg_lit
    my_clause** watched_list = watched[wi];
    my_clause** pointer = watched_list;
    my_clause** end = watched_list+watched_size[wi];
    
    //for each clause in the watched list of neg_lit
    //find a new literal to watch
    while(watched_list<end){

      my_clause* clause = *(watched_list++);
      my_lit* lits = clause->lits;

      my_lit first_lit = lits[1];
      
      //make sure that neg_lit is in the second position in the array
      if(first_lit!=neg_lit){
	lits[1] = lits[0];
	lits[0] = first_lit;		
      }
      
      if(set(lits[0])){
	//this clause is already satisfied, skip it
	//put it in the same watched list (even though this current literal is already falsified!)	    
	
	*(pointer++) = clause;
	continue;
      }
      
      int clause_size = clause->size;
	  
      //search for an un-falsified literal in lits[2...n]
      //note that if clause_size==2, then there is nothing to search.
      //the current clause is guaranteed to be either unit or empty.
      if(clause_size>2){
	
	char found = 0;
	my_lit temp = lits[1];
	    
	int k = 2;
	for(;k<clause_size;k++){
	  my_lit temp2 = lits[k];
	  if(unresolved(temp2)){		
	    lits[1] = temp2;
	    lits[k] = temp;
	    //add this current clause to the watched list of the new found literal.
	    add_watched_clause(temp2,clause);		
	    found = 1;
	    break;
	  }
	}//end for k

	if(found){
	  //done with this clause, move on to the next clause
	  continue;
	}
	
      }//end if clause_size > 2
      
      //at this point, we know we could not find a new unresolved literal from lits[2..n]
      //(this is because alls of them are resolved or none of them even exits)
      //all we have to do now is check whether there is a conflict or not
      //basically, if lit[0] is free, we have a unit clause
      //if lit[0] is falsified, we have a contradiction!
	
      my_lit other_lit = lits[0];
      if(status[var(other_lit)]==neg(other_lit)){
	
	//here, we must pop everything out of the queue
	//move stack_top to last
	//because every literal on the stack has a chance of participating in the conflict
	//[even if it is not yet processed]
	
	while((v=dequeue(q))!=0){
	  //nothing here
	}
	
	my_m->assign_top = last;
	
	//move the rest of neg_list watched clauses into their appropriate positions
	*(pointer++) = clause;
	while(watched_list<end){
	  *(pointer++) = *(watched_list++);
	}
	      
	watched_size[wi] -= watched_list-pointer;
	
	//set the conflicting clause to this clause so
	//that we can later perform conflict analysis correctly.
	my_m->conflicting_clause = clause;

	assert(last==my_m->assign_top);	      
	
	return 0;	
      }else{
	
	//we have a unit implication in this case
	my_lit unit_lit = other_lit;
	my_var unit_var = var(unit_lit);
	    
	if(status[unit_var]==0) {
	  //this literal is implied for the first time
	  
	  reason[unit_var] = clause;	  
	  status[unit_var] = unit_lit;
	  level[unit_var] = slevel;

	  //put this unit variable into the implication queue
	  undo(q,unit_var);
	  *(last++) = unit_lit;
	  
	}//end if else unit for the first time
	    
	*(pointer++) = clause;
      }//end if else
	  
    }//end while more clauses in watched list of neg_lit		
    
    watched_size[wi] -= watched_list-pointer;

  }//end while more literal to process
  
  my_m->assign_top = last;
  return 1;
}//end function bcp

/*
 * Add the current conflict clause to the knowledge base
 * and apply unit propagation (call bcp) on it.
 * Return 0 iff unit propagation derives a conflict.
 *
 */
char assert_conflict_clause()
{
  if(my_m->vc>VC_THRESHOLD && my_m->decision_level<my_m->decision_lit_size/4){
    half_decision_lit_len();
  }
  
  my_clause* conflict_clause = my_m->conflict_clause;
  int size = conflict_clause->size;
  
  if(size>1){
    //Add this conflict clause to the knowledge base only if it is not unit.
    add_conflict_clause();
  }

  my_lit fuip = conflict_clause->lits[0];
  my_var fuip_var = var(fuip);
  my_m->level[fuip_var] = my_m->assertion_level;
  
  my_m->reason[fuip_var] = (size>1?conflict_clause:NULL);
  
  if(size==1){
    free(conflict_clause->lits);
    free(conflict_clause);
    my_m->conflict_clause = NULL;
    my_m->simplify_orig_kb = 1;
    my_m->simplify_learned_kb = 1;
  }

  my_m->score_inc *= my_m->score_inc_factor;
  my_m->clause_score_inc *= CLAUSE_SCORE_INC_FACTOR;    

  return bcp(fuip);
}//end function assert conflict clause

/*
 * Set literal l to true. Set this literal to be the decision literal of the level.
 * Propagate its effects (by calling bcp).
 * Returns 0 iff bcp can derive a conflict.
 *
 */
char set_decision(my_lit l) 
{
  if(my_m->decision_level > my_m->max_decision_level) {
    my_m->max_decision_level = my_m->decision_level;
  }

  int level = ++(my_m->decision_level);
  ++(my_m->decisions);  
  
  my_var v = var(l);
  my_m->level[v] = level;
  my_m->reason[v] = NULL;
  
  if(level>=my_m->decision_lit_size){
    double_decision_lit_len();
  }

  my_m->decision_lit[level] = my_m->assign_top;  

  return bcp(l);
}//end function set decision

/*
 * Return the free variable with the highest score.
 * Return 0 if no free variable remains.
 *
 */
my_var select_variable()
{

#if(USE_RANDOM_ORDER)
  double random_var_freq = 0.2;
  
  double r = (double)rand()/RAND_MAX;

  if(r < random_var_freq){
    my_var next = my_m->vc*((double)rand()/RAND_MAX)+1;
    if(my_m->level[next]==0){
      return next;
    }//end inner if
  }//end if
#endif

  heap* h = my_m->var_order_heap;

  while(!empty(h)){
    my_var next = get_min_element(h);   //this takes care of restructuring heap
    if(my_m->level[next]==0){
      //if this variable is free, return it
      return next;
    }//end if
  }//end while

  //no more free variable:SAT
  return 0;
}//end function select variable

/*
 * The main solving function.
 * Solve the SAT problem stored in the manager my_m.
 * Return 1 if SAT, 0 if UNSAT, and -1 if UNKNOWN (timeout).
 *
 * The idea is to keep making decisions until either a solution 
 * or a conflict is found. 
 * 
 * If a solution is found, return.
 * If a conflict is found, perform conflict analysis, backtrack, 
 * and apply bcp to the new cluase. This is repeated until no
 * conflict remains. Then the solver continue to the loop.
 * 
 */
int solve()
{
  start_time = clock();
  
  my_m->previous_decision_count = 0;
  my_m->previous_conflicts = 0;
  my_m->previous_reduce_kb_count = 0;
  my_m->previous_simplify_kb_count = 0;
  
  //we use the value of result to determine when to return from this function
  //result==-2 means that we have not found a solution.
  int result = -2;
    
  //this is the main loop. Each iteration is 1 decision
  while(1){        

    if(result==0){
      //UNSAT, break and return.
      break;
    }


    /******************************************
     *
     * Loop invariant: 
     * At this point of the loop, the 
     * solver state is closed under
     * unit resolution and is 1-consistent.
     * In other words, unit propagation
     * cannot derive any implication at
     * this point, and there is no 
     * conflict.
     * 
     * 
     * The next thing we do is to check whether 
     * it is time to restart or not, then we
     * check if it is time to manage the knowledge 
     * base or not (simplify, delete,...).
     * After all these, we pick a decision variable
     * and make a decision on it.
     *
     *******************************************/

#if(TIME_OUT)
    //rough implementation of timeout
    if(my_m->decisions%2000==0 && time_out>0){
      double elapsed = get_cpu_time();
      if(elapsed > time_out){
	backtrack(2);
	return -1;
      }
    }
#endif//endif time out

    if(my_m->conflicts>=my_m->next_restart_conflict){	
      //time to restart
      //note how we do not change the value of result (-2).
	
      print_progress();

      backtrack(2);

      my_m->restart++;

      int restart = my_m->restart;
      my_m->restart_conflict_incr = get_luby(restart+1);
      my_m->next_restart_conflict = my_m->conflicts + (int)my_m->restart_conflict_incr;
	
      simplify_original_kb();
    }//endif meet restart criteria

    if(my_m->simplify_learned_kb && my_m->decision_level==1 && my_m->conflicts >= my_m->num_conflicts_for_next_simplify){
      simplify_kb();
    }

    int num_assigned = (my_m->assign_top - my_m->assign);
      
    if(my_m->cur_cdc_count >= my_m->max_learned_clauses + num_assigned){
      reduce_kb();
    }

    /*****************************************************
     *
     * End checking restarting criteria and managing KB.
     *
     *****************************************************/
    
    //Jump directly to the label "pre_decision" if you want a clean way of bypassing the call to select_variable
    
    my_lit literal;
      
    //select a variable as the decision variable
    my_var dec_var = select_variable();
    
    if(dec_var==0){      
      //solution found!!
      result = 1;      	
      print_progress();
      
#if(VERIFY_SOLUTION)
      save_solution();
#endif
      print_progress_footer();
	
      if(my_m->print_mode==2){
	print_solution();
      }
	
      backtrack(2);
      break;
    }//endif solution found      
    
    //decide which phase of dec_var to try first
    if(my_m->saved[dec_var]==0 || !my_m->save_progress){	
      literal = nlit(dec_var);
    }else{	
      literal = my_m->saved[dec_var];
    }//end if else use saved phase or not
      
    //literal must be already set at this point!
    //pre_decision: //currently, this label is not used

    //make the decision
    char res = set_decision(literal);                
    //res is 1 if everything was okay, 0 if there was a conflict

    //deal with conflict, if any.
    while(res!=1){
      //at this point, the current state of the solver has a conflict.
      
      //analyze the conflict (derive conflict clause).
      analyze_conflict(my_m->conflicting_clause,my_m->decision_level);

      if(my_m->assertion_level==0){
	//UNSAT!
	result = 0;
	break;
      }
      
      //backtrack to the assertion level (erase upto assertion level+1)
      backtrack((my_m->assertion_level)+1);
      //assert the conflict clause
      res = assert_conflict_clause();
      //at this point of the program, we are done with the assertion (may have resulted in success or another conflict)
    }//end while conflict
      
    //at this point, we do not have a contradiction
    //in the current state.
      
  }//end while not time to restart or solution found
    
  //at this point, result is either 0 or 1.
  return result;

}//end function solve
