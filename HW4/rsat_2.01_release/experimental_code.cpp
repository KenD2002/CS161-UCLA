/*
 * experimental_code.spp: This file is intended to contain
 * experimental functions that have not been permanently integrated into the
 * solver.
 *
 * The reason for this file is to avoid making other files hard to read.
 *
 * Currently, this file does not contain any function.
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

#include <assert.h>  //must be defined after flags.h for NDEBUG to work

extern my_manager* my_m;

/*
 * **This function is for recursive SAT implementation**
 *
 * Returns 1 iff the manager's decision level is equal to
 * its assertion level;
 *
 */
char at_assertion_level()
{
  return my_m->assertion_level==my_m->decision_level;
}

/*
 * **This function is for recursive SAT implementation**
 *
 * Perform unit propagation starting at the assignment of literal l.
 * Return 1 if no conflict arises, otherwise return 0.
 *
 * The only difference between this function and bcp is that this function
 * calls analyze_conflict if a conflict arises.
 */
char bcp2(my_lit l)
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
	
	analyze_conflict(my_m->conflicting_clause,my_m->decision_level);
	
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
}//end function bcp2

/*
 * **This function is for recursive SAT implementation**
 * 
 * Set literal l to true. Set this literal to be the decision literal of the level.
 * Propagate its effects (by calling bcp).
 * Returns 0 iff bcp can derive a conflict.
 * 
 * The only difference between this function and set_decision is that
 * this function calls bcp2 instead of bcp.
 */
char decide(my_lit l) 
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

  return bcp2(l);
}//end function decide

/*
 * **This function is for recursive SAT implementation**
 *
 * Undo the most recent decision level.
 * 
 */
void undo_decide()
{
  backtrack(my_m->decision_level);
}

/*
 * **This function is for recursive SAT implementation**
 *
 * Add the current conflict clause to the knowledge base
 * and apply unit propagation (call bcp) on it.
 * Return 0 iff unit propagation derives a conflict.
 *
 * The only difference between this function and assert_conflict_clause
 * is that this calls bcp2 instead of bcp.
 */
char assert_cd_literal()
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

  return bcp2(fuip);
}//end function assert cd literal

/*
 * A recursive implementation of a SAT solver.
 * See the paper 
 * New Advances in Compiling CNF to Decomposable Negation Normal Form
 * by Adnan Darwiche for more details.
 *
 * 
 * Return 1 iff the SAT instance is satisfiable.
 * Otherwise, return 0.
 * 
 * This function is intended to be somewhat equivalent to solve (in solver.cpp) [except for timeout and restart].
 * 
 * Note that this function is only for illustration purposes. It should not be used for actual SAT solving.
 */
int solve_recursively()
{  
  //pick a variable
  my_var dec_var = select_variable();

  if(dec_var==0){
    return 1;
  }
  
  //pick a phase of the variable
  my_lit l = nlit(dec_var);  
  
  if(decide(l) && solve_recursively()){
    undo_decide();
    return 1;
  }

  undo_decide();
  
  if(at_assertion_level()){
    return assert_cd_literal() && solve_recursively();
  }

  return 0;
}

/*
 * Return the number of models of the current formula
 * (represented by the current state of the manager).
 *
 * This function should be called from main (see main.cpp).
 *
 * Note that this function is only for illustration purposes. 
 * It is not optimized in any way.
 */
long count_models()
{
  my_var dec_var = select_variable();

  if(dec_var==0){
    //a model is found
    return 1;
  }

  //positive case
  long pcount = 0;
  if(decide(plit(dec_var))){
    pcount = count_models();
  }

  undo_decide();

  if(pcount==0){
    if(at_assertion_level() && assert_cd_literal()){
      return count_models(); //try again
    }else{
      return 0; //backtracking
    }
  }//end if pcount==0
  
  //negative case
  long ncount = 0;
  
  if(decide(nlit(dec_var))){
    ncount = count_models();
  }

  undo_decide();

  if(ncount==0){
    if(at_assertion_level() && assert_cd_literal()){
      return count_models(); //try again
    }else{
      return 0; //backtracking
    }
  }//end if ncount==0    
  
  return pcount+ncount;
}
