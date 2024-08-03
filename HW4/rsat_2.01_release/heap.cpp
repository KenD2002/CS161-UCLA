/*
 * heap.cpp
 * (based on MiniSat's Heap.C)
 * This file contains functions related to the implementation
 * of the variable heap for ordering variables.
 * 
 * The following functions are in this file:
 * - gt (comparison function)
 * - percolate_up
 * - percolate_down
 * - init_heap
 * - insert
 * - increase
 * - decrease
 * - get_min_element
 * - empty
 * - in_heap
 * - update
 * - update2
 * - undo
 * - dequeue
 * - increment_literal_score
 * - rescale_variable_scores
 * - increment_clause_score
 * - rescale_clause_scores
 * - free_heap
 * - reset_heap
 *
 * (printing and debuggin)
 * - check_heap_property
 * - print_indices
 * - print_order
 * 
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "constants.h"
#include "flags.h"
#include "structures.h"

extern my_manager* my_m;

/*
 * Return 1 iff the score of v1 is greater than the score of v2
 *
 */
inline char gt(my_var v1,my_var v2)
{
  double s1 = my_m->score[v1];
  double s2 = my_m->score[v2];
  if(s1>s2){return 1;}

  return 0;
}

/*
 * Percolate node i up the heap until it reaches its appropriate position.
 *
 */
inline void percolate_up(heap* h,int i)
{
  my_var* order = h->order;
  int* indices = h->indices;
  my_var v = order[i];
  int parent_index = parent(i);
  //while v's score is still greater than that of its parent
  //i is the order index of the current position of the thing we are percolating

  while(parent_index!=0 && gt(v,order[parent_index])){
    int ind = order[parent_index];
    order[i] = ind;

    indices[ind] = i;
    i = parent_index;          //i moves up
    parent_index = parent(i);  //parent = next parent

  }//end while

  order[i] = v;
  indices[v] = i;
}

/*
 * Percolate node i down the heap into its appropriate position.
 *
 */
inline void percolate_down(heap* h,int i)
{
  my_var* order = h->order;
  int* indices = h->indices;
  my_var v = order[i];  
  int h_size = h->size;

  //until we run out of heap elements
  while(left(i) <= h_size){
    int left_index = left(i);
    int right_index = right(i);

    int bigger_child = ((right_index<=h->size && gt(order[right_index],order[left_index])) ? right_index:left_index);    
    
    if(!gt(order[bigger_child],v)){
      //found the place
      break;
    }

    order[i] = order[bigger_child];
    indices[order[i]] = i;
    i = bigger_child;
  }//end while

  order[i] = v;
  indices[v] = i;
}

/*
 * Initialize heap h by allocating space for all n variables.
 *
 * Initially, set size to 0 as there is nothing in the heap.
 */
void init_heap(heap* h,int n)
{
  h->order = (my_var*)calloc(n+1,sizeof(my_var));  //+1 because order[0] is not used
  h->indices = (int*)calloc(n+1,sizeof(int));
  h->size = 0;
}

/* 
 * Put variable v in the heap (for the first time) based on v's score.
 * 
 */
void insert(heap* h,my_var v)
{  
  int position = (++h->size);
  
  h->indices[v] = position; //put l in the last position in the heap
  h->order[position] = v;
  percolate_up(h,position);
}

/*
 * Get the variable with index v to the right position
 * Assume that the right position of v is above (or equal to) its current position.
 *
 */
void increase(heap* h,my_var v)
{
  percolate_up(h,h->indices[v]);
}

/*
 * Get the variable with index v to the right position.
 * Assume that the right position of v is below (or equal to) its current position.
 *
 */
void decrease(heap* h,my_var v)
{
  percolate_down(h,h->indices[v]);
}

/*
 * Return the index of the variable with highest score in the heap.
 * Also remove that variable from the heap.
 *
 */
my_var get_min_element(heap* h) 
{
  my_var r = h->order[1];   //min element is always kept in [1].
  h->order[1] = h->order[h->size];  //replace min with the last element to keep the heap's shape correct.
  h->size--;                        //decrement the heap's size.
  h->indices[h->order[1]] = 1;
  h->indices[r] = 0;             //r is now out of the heap. Set indices[r] to 0 to reflect that.
  if(h->size > 1){
    percolate_down(h,1);            //adjust the position of the top element
  }
  
  return r;
}

/*
 * Return 1 iff there is currently no element in the heap.
 *
 */
char empty(heap* h)
{
  return h->size==0;
}

/*
 * Return 1 iff variable v is currently in the heap.
 *
 */
char in_heap(heap* h,my_var v)
{
  return h->indices[v]!=0;
}

/*
 * Update the position of variable with index v in the heap.
 * Assume that its correct position is above (or equal to) its current position.
 * 
 */
void update(heap* h,my_var v)
{
  if(in_heap(h,v)){
    increase(h,v);
  }
}

/*
 * Update the position of variable with index v in the heap.
 * Assume that its correct position is below (or equal to) its current position.
 * 
 */
void update2(heap* h,my_var v)
{
  if(in_heap(h,v)){
    decrease(h,v);
  }
}

/*
 * Essentially put the variable v back in the heap (assuming that we has a space for it).
 *
 */
void undo(heap* h,my_var v)
{
  if(!in_heap(h,v)){
    insert(h,v);
  }
}

/*
 * Dequeue a variable from the implication queue (which is really just a heap of variable).
 *
 */
my_var dequeue(implication_queue* h)
{
  while(!empty(h)){
    my_var next = get_min_element(h);   //this takes care of restructuring heap
    return next;
  }//end while

  //no more free variable
  return 0;
}

/*
 * Divide the scores of all variables and score_inc by
 * SCORE_DIVIDIER.
 *
 */
void rescale_variable_scores()
{ 
  int size = my_m->vc;
  double* score = my_m->score;

  for (int i = 1; i <= size; i++){    
    score[i] *= SCORE_DIVIDER;
  }

  my_m->score_inc *= SCORE_DIVIDER;
}

/*
 * Increment the score of variable var(l) by my_m->score_inc.
 * Also update the position of var(l) in the variable heap.
 *
 */
void increment_literal_score(my_lit l)
{
  my_var v = var(l);
  double score = my_m->score_inc;

  my_m->score[v] += score;
  score = my_m->score[v];

  if(score > SCORE_LIMIT){
    rescale_variable_scores();
  }

  update(my_m->var_order_heap,v);

}

/*
 * Divide the scores of all clauses and my_m->clause_score_inc by
 * CLAUSE_SCORE_DIVIDER;
 *
 */
void rescale_clause_scores()
{
  int size = my_m->cur_cdc_count;
  double* scores = my_m->learned_clause_scores;
  for(int i=0;i<size;i++){
    scores[i] *= CLAUSE_SCORE_DIVIDER;
  }
  my_m->clause_score_inc *= CLAUSE_SCORE_DIVIDER;
}

/*
 * Increment the score of the *learned* clause c by
 * my_m->clause_score_inc.
 *
 */
void increment_clause_score(my_clause* c)
{

  if((my_m->learned_clause_scores[c->index] += my_m->clause_score_inc) > CLAUSE_SCORE_LIMIT){
    rescale_clause_scores();
  }

}

/*
 * Debugging utility: 
 * Check the consistency of the heap h
 * Side effect: will exit and print out useful information if inconsistency is detected.
 *
 */
void check_heap_property(heap* h,int var_count)
{
  my_var* order = h->order;
  int* indices = h->indices;
  int size = h->size;
  
  for(int i=1;i<=var_count;i++){
    if(indices[i]!=0){
      if(i!=order[indices[i]]){
	printf("indices array is corrupted at i=%d\n",i);
	print_indices(h,var_count);
	exit(0);
      }
    }
  }//end for i

  //check to make sure the ordering of node (wrt its parent) is correct.
  for(int i=2;i<size;i++){
    double cur_score = my_m->score[order[i]];
    double parent_score = my_m->score[order[parent(i)]];

    if(cur_score>parent_score){
      printf("heap order is corrupted at i=%d | cur_score = %.3f , parent's score = %.3f\n",i,cur_score,parent_score);
      print_order(h);
      exit(0);
    }
  }
}

/*
 * Print the indices array of the heap.
 *
 */
void print_indices(heap* h,int var_count)
{
  printf("Indices Array:\n");
  for(int i=1;i<=var_count;i++){
    printf("[%d-->%d(%d)] ",i,h->indices[i],h->order[h->indices[i]]);
  }

  printf("\n\n");
}

/*
 * Print the order array of the heap.
 *
 */
void print_order(heap* h)
{
  printf("\nHeap contains %d variables\n",h->size);
  for(int i=1;i<=h->size;i++){
    printf("[%d|%d] (%.4f)\n",i,h->order[i],my_m->score[h->order[i]]);
  }
  
  printf("\n\n");
}

/*
 * Free memory related to the heap h.
 */
void free_heap(heap* h)
{
  free(h->order);
  free(h->indices);
}

/*
 * Reinitialize the heap h.
 *
 */
void reset_heap(heap* h)
{
  int size = my_m->vc;
  for(int i=0;i<=size;i++){
    h->indices[i] = 0;
  }

  h->size = 0;   
}
