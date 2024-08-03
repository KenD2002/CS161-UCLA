/*
 * structures.h: This file contains all important defintions.
 * You should study this file first if you want to modify the code
 * of RSat.
 *
 * Below, you will see defintions of data structures,
 * macro definitions, and function prototypes.
 *
 * The main structures are
 * - my_var      [variable]
 * - my_lit      [literal]
 * - my_clause   [clause]
 * - my_manager  [solving manager]
 * 
 */

#ifndef STRUCTURES_DEFINED 
#define STRUCTURES_DEFINED 

#include "flags.h"

//format string for printing large integers
#ifdef _MSC_VER
typedef __int64  int64;
#define i64d "I64d"
#else
typedef long long int64;
#define i64d "lld"
#endif

//all allocation calls are made through these 2 wraping functions (defined in mem_alloc.cpp)
#define calloc my_calloc
#define malloc my_malloc

//type definition for variables and literals
/************************************************************
 * Variables. Variables are often used as indices into arrays.
 * Variables ranges from 1 to # of variables.
 * For example, if the input problem contains 100 variables,
 * the variable indices will range from 1 to 100.
 ************************************************************/
typedef int my_var;   
/************************************************************
 * Literals. The positive literal of the variable v is 
 * represented as (v<<1). The negative literal is (v<<1)|1.
 * There are many macros that can be used to manipulate literals.
 * Please see their definition below (search for 'macros').
 *
 * For example, if l is of type my_lit
 * var(l) is the variable of l (type my_var).
 * lit_index(l) is the integer representation of l (can be
 * printed with %d).
 * neg(l) is the negation of l (type my_lit).
 *
 ************************************************************/
typedef int my_lit;   

//all functions related to heap are in heap.cpp
typedef struct heap_t{
  my_var* order;    //order[i] = variable at heap position i
  int* indices;     //indices[x] = index of variable x in the (heap) order array
  int size;         //current heap size (# items in heap)
} heap;

//type definition for the queue of implications used in bcp
typedef heap implication_queue; 

//a clause contains an index, an array of literals and a size
typedef struct clause_tt{
  
  /*
   * About clause index.
   * Original clauses have negative indices [-1,-2,-3,...].
   * Learned clauses have non-negative indices [0,1,2,...].
   * This is because we keep a few information about learned clauses in arrays.
   * This way, we can simply use indices of learned clauses as array indices.
   * On the other hand, we do not have any array for orignal clauses.
   */
  int index;    //the clause index
  my_lit* lits; //array of literals in this clause
  int size;     //the size of this clause  
} my_clause;

//this is the main data structure for managing various things during the search
//all functions related to initialization of this structure are in manager.cpp
typedef struct manager_tt{

  int vc;    //number of variables in the problem
  int64 cc;  //number of original clauses (after some simplification in read_cnf)
  my_clause** original_clauses;   //array of original clauses
  int original_clauses_array_len; //the capacity of the original_clauses array
  my_clause** learned_clauses;    //array of learned clauses
  int learned_clauses_array_len;  //the capacity of the learned_clauses array
  
  //Levels start at 1 (top level). 0 means that varaible is not yet assigned. 
  int* level;  //array of variables' levels. my_var-indexed.
  my_lit* assign; //array of assignments. This is really the assignment stack.
  my_lit* assign_top; //the top of the assignment stack.
  my_lit** decision_lit; //array of decision literals. Indexed by the level of the decision.
  int decision_lit_size; //the capacity of the decision_lit array.
  my_lit* status;        //array of assignments of variables. my_var-indexed. status[v] is 0 if v is a free variable.
  my_clause** reason;    //array of reasons for each implication. my_var-indexed. Decision variables have NULL reasons.
  double* score;         //array of (vsids) scores of variables. my_var-inded.
  my_clause*** watched;  //array of watched list for all literals. The entry of literal l is at position watched_index(l).
  int* watched_size;     //the size of the watched list of each literal. Indexed by watched_index(l).
  int* watched_len;      //the capacity of the watched list of each literal. Indexed by watched_index(l).

  int decision_level;    //the current decision level
  double restart_conflict_incr; 
  int64 next_restart_conflict; //the number of conflicts the solver has to reach to restart
  int restart;                 //the number of restarts performed by the solver so far
  int stack_offset;            //the offset into the assignment stack (assign). This is used only for enqueuing unit original clauses (see enqueue/process_unit_literal_queue).
  char ok;                     //a flag used for indicating inconsistency during input reading. If ok==0, it means that the instance is trivially unsatisfiable.
  my_clause* conflicting_clause;//the most recent conflicting clause.
  my_clause* conflict_clause;  //the most recent conflict clause.
  int assertion_level;         //the assertion level of the most recent conlict clause.
  int conflict_level;          //the level of the most recent conflict.

  implication_queue* imp;      //the queue of implications used in bcp.

#if(VERIFY_SOLUTION)
  my_lit* solution_stack;
  my_lit* solution_stack_top;
#endif

  char save_progress;          //a flag. Whether to progress saving is ON or OFF.
  my_lit* saved;               //the saved literal array. my_var-indexed. Used for progress saving implementation.
  double* learned_clause_scores; //array of scores for all learned clauses. Indexed by the indices of learned clauses.

  my_lit* cdc;  //a temporary array of literals (for conflict clause). Used in the function derive_conflict_clause.
  int cdc_size; //the capacity of the cdc array.

  int cdc_index; //the next free position in the cdc array.
  
  char* seen;    //a temporary array used in derive_conflict_clause and removable. my_var-indexed.
  my_lit* stack; //a temporary stack used in removable. 
  int stack_size; //the capacity of stack.
  int* save;      //a temporary array used in removable.
  int save_size;  //the capacity of save.
  heap* var_order_heap; //the heap used for variable ordering (see heap.cpp).

  double score_inc;  //the current variable score increment amount.
  double score_inc_factor;  //the factor to increase score_inc by.
  
  int64 decisions;          //the number of decisions made by the solver so far
  int64 conflicts;          //the number of conflicts experienced by the solver so far

  //the following variables are mostly for stats
  int64 cdc_count;          //total number of learned clauses ever learned (some may have been deleted).
  int64 cdl_count;          //total number of literals ever appear in learned clauses.
  int64 cur_cdc_count;      //the current number of learned clauses.
  int64 cur_cdl_count;      //the current number of literals in learned clauses.
  int64 cur_cc;             //the current number of original clauses.
  int64 cur_lit_count;      //the current number of literals in original clauses.
  int64 original_literals_count; //total number of literals in the original instance that still remain
  int64 original_clauses_count;  //total number of clauses in the original instance that still remain
  int max_decision_level;   //the maximum decision level ever reached by the solver  

  int kb_reduction_count;  //number of times we have performed learned clause deletion
  double clause_score_inc; //the current clause score increment amount.
  double max_learned_clauses;  //the maximum number of learned clauses allowed before we need to delete some.
  
  int kb_simplification_count; //number of times we have performed knowledge base simplification.
  int num_conflicts_for_next_simplify; //number of conflicts to perform knowledge base simplification.
  int next_simplify_increment;         //amount to increment num_conflicts_for_next_simplify by.
  char simplify_orig_kb;               //a flag whether to perform (orig.) knowledge base simplication.
  char simplify_learned_kb;            //a flag whether to perform (learned) knowledge base simplication.

  double random_seed;   //a random seed used by the solver

  int luby_unit;     //the number of conflicts used as the unit in our restarting policy calculation.

  //these variables are for the implementation of periodic progress saving.
  //they control when progress saving is turned ON or OFF. See analyze_conflict().
  int on_th;         //how many conflicts to turn progress saving on for
  int on_th_inc;     //increment amount for on_th every time we switch
  int off_th;        //how many conflicts to turn progress saving off for
  int off_th_inc;    //increment amount for off_th every time we switch
  int next_sp_switch;//the next amount of conflicts to swich the state of progress saving
  
  /*
   * Result printing mode:
   * 0: (default) print result line but not solution line
   * 1: print nothing!
   * 2: print result line AND solution line
   */
  char print_mode;
  char verbose;

  //varaibles below are for progres printing (see print_utils.cpp)
  int64 previous_decision_count;
  int64 previous_conflicts;
  int previous_reduce_kb_count;
  int previous_simplify_kb_count;
  int base_unit_clause_learned;
} my_manager;

//Some frequently used macros.
#define sign(l) (l&1)   //sign(l) is 1 if l is a negative literal
#define neg(l)  (l^1)   //compute the negation of literal l
#define lit_index(l) (sign(l)?-(l>>1):l>>1)  //compute the integer representation of literal l
#define var(l) (l>>1)   //the variable of l
#define plit(v) (v<<1)  //the positive literal of v
#define nlit(v) ((v<<1)|1) //the negative literal of v
#define set(l) (status[var(l)]==l) //1 iff l is set to true. *** status must point to my_m->status at the call location.
#define watched_index(l) (2*(var(l)-1)+sign(l)) //the index of literal l in various arrays.
#define lit_from_int(in) (in<0?((-in)<<1)|1:in<<1) //convert integer in into a literal of type my_lit
#define unresolved(l) (status[var(l)]!=neg(l)) //1 iff l is true or free.
#define free_lit(l) (status[var(l)]==0)  //1 iff l is a free literal.
#define resolved(l) (status[var(l)]==neg(l)) //1 iff l is set to false.
#define var_ind(x) (x<0?-x:x)  //essentially abs(x)
#define max(x,y) (x>y?x:y) //max of x and y
#define min(x,y) (x<y?x:y) //min of x and y

//operations for heap
#define left(i) (i*2)
#define right(i) ((i*2)+1)
#define parent(i) (i/2) //this automatically rounds down

//function for printing out a comment line
#define rprintf(format, args...) ( printf("c "), printf(format , ## args), fflush(stdout) )

//function prototypes
void* my_calloc(size_t,size_t);
void* my_malloc(size_t);

//input parsing
void read_cnf(char*);
void enqueue(my_lit);

//core functions
char process_unit_literal_queue();
void add_conflict_clause();
void analyze_conflict(my_clause*,int level);
char set_decision(my_lit);
int get_luby(int i);
char assert_conflict_clause();
int solve();
void backtrack(int);
char bcp(my_lit);

//watched list
void init_watched_literals();
void remove_watched_clause(my_lit,my_clause*);
void add_watched_clause(my_lit,my_clause*);
void declare_watched_literals(my_clause*);

//my_manager
char finish_up_init_manager();
void init_clause(int*,int,int);
void init_manager();
void free_manager();

//printing
void print_progress_header();
void print_progress();
void print_progress_footer();
void print_clause(my_clause*);
void print_stats();
void print_location();
void print_solution();
void print_watched_list(my_lit l);
void print_indices(heap* h,int var_count);
void print_order(heap* h);

//debugging
void check_watched_list(char);
void check_watched_literal_completeness();
void check_sorted_clause_array(my_clause**,double*,int);
void check_assignment_stack();
void check_heap_property(heap* h,int var_count);
void save_solution_to_file();
#if(VERIFY_SOLUTION)
void save_solution();
char verify_solution();
#endif//endif verif solution

//kb management
void remove_clause(my_clause*);
void sort_clauses_by_scores(my_clause***,double**,int);
void simplify_kb();
void simplify_original_kb();
void reduce_kb();

//heap related
void init_heap(heap* h,int n);
my_var get_min_element(heap* h);
char empty(heap* h);
void insert(heap* h,my_var v);
void increase(heap* h,int v);
void update(heap* h,int v);
void undo(heap* h,my_var v);
my_var select_variable();
my_var dequeue(implication_queue* q);
void rescale_variable_scores();
void increment_literal_score(my_lit);
void increment_clause_score(my_clause* c);
void free_heap(heap* h);
void reset_heap(heap*);

//array size manipulation
void double_decision_lit_len();
void double_stack_len();
void double_save_len();
void double_cdc_len();
void half_decision_lit_len();
void double_learned_clauses_array();

//functions for recursive/exhaustive SAT implementation (experimental_code.cpp)
int solve_recursively(); //not used by the normal solver
long count_models();
char at_assertion_level();
char bcp2(my_lit);
char decide(my_lit);
void undo_decide();
char assert_cd_literal();

//time measuring function
#ifdef _MSC_VER
#include <ctime>
static inline double get_cpu_time(void) {
    return (double)clock() / CLOCKS_PER_SEC; }
#else
#include <sys/time.h>
#include <sys/resource.h>
static inline double get_cpu_time(void) {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif

#endif//endif ifndef (topmost)
