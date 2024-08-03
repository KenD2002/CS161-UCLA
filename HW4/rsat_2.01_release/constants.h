//This file contains constants used in the program

// A line must contain at most MAX_LINE_LEN-2 chars.
#define MAX_LINE_LEN 100000 //used for reading input file
// Actually, a clause must contain at most MAX_CLAUSE_LEN-1 literals.
#define MAX_CLAUSE_LEN 1025
#define KB 1024
#define MB 1048576
#define GB 1073741824
#define FIRST_RESTART 100   //the number of conflicts to restart for the first time
#define INITIAL_RESTART_INCR 100 //how many backtracks to increment by
#define RESTART_INCR_INCR 0 //add to the restart_incr by this amount each time
#define MAX_LEARNED_CLAUSES_MULTIPLIER 1.5 //multipler for the maximum number of learned clauses allowed
#define CLAUSE_SCORE_INC_FACTOR 1.001001001001001001001001001001 //based on minisat (1/0.999)
#define NEXT_SIMPLIFY_INCREMENT 0 
#define SCORE_INC_PARAM 0.95  // 1/SCORE_INC_PARAM is the multiplier for score_inc.
#define SCORE_LIMIT 1e100     //the maximum score 
#define CLAUSE_SCORE_LIMIT 1e20  //the maximum clause score
#define SCORE_DIVIDER 1e-100  //must == 1/score_limit
#define CLAUSE_SCORE_DIVIDER 1e-20 //must == 1/clause_score_limit
#define INIT_RANDOM_SEED 91648253 //a random seed
#define CONSERVATIVE_KB_REDUCTION_FACTOR 0.5
#define VC_THRESHOLD 100000
#define LUBY_UNIT 512
#define INIT_ON_TH 100
#define INIT_ON_TH_INC 0
#define INIT_OFF_TH 400
#define INIT_OFF_TH_INC 0
