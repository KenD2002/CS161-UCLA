/*
 *
 * main.cpp: This file contains the "main" function of the solver.
 * It also contains functions related to command line argument parsing,
 * signal handling, and help message printing.
 *
 * Note, however, that the main solving function, 'solve', is in solver.cpp.
 * This function is called by 'main'.
 *
 * The following functions are in this file:
 * - main 
 * - parse_options
 * - print_usage
 * - print_options
 * - SIGINT_handler
 * - SIGSEGV_handler
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <signal.h>
#include <time.h>

#include "flags.h"
#include "structures.h"
#include "constants.h"

my_manager* my_m;
char print_mode=0;
char verbose=0;

#if(TIME_OUT)
double time_out;  //initialized in parse_options
#endif

//for integration with SatELite
FILE* res = NULL;

/*
 * A signal handling function.
 * For handling user interuption (Ctrl+c).
 * Print out execution stats and exit.
 *
 */
void SIGINT_handler(int signum) 
{
  print_progress();
  print_progress_footer();  
  rprintf("\n");
  rprintf("\n");
  rprintf("INTERRUPTED\n");
  print_stats();  
  rprintf("Time used: %fs",get_cpu_time());

  exit(0); 
}

/*
 * A signal handling function. 
 * For handling segmentation fault.
 * 
 * Print out indicator message and exit.
 */
void SIGSEGV_handler(int signum) 
{
  print_progress();
  print_progress_footer();  
  rprintf("\n");
  rprintf("\n");
  rprintf("SEGMENTATION FAULT\n");
  printf("s UNKNOWN\n");
  rprintf("\n");
  print_stats();
  exit(3); 
}

/*
 * Print options for RSat.
 * 
 */
void print_options()
{
  printf("RSat 2.01 options:\n");
  printf("\n");
  printf(" -q %9s\tquiet. Do not print out the answer line. Suppress -s.\n","");
  printf(" -s %9s\tsolution. Print out solution if one is found.\n","");
  printf(" -t %9s\ttime-out. Stop and return UNKNOWN after <timeout> seconds.\n","<timeout>");
  printf(" -v %9s\tverbose. Print out useful information during execution.\n","");
  printf("\n");
  printf("Example:\n");
  printf("\t./rsat problem.cnf -s -t 100 -v\n");
  printf("Report bugs to <rsat@cs.ucla.edu>.\n");
}

/*
 * Print usage for RSat.
 *
 */
void print_usage()
{
  printf("Usage: rsat <cnf-file-name> [options]\n");
  printf("Solve the SAT problem specified in <cnf-file-name>.\n");
  printf("Example: rsat sat-problem.cnf\n");
  print_options();
}

/*
 * Parse the command line arguments and take the appropriate actions.
 *
 */
void parse_options(int num,char** argv)
{
  //skip the cnf file in argv[0]

  //for each argument
  for(int i=1;i<num;i++){
    char* arg = argv[i];

    //time out flag
    if(!strcmp(arg, "-t")){
      //next arg must be time out value in seconds.
      if(i==num-1){
	printf("Expecting a time-out argument following -t.\n");
	exit(0);
      }
      time_out = atof(argv[++i]);
    }else if(!strcmp(arg, "-r")){
      //result file (for integration with preprocessor)
      
      if(i==num-1){
	printf("Expecting a result filename argument following -r.\n");
	exit(0);
      }
      char* fname = argv[++i];
      res = fopen(fname,"wb");
      
      if(!res){
	rprintf("Error opening result file %s for writing.\n",fname);
      }
    }else if(!strcmp(arg,"-q")){
      //quite flag	  
      /*
       * -q always overwrites -s
       *
       */
      
      //quiet!
      print_mode = 1; 
    }else if(!strcmp(arg,"-s")){
      //print solution flag
      
      //print out solution (if one found)      
      if(!print_mode){
	print_mode = 2;
      }
    }else if(!strcmp(arg,"-v")){
      verbose=1;
    }else if(!strcmp(arg,"-h") || !strcmp(arg,"--help")){
      //help flag
      print_usage();
      exit(0);
    }
    
  }//end for each argument

  if(time_out>0 && print_mode!=1){
    rprintf("Time out set to %.4f seconds\n",time_out);
  }

}

/*
 * The main function of the solver.
 * Here is its rough structure:
 *  - parse options
 *  - read input (read_cnf)
 *  - some initializations
 *  - call the main solving function (solve)
 *  - print out answer line (if required)
 *  - exit with the appropriate code
 *
 */
int main(int argc, char *argv[])
{
  signal(SIGINT,SIGINT_handler);
  signal(SIGSEGV,SIGSEGV_handler);

  my_m = NULL;
      
  if(argc<2){
    print_usage();    
    return 0;
  }
  
  char *cnf_fname = argv[1];
  
  time_out = -1.0;

  //parse command line arguments
  parse_options(argc,argv);

  if(print_mode!=1){
    rprintf("Rsat version %0.2f\n",RSAT_VERSION);
  }
  
  fflush(stdout);
  
  //read the input cnf file!
  read_cnf(cnf_fname);
  
  //at this point, we may have already found an inconsistency.
  //If my_m->ok is 0, then the problem is UNSAT. Otherwise,
  //we finish up initialization.
  if(my_m->ok){
    my_m->ok = finish_up_init_manager();
  }

  //copy the print mode to the manager
  my_m->print_mode = print_mode;
  my_m->verbose = verbose;

  //result is the answer of this SAT problem.
  //0 is UNSAT, 1 is SAT, -1 for UNKNOWN
  char result = 1;
  if(!my_m->ok){
    //trivial case
    //UNSAT
    result = 0;
  }else{

    //call the main solving function only if the problem is not completely trivial
    if(my_m->cc>=1){
      
      result = 1;
      print_progress_header();
      //this is the number of unit implications realized so far during input parsing.
      my_m->base_unit_clause_learned = my_m->assign_top-my_m->assign;
      
      /****************************************************************
       *
       * This is the call to the main solving function (in solver.cpp).
       *
       ****************************************************************/
      //Choose only one of the following calls
      //1) solve()
      //2) solve_recursively()
      //3) count_models()
      
      //Normal RSat
      result = solve(); 

      //Recursive SAT (illustration purpose)
      //result = solve_recursively();

      //Model counting (illustration purpose)
      //This option cannot be used with the preprocessor.
      //long models = count_models();
      //rprintf("# of models = %ld\n",models);
      //result = models>0;
      
      //deal with UNSAT result
      if(result<=0){
	print_progress();
	print_progress_footer();
      }
      
      //erase any assignment at the top level
      backtrack(1);

#if(VERIFY_SOLUTION)
      if(status > 0) {
	if (verify_solution()) {
	  rprintf("\n");
	  rprintf("Solution Verified\n");
	}
	else {
	  rprintf("\n");
	  rprintf("Incorrect solution!!!\n");
	  exit(0); 
	}
      }
#endif//endif verify solution
      
    }//end if cc>1
  }//end if else !ok
  
  /************************
   * At this point, 
   * solving is done.
   * Either we have an answer
   * or we time-out'd.
   * Process the result.
   ************************/

  //print out the appropriate answer line
  if (result>0) {
    //SATISFIABLE

    if(print_mode==0 || print_mode==2){
      rprintf("\n");
      rprintf("\n");
      printf("s SATISFIABLE\n");      
    }else{
      
      //print result to file so that the preprocessor can extend it to a full solution.
      if(res!=NULL){
	fprintf(res,"SAT\n");
	int size = my_m->vc;
	
	my_lit* cur = my_m->assign;
	for(int i=0;i<size;i++){
	  fprintf(res,"%s%d",(i==0?"":" "),lit_index(cur[i]));
	}
	fprintf(res," 0\n");
      }
    }

  }else if(result<0){
    //TIMEOUT
    //in the case of timeout, ALWAYS print out solution!
    //because rsat.sh will not call SatElite.
    rprintf("\n");
    rprintf("\n");
    printf("s UNKNOWN\n");        
  }else{
    //UNSAT
    if(print_mode==0 || print_mode==2){
      rprintf("\n");
      rprintf("\n");
      printf("s UNSATISFIABLE\n");
    }else{
    
      if(res!=NULL){ 
	fprintf(res,"UNSAT\n"); 
      }
    }

    if(my_m->conflict_clause!=NULL){
      free(my_m->conflict_clause->lits);
      free(my_m->conflict_clause);
    }
  }//end if else result type
  
  //close the result file if opened.
  if(res!=NULL){
    fclose(res);
  }

  print_stats();
  
  //clean up (manager.cpp).
  free_manager();

  rprintf("Running time: %.5f seconds\n",get_cpu_time());

  //exit with the appropriate code (SAT competition)
  if(result>0){
    exit(10);
  }else if(result==0){
    exit(20);
  }else{
    exit(0);
  }

}//end function main
