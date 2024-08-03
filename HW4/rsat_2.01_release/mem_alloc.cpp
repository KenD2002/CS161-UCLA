/*
 * mem_alloc.cpp: This file contains memory allocation functions.
 * Every memory alloction of the solver are made through functions in
 * this file (see structures.h).
 * 
 * The following functions are in this file:
 * - my_malloc
 * - my_calloc
 *
 *
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void* my_malloc(size_t size)
{
  void* ans = malloc(size);

  if(ans==NULL){
    printf("c Insufficient memory in malloc\n");
    printf("s UNKNOWN\n");
    exit(0);
  }
  return ans;
}

void* my_calloc(size_t num,size_t size)
{  
  void* ans = calloc(num,size);
  
  if(ans==NULL){
    printf("c Insufficient memory in calloc\n");
    printf("s UNKNOWN\n");
    exit(0);
  }
  return ans;
}
