# Question 1
def PAD(N):
    '''PAD takes a single integer argument N, and returns the Nth Padovan number'''
    if(N >= 3):
        return PAD(N - 2) + PAD(N - 3)
    else:
        return 1

# Question 2
def SUMS(N):
    '''SUMS takes a single numeric argument N, and returns the number of additions.
       In each recursion, p(n) is broken down to p(n-2) and p(n-3) with an addition.'''
    if(N >= 3):
        return 1 + SUMS(N - 2) + SUMS(N - 3)
    else:
        return 0

# Question 3
def ANON(TREE):
    '''ANON takes a single argument TREE that represents a tree, and returns an 
       anonymized tree with the same structure, but where every leaf in the tree 
       is replaced by a question mark.'''
    if(type(TREE) != tuple):
        return "?"
    else:
        TREE_LIST = list(TREE)
        for idx in range(len(TREE)):
            TREE_LIST[idx] = ANON(TREE[idx])
        return tuple(TREE_LIST)

# Question 4
def TREE_HEIGHT(TREE):
    '''TREE_HEIGHT takes a tree TREE in tuples, and returns the height of TREE.'''
    if(type(TREE) != tuple):
        return 0
    else:
        return max(TREE_HEIGHT(sub_tree) for sub_tree in TREE) + 1
    
# Question 5
def TREE_ORDER(TREE):
    '''TREE_ORDER takes one argument TREE that represents an ordered tree, and 
    returns a tuple that represents the postorder traversal of the numbers in TREE.'''
    if(type(TREE) != tuple):
        return tuple([TREE])
    else:
        return TREE_ORDER(TREE[0]) + TREE_ORDER(TREE[2]) + TREE_ORDER(TREE[1])
