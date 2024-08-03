# Question 1

def BFS(TREE):
    '''BFS is a function that takes a single argument TREE that represents a tree, 
    and returns a tuple of leaf nodes in the order they are visited by left-to-right 
    breadth-first search.
    
    This function uses a queue to realize FIFO, which allows iteration through each
    node of the same level before moving on to the next level.'''
    leaves = []
    if(type(TREE) != tuple):
        leaves.append(TREE)
        return tuple(leaves)
    subtree_queue = [TREE]
    while(len(subtree_queue) != 0):
        subtree = subtree_queue.pop(0)
        for elem in subtree:
            if(type(elem) != tuple):
                leaves.append(elem)
            else:
                subtree_queue.append(elem)
    return tuple(leaves)


print("q1 test")

print(BFS("ROOT"))

print(BFS(((("L", "E"), "F"), "T")))

print(BFS(("R", ("I", ("G", ("H", "T"))))))

print(BFS((("A", ("B",)), ("C",), "D")))

print(BFS(("T", ("H", "R", "E"), "E")))

print(BFS(("A", (("C", (("E",), "D")), "B"))))



# Question 2

def DFS(TREE):
    '''DFS is a function that takes a single argument TREE that represents a tree,
    and returns a tuple of leaf nodes in the order they are visited by left-to-right
    depth-first search.
    
    This function uses a stack to realize LIFO, which allows iteration through all the
    children of a node before moving on to the next node.'''
    leaves = []
    subtree_stack = [TREE]
    while(len(subtree_stack) != 0):
        subtree = subtree_stack.pop()
        if(type(subtree) != tuple):
            leaves.append(subtree)
        else:
            subtree_stack.extend(reversed(subtree))
    return tuple(leaves)

print("Question 2 test")

print(DFS("ROOT"))

print(DFS(((("L", "E"), "F"), "T")))

print(DFS(("R", ("I", ("G", ("H", "T"))))))

print(DFS((("A", ("B",)), ("C",), "D")))

print(DFS(("T", ("H", "R", "E"), "E")))

print(DFS(("A", (("C", (("E",), "D")), "B"))))



# Question 3

def DFID_at_depth(TREE, depth):
    '''DFID_at_depth is an auxiliary function for DFID, which takes two arguments, a tuple
    TREE representing a tree and an integer depth represent the maximum depth it can reach.
      
    It uses recursion at each non-leaf node to get the final result and concatenate them.'''
    leaves = []
    if depth < 0:
        return leaves
    if(type(TREE) != tuple):
        return [TREE]
    for subtree in reversed(TREE):
        leaves.extend(DFID_at_depth(subtree, depth - 1))
    return leaves

def DFID(TREE, D):
    '''DFID is a function that takes two arguments, a tuple TREE representing a tree and 
    an integer D representing the depth of TREE, and returns a tuple of leaf nodes in the
    order they are visited by a right-to-left depth-first iterative-deepening search.
    
    It concatenates the result of performing DFS at each depth.'''
    leaves = []
    for depth in range(D + 1):
        leaves.extend(DFID_at_depth(TREE, depth))
    return tuple(leaves)


print("Question 3 test")

print(DFID("ROOT", 0))

print(DFID(((("L", "E"), "F"), "T"), 3))

print(DFID(("R", ("I", ("G", ("H", "T")))), 4))

print(DFID((("A", ("B",)), ("C",), "D"), 3))

print(DFID(("T", ("H", "R", "E"), "E"), 2))

print(DFID(("A", (("C", (("E",), "D")), "B")), 5))



# Question 4

# These functions implement a depth-first solver for the homer-baby-dog-poison
# problem. In this implementation, a state is represented by a single tuple
# (homer, baby, dog, poison), where each variable is True if the respective entity is
# on the west side of the river, and False if it is on the east side.
# Thus, the initial state for this problem is (False False False False) (everybody
# is on the east side) and the goal state is (True True True True).

# The main entry point for this solver is the function DFS_SOL, which is called
# with (a) the state to search from and (b) the path to this state. It returns
# the complete path from the initial state xto the goal state: this path is a
# list of intermediate problem states. The first element of the path is the
# initial state and the last element is the goal state. Each intermediate state
# is the state that results from applying the appropriate operator to the
# preceding state. If there is no solution, DFS_SOL returns [].
# To call DFS_SOL to solve the original problem, one would call
# DFS_SOL((False, False, False, False), [])
# However, it should be possible to call DFS_SOL with any intermediate state (S)
# and the path from the initial state to S (PATH).

# First, we define the helper functions of DFS_SOL.

# FINAL_STATE takes a single argument S, the current state, and returns True if it
# is the goal state (True, True, True, True) and False otherwise.
def FINAL_STATE(S):
    return S == (True, True, True, True)


# NEXT_STATE returns the state that results from applying an operator to the
# current state. It takes two arguments: the current state (S), and which entity
# to move (A, equal to "h" for homer only, "b" for homer with baby, "d" for homer
# with dog, and "p" for homer with poison).
# It returns a list containing the state that results from that move.
# If applying this operator results in an invalid state (because the dog and baby,
# or poisoin and baby are left unsupervised on one side of the river), or when the
# action is impossible (homer is not on the same side as the entity) it returns [].
# NOTE that NEXT_STATE returns a list containing the successor state (which is
# itself a tuple)# the return should look something like [(False, False, True, True)].
def NEXT_STATE(S, A):
    result = list(S)

    invalid_results = [(False, True, True, False),
                       (True, False, False, True),
                       (False, True, False, True),
                       (True, False, True, False)]
# (homer, baby, dog, poison)

    if(A == "h"):
        result[0] = not S[0]
    elif(A == "b" and S[0] == S[1]):
        result[0] = not S[0]
        result[1] = not S[1]
    elif(A == "d" and S[0] == S[2]):
        result[0] = not S[0]
        result[2] = not S[2]
    elif(A == "p" and S[0] == S[3]):
        result[0] = not S[0]
        result[3] = not S[3]
    else:
        return []

    if tuple(result) in invalid_results:
        return []
    
    return [tuple(result)]


# SUCC_FN returns all of the possible legal successor states to the current
# state. It takes a single argument (S), which encodes the current state, and
# returns a list of each state that can be reached by applying legal operators
# to the current state.
def SUCC_FN(S):
    next_states = []
    next_states.extend(NEXT_STATE(S, "h"))
    next_states.extend(NEXT_STATE(S, "b"))
    next_states.extend(NEXT_STATE(S, "d"))
    next_states.extend(NEXT_STATE(S, "p"))
    return next_states


# ON_PATH checks whether the current state is on the stack of states visited by
# this depth-first search. It takes two arguments: the current state (S) and the
# stack of states visited by DFS (STATES). It returns True if S is a member of
# STATES and False otherwise.
def ON_PATH(S, STATES):
    return S in STATES


# MULT_DFS is a helper function for DFS_SOL. It takes two arguments: a list of
# states from the initial state to the current state (PATH), and the legal
# successor states to the last, current state in the PATH (STATES). PATH is a
# first-in first-out list of states# that is, the first element is the initial
# state for the current search and the last element is the most recent state
# explored. MULT_DFS does a depth-first search on each element of STATES in
# turn. If any of those searches reaches the final state, MULT_DFS returns the
# complete path from the initial state to the goal state. Otherwise, it returns
# [].
def MULT_DFS(STATES, PATH):
    for next_state in SUCC_FN(STATES):
        if next_state not in PATH:
            new_path = DFS_SOL(next_state, PATH + [STATES])
            if new_path:
                return new_path
    return []


# DFS_SOL does a depth first search from a given state to the goal state. It
# takes two arguments: a state (S) and the path from the initial state to S
# (PATH). If S is the initial state in our search, PATH is set to []. DFS_SOL
# performs a depth-first search starting at the given state. It returns the path
# from the initial state to the goal state, if any, or [] otherwise. DFS_SOL is
# responsible for checking if S is already the goal state, as well as for
# ensuring that the depth-first search does not revisit a node already on the
# search path (i.e., S is not on PATH).
def DFS_SOL(S, PATH):
    if FINAL_STATE(S):
        return PATH + [S]
    if ON_PATH(S, PATH):
        return []
    return MULT_DFS(S, PATH)
    


print("Question 4 test")

initial_state = (False, False, False, False)
print(DFS_SOL(initial_state, []))
