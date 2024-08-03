from heapq import heappush, heappop, heapify
import numpy as np

from queue import PriorityQueue

class PathNode:
    def __init__(self, state, parent, cost, evaluation):
        """

        :param state: the current state
        :param parent: the previous node (PathNode)
        :param cost: the cost from the start state to the current state i.e. g(n)
        :param evaluation: the state value f(n) = g(n) + h(n)
        """
        self.state = ()
        row = state.shape[0]
        col = state.shape[1]
        for i in range(row):
            for j in range(col):
                self.state = self.state + (state[i,j],)
        self.state1 = state
        self.parent = parent
        self.cost = cost
        self.evaluation = evaluation

    def __lt__(self, other):
        if self.evaluation < other.evaluation:
            return True
        else:
            return False


def a_star_search(start_state, goal_test, next_states, heuristic):
    """
    :param start_state:
    :param goal_test: a function, return true only when the input is the goal state
    :param next_states: a function, return a list of all successor states
    :param heuristic: a function, return the heuristic function value of the given state
    :return:
    """
    pq = PriorityQueue()
    initial_node = PathNode(start_state, None, 0, heuristic(start_state))
    pq.put(initial_node)
    explored = dict()

    node_generated = 1
    node_expanded = 0

    while pq:
        node = pq.get()
        if goal_test(node.state1):
            return node, node_generated, node_expanded
        old_cost = explored.get(node.state)
        if old_cost is not None and old_cost <= node.cost:
            continue
        explored[node.state] = node.cost
        all_successors = next_states(node.state1)
        node_expanded += 1
        for s in all_successors:
            new_cost = node.cost + 1
            new_node = PathNode(s, node, new_cost, new_cost + heuristic(s))
            node_generated += 1
            pq.put(new_node)

    return None, node_generated, node_expanded





