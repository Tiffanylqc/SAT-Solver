import random
import time
import copy

#####################################################
#####################################################
# Please enter the number of hours you spent on this
# assignment here
num_hours_i_spent_on_this_assignment = 20
#####################################################
#####################################################

#####################################################
#####################################################
# Give one short piece of feedback about the course so far. What
# have you found most interesting? Is there a topic that you had trouble
# understanding? Are there any changes that could improve the value of the
# course to you? (We will anonymize these before reading them.)
# Now I feel that sometimes in class, I cannot catch up with the topics in class
# and I need to go over the book before I can totally understand it. But in Thursday's in
# class question, we are supposed to apply what is taught right on that day. So maybe you can inform us of the next
# topic in the previous class for me to preview the topics :)
#####################################################
#####################################################


# A clause consists of a set of symbols, each of which is negated
# or not. A clause where
# clause.symbols = {"a": 1, "b": -1, "c": 1}
# corresponds to the statement: a OR (NOT b) OR c .
class Clause:
    def __init__(self):
        pass

    def from_str(self, s):
        s = s.split()
        self.symbols = {}
        for token in s:
            if token[0] == "-":
                sign = -1
                symbol = token[1:]
            else:
                sign = 1
                symbol = token
            self.symbols[symbol] = sign

    def __str__(self):
        tokens = []
        for symbol,sign in self.symbols.items():
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            tokens.append(token)
        return " ".join(tokens)

# A SAT instance consists of a set of CNF clauses. All clauses
# must be satisfied in order for the SAT instance to be satisfied.
class SatInstance:
    def __init__(self):
        pass

    def from_str(self, s):
        self.symbols = set()
        self.clauses = []
        for line in s.splitlines():
            clause = Clause()
            clause.from_str(line)
            self.clauses.append(clause)
            for symbol in clause.symbols:
                self.symbols.add(symbol)
        self.symbols = sorted(self.symbols)

    def __str__(self):
        s = ""
        for clause in self.clauses:
            s += str(clause)
            s += "\n"
        return s

    # Takes as input an assignment to symbols and returns True or
    # False depending on whether the instance is satisfied.
    # Input:
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    # Output: True or False
    def is_satisfied(self, assignment):
        ###########################################
        # Start your code

        #first checck whether every symbol is assigned
        for symbol in self.symbols:
            if symbol not in assignment:
                return False

        #if all assigned, then check whether each clause is satisfied
        for clause in self.clauses:
            clause_value = False
            for clause_symbol in clause.symbols:
                if assignment[clause_symbol]*clause.symbols[clause_symbol] == 1 :
                    clause_value = True
                    break

            #In one clause, no literals is true, so return false
            if clause_value == False:
                return False

        # every clause is true
        return True
        # End your code
        ###########################################

    # Take as input an assignment to symbols
    # If for assigned symbols, some clause is false, then return true
    # Input:
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    #  Output: True or False
    def exist_not_satisfied(self, assignment):

        for clause in self.clauses:
            flag = 0
            for clause_symbol in clause.symbols:
                # if not all symbols in this clause is assigned, go on check next clause
                if clause_symbol not in assignment:
                    flag = 1
                    break

            # if all symbols in this clause are assigned
            if flag == 0:
                clause_value = False
                for clause_symbol in clause.symbols:
                    # clause is true
                    if assignment[clause_symbol]*clause.symbols[clause_symbol] == 1:
                        clause_value = True
                        break

                if clause_value == False:
                    return True

        return False

    # Find unassigned pure symbol
    # Input
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    # Output:
    #   If unassigned pure symbol exists, return [symbol,sign] as tuple
    #   Otherwise, return [-1,-1]
    def find_pure_symbol(self, assignment):
        undetermined_clauses=[]
        for clause in self.clauses:
            flag = 0
            for clause_symbol in clause.symbols:
                if clause_symbol in assignment:
                    # clause is already true for partial assignment
                    if assignment[clause_symbol]*clause.symbols[clause_symbol] == 1:
                        flag = 1
                        break

            if flag == 0:
                undetermined_clauses.append(clause)

        # negated or nonnegated value for unassigned symbols
        symbol_value={}

        for clause in undetermined_clauses:
            for clause_symbol in clause.symbols:
                if clause_symbol not in assignment:
                    # if unassigned symbol is negated, store -1, otherwise store 1 in symbol_value
                    if clause_symbol not in symbol_value:
                        symbol_value[clause_symbol] = clause.symbols[clause_symbol]
                    # if unassigned symbol is not pure symbol(negated value and nonnegated value both appear), mark symbol_value as 0
                    elif symbol_value[clause_symbol] != clause.symbols[clause_symbol]:
                        symbol_value[clause_symbol] = 0
        # find and return one pure symbol
        for symbol in symbol_value:
            if symbol_value[symbol] != 0:
                return [ symbol,symbol_value[symbol] ]

        # no pure_symbol
        return [-1,-1]

    # Find unit clause
    # Input
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    # Output:
    #   If unit clause exists, return the literal [symbol,sign] as tuple
    #   Otherwise, return [-1,-1]
    def find_unit_clause(self, assignment):

        # find clause with only one literal which is unassigned
        for clause in self.clauses:
            if len(clause.symbols)==1:
                symbol = clause.symbols.keys()[0]
                if symbol not in assignment:
                    return [ symbol, clause.symbols[symbol] ]

        # find clause with all literals assigned false except one is unassigned
        for clause in self.clauses:
            unit_clause=[]
            unassigned_cnt = 0
            flag = 0
            for clause_symbol in clause.symbols:
                if clause_symbol not in assignment and unassigned_cnt == 0:
                    unassigned_cnt += 1
                    unit_clause.append(clause_symbol)
                    unit_clause.append(clause.symbols[clause_symbol])
                elif clause_symbol not in assignment and unassigned_cnt != 0:
                    unassigned_cnt += 1
                    break
                elif assignment[clause_symbol]*clause.symbols[clause_symbol] == 1:
                    flag = 1
                    break

            if unassigned_cnt==1 and flag==0:
                return unit_clause

        # no unit clause
        return [-1,-1]

    # Get first unassigned symbol
    # Input
    # - assignment: Dictionary of the format {symbol: sign}, where sign
    #       is either 1 or -1.
    # Output:
    #    unassigned symbol
    def first_unassigned_symbol(self, assignment):
         for symbol in self.symbols:
             if symbol not in assignment:
                 return symbol

         return -1

assignment_solution={}
# Find correct assignment to SatInstance using DPLL with backtracking and some heuristics
# Input:
#  - instance: SAT instance
#  - assignment: Dictionary of the format {symbol: sign}, where sign
#       is either 1 or -1.
# Output:
#   True or false
def dpllsolver(instance):
    global assignment_solution

    if instance.is_satisfied(assignment_solution):
        return True
    if instance.exist_not_satisfied(assignment_solution):
        return False

    [symbol,value] = instance.find_pure_symbol(assignment_solution)
    if symbol!=-1:
        assignment_solution.update({symbol: value})
        return dpllsolver(instance)

    [symbol,value] = instance.find_unit_clause(assignment_solution)
    if symbol!=-1:
        assignment_solution.update({symbol: value})
        return dpllsolver(instance)

    symbol = instance.first_unassigned_symbol(assignment_solution)
    original_assignment={}
    for (i,j) in assignment_solution.items():
        original_assignment[i] = j

    assignment_solution.update({symbol: 1})
    if dpllsolver(instance)==True:
        return True
    else:
        assignment_solution = original_assignment
        assignment_solution.update({symbol: -1})
        return dpllsolver(instance)


# Finds a satisfying assignment to a SAT instance,
# using the DPLL algorithm.
# Input: SAT instance
# - assignment: Dictionary of the format {symbol: sign}, where sign
#       is either 1 or -1.
def solve_dpll(instance):
    ###########################################
    # Start your code
    global assignment_solution
    assignment_solution={}

    if dpllsolver(instance) == True:
        return assignment_solution

    else:
        print("Not satisfiable")
        return {}
    # End your code
    ###########################################

with open("big_instances.txt", "r") as input_file:
     instance_strs = input_file.read()

instance_strs = instance_strs.split("\n\n")

with open("big_assignments.txt", "w") as output_file:
    for instance_str in instance_strs:
        instance = SatInstance()
        instance.from_str(instance_str)
        assignment = solve_dpll(instance)
        for symbol_index, (symbol,sign) in enumerate(assignment.items()):
            if symbol_index != 0:
                output_file.write(" ")
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            output_file.write(token)
        output_file.write("\n")
















