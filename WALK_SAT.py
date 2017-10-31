import random
import time
import copy

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
        for clause in self.clauses:
            clause_value = False
            for clause_symbol in clause.symbols:
                if assignment[clause_symbol]*clause.symbols[clause_symbol] == 1 :
                    clause_value = True
                    break

            #In one clause, no literals is true, so return false
            if clause_value == False:
                return False

        # every clause is true, CNF is satisfied
        return True
        # End your code
        ###########################################

    # Randomly assign value to symbols
    # Output: Randomly assignment values to symbols
    def random_init_assign(self):
        assignment = {}

        for symbol in self.symbols:
            randnum = random.random()
            if randnum<0.5:
                assignment[symbol] = 1
            else:
                assignment[symbol] = -1

        return assignment

    # Find clauses which are false under assignment, and return one of them randomly
    # Input:
    # - assignment: Dictionary of the format {symbol: sign}, where sign is either 1 or -1.
    # Output: randomly selected clause from clauses that false in P
    def random_false_clause(self,assignment):
        false_clauses=[]
        # find false clauses
        for clause in self.clauses:
            clause_value=False
            for clause_symbol in clause.symbols:
                if assignment[clause_symbol]*clause.symbols[clause_symbol] == 1 :
                    clause_value = True
                    break
            if clause_value == False:
                false_clauses.append(clause)

        false_num=len(false_clauses)
        rand_index=random.randint(0,false_num-1)
        return false_clauses[rand_index]

    # Flip the value of the symbol that maximizes the number of satisfied clauses
    # Input:
    # - assignment: Dictionary of the format {symbol: sign}, where sign is either 1 or -1.
    # Output: the new assignment after flipping the symbol that maximizes the number of satisfied clauses
    def flip_variable(self,assignment):
        # Number of satisfied clauses after flipping each symbol
        satisfied_clause={}

        # find the value of satisfied clauses for each symbol
        for symbol in self.symbols:
            flipped_assignment = copy.deepcopy(assignment)
            flipped_value = assignment[symbol]*(-1)
            flipped_assignment.update({symbol:flipped_value})
            num_of_satisfied=0
            for clause in self.clauses:
                clause_value = False
                for clause_symbol in clause.symbols:
                    if flipped_assignment[clause_symbol] * clause.symbols[clause_symbol] == 1:
                        clause_value = True
                        break
                if clause_value == True:
                    num_of_satisfied += 1
            satisfied_clause[symbol] = num_of_satisfied

        # find the maiximum number of satisfied clauses
        flipped_symbol = max(satisfied_clause, key=satisfied_clause.get)
        flipped_assignment = copy.deepcopy(assignment)
        flipped_value = assignment[flipped_symbol] * (-1)
        flipped_assignment.update({flipped_symbol: flipped_value})

        return flipped_assignment


# Finds a satisfying assignment to a SAT instance,
# using the WALK_SAT algorithm.
# Input: SAT instance
# - assignment: Dictionary of the format {symbol: sign}, where sign
#       is either 1 or -1.
def walk_sat(instance):
    MAX_TRIES=2000
    MAX_CHANGES=2000
    p=0.8
    for i in range(MAX_TRIES):
        rand_assignment=instance.random_init_assign()

        for j in range(MAX_CHANGES):
            if instance.is_satisfied(rand_assignment):
                return rand_assignment
            false_clause=instance.random_false_clause(rand_assignment)

            probability=random.random()
            # with probability p, flip the value of randomly selected symbol in false_clause
            if probability<p :
                flipped_symbol=random.choice(list(false_clause.symbols.keys()))
                flipped_value = rand_assignment[flipped_symbol] * (-1)
                rand_assignment.update({flipped_symbol: flipped_value})
            # Flip the value of the symbol that maximizes the number of satisfied clauses
            else:
                rand_assignment = instance.flip_variable(rand_assignment)

    return {}

with open("bonus_instances.txt", "r") as input_file:
     instance_strs = input_file.read()

instance_strs = instance_strs.split("\n\n")

with open("bonus_instances_sat_inferred_0.8_2000.txt", "w") as output_file:
    for instance_str in instance_strs:
        instance = SatInstance()
        instance.from_str(instance_str)
        assignment = walk_sat(instance)
        for symbol_index, (symbol,sign) in enumerate(assignment.items()):
            if symbol_index != 0:
                output_file.write(" ")
            token = ""
            if sign == -1:
                token += "-"
            token += symbol
            output_file.write(token)
        output_file.write("\n")