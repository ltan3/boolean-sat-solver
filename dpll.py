#!/usr/bin/env python3

import csv
import heapq					# only supports min-heaps
import sys
from collections import deque
from pprint import pprint

from branching import Clock, Scores

Last_Clause_Unit_Propagated = None

# constants
class Status:
	UNSAT = -1
	UNRESOLVED = 0
	SAT = 1
	UNIT = 2

# counters
class Ct:
	numAssignedVars = 0
	numSatClauses = 0
	numTotalVars = 0
	numTotalClauses = 0

	def allVarsAssigned():
		return Ct.numAssignedVars == Ct.numTotalVars

	def allClausesSat():
		return Ct.numSatClauses == Ct.numTotalClauses


class Predicate:
	def __init__(self, num):
		self.id = num
		self.value = 0
		self.decisionLevel = 0
		self.clauses = dict()
		self.numClauses = [0, 0, 0]
		# Id of the clause was unit propagated on to cause this variable to be assigned,
		# or None if a guess, or unassigned.
		self.antecedent = None

	def __repr__(self):
		return 'Predicate(id={self.id}, value={self.value}, dl={self.decisionLevel}, a={self.antecedent}, clauses={self.clauses}'.format(self=self)

class Clause:
	def __init__(self, num):
		self.id = num
		self.value = 0
		self.watched = None  # two watched literals tuple
		self.watchable = set()
		self.unwatchable = set()

	def __repr__(self):
		return 'Clause(id={self.id}, value={self.value}, watched={self.watched}, watchable={self.watchable}, unwatchable={self.unwatchable}'.format(self=self)

	def allPreds(self):
		return self.watchable.union(self.unwatchable)

def deleteClauseFromPredicates(preds, clauseID):
	for p in preds:
		if clauseID in preds[p].clauses:
			truth = preds[p].clauses[clauseID]
			preds[p].numClauses[truth] -= 1
			preds[p].numClauses[0] -= 1
			del preds[p].clauses[clauseID]

# Returns two dictionaries {predicate id : predicate object}, {clause id : clause object}
def parse(filename):
	predicates = dict()
	clauses = dict()
	nvars = 0
	nclauses = 0

	with open(filename, newline='') as f:
		reader = csv.reader(f, delimiter=' ')
		clauseID = 1
		for line in reader:
			if not line or line[0] == 'c':
				continue

			elif line[0] == 'p':
				assert(line[1] == 'cnf')
				nvars, nclauses = int(line[2]), int(line[3])
				for i in range(nvars):
					predicates[i+1] = Predicate(i+1)
				# print("There are {} variables and {} clauses in this problem.".format(nvars, nclauses))

			else:
				c = [int(i) for i in line if i != '']
				assert(c[-1] == 0)
				clause = Clause(clauseID)
				addClause = True
				literals = set(c[:-1])
				for l in literals:
					var = abs(l)
					truth = 1 if l > 0 else -1
					if clauseID in predicates[var].clauses and predicates[var].clauses[clauseID] != truth:
						deleteClauseFromPredicates(predicates, clauseID)
						addClause = False
						break
					else:
						predicates[var].clauses[clauseID] = truth
						predicates[var].numClauses[truth] += 1
						predicates[var].numClauses[0] += 1
				if addClause:
					# print("{}: {}".format(clauseID, " ".join(line)))
					assert(len(literals) > 0)
					clause.watchable = {abs(l) for l in literals}
					clause.watched = (abs(list(literals)[0]), abs(list(literals)[-1])) 	# arbitrary
					clauses[clauseID] = clause
					clauseID += 1
				else:
					nclauses -= 1

	assert(clauseID-1 == nclauses)

	Ct.numTotalVars = nvars
	Ct.numTotalClauses = nclauses
	Scores.initialize(predicates)

	return predicates, clauses

def findPureLiterals(preds):  # FIX
	pureLits = []
	for p in preds:
		if preds[p].numClauses[1] == 0:
			pureLits.append((preds[p].id, -1, None))
		elif preds[p].numClauses[-1] == 0:
			pureLits.append((preds[p].id, 1, None))
	return pureLits

def computeTruth(preds, var, c):
	return preds[var].value * preds[var].clauses[c]

def moveWatch(preds, clauses, c, currValue, watchToMove, otherWatch):
	# toRemove = []
	newWatch = watchToMove
	newValue = currValue
	for elt in clauses[c].watchable:
		truth = computeTruth(preds, elt, c)
		# if truth < 0:
		# 	toRemove.append(elt)
		# 	continue
		if elt != otherWatch:
			newWatch = elt
			newValue = truth
			break
	# for e in toRemove:
	# 	clauses[c].watchable.remove(e)
	return newWatch, newValue

# returns (int Status, int unitPredicate)
def satStatus(preds, clauses, c):
	l1, l2 = clauses[c].watched
	v1 = computeTruth(preds, l1, c)
	v2 = computeTruth(preds, l2, c)
	
	# move watches if necessary
	if v1 < 0:
		l1, v1 = moveWatch(preds, clauses, c, v1, l1, l2)
	if v2 < 0:
		l2, v2 = moveWatch(preds, clauses, c, v2, l2, l1)
	clauses[c].watched = (l1,l2)

	# evaluate clause
	if v1 == 1 or v2 == 1:
		return Status.SAT, None
	elif v1 == 0 and v2 == 0 and l1 != l2:
		return Status.UNRESOLVED, None
	elif v1 == 0:
		return Status.UNIT, l1
	elif v2 == 0:
		return Status.UNIT, l2
	else:
		return Status.UNSAT, None

# Looks at all clauses, identifies the clauses that are unit.
# For each unit clause, looks at all variables in the clause to determine which one is unassigned, 
# and its sign in th clause.
# Returns list of pairs [ (variable, sign it sould be assigned to, id of responsible clause) ]
def findUnitClauses(preds, clauses):
	units = []
	unitsFound = set()
	Ct.numSatClauses = 0
	for c in clauses:
		status, p = satStatus(preds, clauses, c)
		if p is not None:
			truth = p * preds[p].clauses[c]
		if status == Status.SAT:
			Ct.numSatClauses += 1
		elif status == Status.UNSAT:
			# print("\tfound units, returning unsat: {}".format(units))
			return units, -1
		elif status == Status.UNIT and truth not in unitsFound:
			# print("derp clause {} pred {}: {}".format(c, p, preds[p].clauses[c]))
			units.append((p, preds[p].clauses[c], c))
			unitsFound.add(truth)
	# print("\tfound units: {}".format(units))
	return units, 1

# Assigns val to var with decision level dLevel, and updates preds and clauses.
# Returns 1 (success) or -1 (unsat)
def assignVal(preds, clauses, dLevel, var, val, antecedent):
	#print("ASSIGNING {} to {} at level {}".format(val, var, dLevel))
	global Last_Clause_Unit_Propagated
	assert(Last_Clause_Unit_Propagated is not None or val == 0 or preds[var].value == 0)  # conflict
	if preds[var].value == 0 and val != 0:  # new assigned variable
		Ct.numAssignedVars += 1
	elif preds[var].value != 0 and val == 0:  # de-assigning variable
		Ct.numAssignedVars -= 1
		if preds[var].value < 0:  # add back into watchable
			for c in preds[var].clauses:
				clauses[c].watchable.add(var)

	# set value and update stuff
	preds[var].value = val
	preds[var].decisionLevel = dLevel
	preds[var].antecedent = antecedent

	for c in preds[var].clauses:  # update watchable
		truth = preds[var].clauses[c] * val  # value to be in clause
		if truth < 0 and var in clauses[c].watchable:
			clauses[c].watchable.remove(var)
			clauses[c].unwatchable.add(var)
		else:
			clauses[c].watchable.add(var)
			if var in clauses[c].unwatchable:
				clauses[c].unwatchable.remove(var)

# Assigns var := val, then performs unit propagation as far as possible.
# Returns 1 (success) or -1 (unsat).
def unitProp(preds, clauses, dLevel, var=0, val=0):
	memory = dict()  # (truth: ant)
	if var != 0:
		assert(val != 0)
		assignVal(preds, clauses, dLevel, var, val, None)
	units, success = findUnitClauses(preds, clauses)
	if success < 0:
		return -1
	while len(units) > 0:
		# print("UNITS: {}".format(units))
		for varU, valU, antecedentU in units:
			assert(valU != 0)
			truth = varU*valU
			if truth*-1 in memory:  # conflict
				global Last_Clause_Unit_Propagated
				Last_Clause_Unit_Propagated = memory[truth*-1]
				assignVal(preds, clauses, dLevel, varU, valU, antecedentU)
				return -1
			memory[truth] = antecedentU
			# print("UPROP: {} for {} at level {}".format(valU, varU, dLevel))
			assignVal(preds, clauses, dLevel, varU, valU, antecedentU)
		units, success = findUnitClauses(preds, clauses)
		if success < 0:
			return -1
	return 1

# Backtrack to when the decision level was dLevel - 1.
def revertChanges(preds, clauses, dLevel):
	assert(dLevel > 0)

	# update decision stack. find last decision literal with level <= dLevel 
	# where you have not yet tried the other assignment
	# var, tried = 0, True
	# while len(dStack) > 0 and (preds[dStack[-1][0]].decisionLevel >= dLevel or tried):
	# 	var, tried = dStack.pop()
	# val = -1*preds[var].value if var > 0 else None

	# reset predicate values
	for p in preds:
		if preds[p].decisionLevel >= dLevel:  # set val to 0 and remove traces
			assignVal(preds, clauses, 0, p, 0, None)

	# update scores heaps
	while len(Scores.resolvedHeap) > 0 and Scores.resolvedHeap[0][0] <= -1*dLevel:
		lit = heapq.heappop(Scores.resolvedHeap)
		heapq.heappush(Scores.unresolvedHeap, (lit[1], lit[2]))

	# return var, val


# Resolve the clause learnedClause with clause newClause, and assigns result to learnedClause.
# learnedClause is a map {variable in c1 : polarity in c1} and newClause a clause ID.
def resolve(predicates, clauses, learnedClause, newClause, dl, nDL=0):
	# There is a unique variable x st. x is in both learnedClause and newClause 
	# but has opposite polarity in each. This tracks what is is (if we've found it).
	# print("RESOLVING AT LEVEL {}".format(dl))
	# opposite = None
	for newPred in clauses[newClause].allPreds():
		newPolarity = predicates[newPred].clauses[newClause] # polarity of newPred in newClause
		# Take the resolution of learnedClause and newClause
		if newPred in learnedClause:
			if learnedClause[newPred] != newPolarity:
				# assert(opposite is None)
				# opposite = newPred
				del learnedClause[newPred]
				if predicates[newPred].decisionLevel == dl:
					nDL -= 1
		else:
			learnedClause[newPred] = newPolarity
			if predicates[newPred].decisionLevel == dl:
				nDL += 1
	return nDL


# Learn a clause from the conflict, and add it.
# Then return the decision level we should backtrack to.
def analyzeConflict(predicates, clauses, dl):
	# Find the unsat clause
	unsatClause = [c for c in clauses if satStatus(predicates, clauses, c)[0] == Status.UNSAT][0]
	# print("unsat clause: {}".format(unsatClause))

	# Analyze graph of antecedents to learn a clause
	# Map { id of variable in new clause : polarity }
	learnedClause = {p : predicates[p].clauses[unsatClause] for p in clauses[unsatClause].allPreds()}
	# print("\tlearning: {}".format(learnedClause))

	# IMMEDIATLY resolve with the clause that was most recently unit implied on
	# todo
	# last_unit_clause = 5 # lol
	global Last_Clause_Unit_Propagated
	lastClause = Last_Clause_Unit_Propagated
	if not lastClause:
		return -1
	# assert(lastClause)
	# resolve(predicates, clauses, learnedClause, lastClause, dl)

	# print("\tlastClause: {}".format(lastClause))
	# print("\tresolve with {}: {}".format(lastClause, {p:predicates[p].clauses[lastClause] for p in clauses[lastClause].allPreds()}))
	resolve(predicates, clauses, learnedClause, lastClause, dl)
	# print("\tlearning: {}".format(learnedClause))


	# Breadth first search
	queue = deque(learnedClause.keys()) 						# breadth first search
	visited = set(learnedClause.keys()) 				# Set of things already visited
	
	# Stop if there is exactly one variable in learned_clause that was assigned at current decision level
	nDL = sum(1 for p in learnedClause if predicates[p].decisionLevel == dl)
	# print("NDL: {}".format(nDL))
	while queue and nDL != 1:
		p = queue.pop()
		antecedent = predicates[p].antecedent
		if predicates[p].decisionLevel == dl and antecedent is not None:
			# print("\tresolve with antecedent {} of {}: {}".format(antecedent, p, {p:predicates[p].clauses[antecedent] for p in clauses[antecedent].allPreds()}))
			nDL = resolve(predicates, clauses, learnedClause, antecedent, dl, nDL)
			# print("\tlearning: {}".format(learnedClause))
			# Update queue
			for newPred in clauses[antecedent].allPreds():
				if newPred not in visited:
					queue.appendleft(newPred)
					visited.add(newPred)

	# print("\tlearned: {}".format(learnedClause))
	# print("\tlearned clause values: {}".format([(p, predicates[p].value, predicates[p].decisionLevel) for p in learnedClause]))
	
	# Create and add clause object
	newID = len(clauses) + 1
	assert(newID not in clauses)
	newClause = Clause(newID)
	for p, polarity in learnedClause.items():
		if predicates[p].value != 0:
			# print("PRED check0: {}".format(predicates[p]))
			predicates[p].clauses[newID] = polarity
			predicates[p].numClauses[polarity] += 1
			predicates[p].numClauses[0] += 1
		newClause.watchable.add(p)

	newClause.watched = (abs(list(newClause.watchable)[0]), abs(list(newClause.watchable)[-1]))
	clauses[newID] = newClause

	# Calculate decision level that we should backtrack to.
	# Decision level we should backtrack to is max dl of variables
	# in new clause besides the current dl.
	dLCandidates = [predicates[p].decisionLevel for p in newClause.allPreds() if predicates[p].decisionLevel < dl]
	# print("dLCandidates: {}".format(dLCandidates))
	newDL = max(dLCandidates) if len(dLCandidates) > 0 else dl - 1
	# print("\tpredicate decision levels: {}".format([predicates[p].decisionLevel for p in newClause.allPreds()]))

	Scores.applyLearningPenalty(predicates, set([p*pol for p, pol in learnedClause.items()]))
	return newDL


# Performs DPLL iteratively.
def dpll(predicates, clauses):
	dLevel = 0
	dStack = deque()					# stack of decision literals
	var, val = -1, None
	branch = True
	preds = predicates

	if unitProp(predicates, clauses, dLevel) < 0:
		# print("******* UNIT PROP failed at dl 0 => UNSAT".format(dLevel))
		return -1

	while not Ct.allVarsAssigned() and not Ct.allClausesSat():
		if branch:
			var, val = Scores.pickBranchingVar(predicates, clauses)
			dLevel += 1
			# print("TRYING {} := {} at level {}".format(var, val, dLevel))
		success = unitProp(predicates, clauses, dLevel, var, val)
		# print("\tnew assignments: {}".format([(p, preds[p].value, preds[p].decisionLevel, preds[p].antecedent) for p in preds if preds[p].value != 0]))
		if success < 0:
			if not branch:
				return -1
			Clock.update()
			if val is not None: 
				Scores.applyConflictPenalty(preds, var*val, dLevel)
			newDLevel = analyzeConflict(predicates, clauses, dLevel)
			if newDLevel < 0:
				return -1
			else:
				# print("BACKTRACK to level {}".format(newDLevel))
				dLevel = newDLevel
				revertChanges(predicates, clauses, newDLevel + 1)
				branch = False
				var, val = 0, None
				# print("\treverted assignments: {}".format([(p, preds[p].value, preds[p].decisionLevel, preds[p].antecedent) for p in preds if preds[p].value != 0]))
		else:
			branch = True
	return 1

if __name__ == '__main__':
	if len(sys.argv) != 2:
		print("Usage: {} [input.cnf]".format(sys.argv[0]))
		sys.exit(1)

	predicates, clauses = parse(sys.argv[1])

	# handle pure literals
	literals = findPureLiterals(predicates)
	for varL,valL,antecedentL in literals:
		assert(valL != 0)
		# print("PURELIT: {} for {}".format(valL, varL))
		assignVal(predicates, clauses, 0, varL, valL, antecedentL)
	# success, _ = dpll(predicates, clauses, 0)
	success = dpll(predicates, clauses)
	if success < 0:
		print("unsat")
	else:
		print("sat")
		for p in predicates:
			if predicates[p].value == 0:  # unassigned bc stopped early
				predicates[p].value = 1
			print('{} '.format(predicates[p].id * predicates[p].value), end='')
		print()
