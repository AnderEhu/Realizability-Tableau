
from asyncio import futures
import copy
import itertools

from collections import deque
import time

from numpy import var

from separated_formula import print_separated_formula, set_separated_formula
from temporal_formula import get_neg_literal, get_variable, is_var_env, neg_literal

class TNF:
    def __init__(self, separated_formulas):
        
        self.separated_formulas = separated_formulas     
 

    def get_tnf(self):
        if self.tnf_formula:
            return self.tnf_formula
        return False
          

    def calculate_tnf(self):
        print("Calculating TNF...")
        self.start = time.time()
        self.tnf_formula = self.tnf()
        self.time = time.time()-self.start
        print("TNF TIME: ", self.time)
        return self.tnf_formula
        

    def __print_tnf(self):
        print("\n=========================== TNF ===========================\n")
        print(print_separated_formula(self.tnf_formula))
        print("\n=========================== TNF ===========================\n")


    def __hold_condition(self, literals_i, literals_j):
        if not literals_j or not literals_i:
            return False
        for literal_i in literals_i:
            neg_literal_i = get_neg_literal(literal_i)
            if neg_literal_i in literals_j:
                return True
        return False

    def __get_common_literals(self, literals_i, literals_j):
        return literals_i.intersection(literals_j)

    def __get_different_literals(self, literals_i, literals_j):
        return literals_i-literals_j, literals_j-literals_i

    def __dnf_literals(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future, all = False):
        if all:
            return self.__dnf_literals_all(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future)
        else:
            return self.__dnf_literals_alternative(d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future)



    def __dnf_literals_all(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future):
        negdj = neg_dj_X | neg_dj_Y
        if negdj == set():
            return False
        l = [False, True]
        negdj_assignment = self.__get_assignment(negdj) 
        assignments = set(itertools.product(l, repeat=len(negdj))) - negdj_assignment 
        res = list()
        for assignment in assignments:
            negdj_list = list(negdj)
            X = d_X | di_X
            Y = d_Y | di_Y
            for i, is_true in enumerate(assignment):
                var_i = get_variable(negdj_list[i])
                if is_true:
                    if is_var_env(var_i):
                        X.add(var_i)
                    else:
                        Y.add(var_i)
                else:
                    neg_literal_i = get_neg_literal(var_i)
                    if is_var_env(var_i):
                        X.add(neg_literal_i)
                    else:
                        Y.add(neg_literal_i)

            res.append(set_separated_formula(X, Y, future))
        return res

    def __dnf_literals_alternative(self, d_X, d_Y, di_X, di_Y, neg_dj_X ,neg_dj_Y, future):
        if neg_dj_X == set() and neg_dj_Y == set():
            return False
        res = list()
    
        for literal in neg_dj_X:
            X = d_X | di_X
            Y = d_Y | di_Y
            X.add(neg_literal(literal))
            res.append(set_separated_formula(X, Y, future))

        for literal in neg_dj_Y:
            X = d_X | di_X
            Y = d_Y | di_Y
            Y.add(neg_literal(literal))
            res.append(set_separated_formula(X, Y, future))

        return res

    def __get_assignment(self, f):
        ass = list()
        for l in f:
            if l[0] == "-":
                ass.append(False)
            else:
                ass.append(True)
        return {tuple(ass)}


    def __apply_join_rule(self, sf1, sf2):
        d_X =  self.__get_common_literals(sf1['X'], sf2['X'])
        d_Y = self.__get_common_literals(sf1['Y'], sf2['Y'])
        d1_X, d2_X = self.__get_different_literals(sf1['X'], sf2['X'])
        d1_Y, d2_Y = self.__get_different_literals(sf1['Y'], sf2['Y'])
        join_futures = self.__join_futures(sf1['Futures'], sf2['Futures'])
        new_join_1 = set_separated_formula(d_X | d1_X | d2_X, d_Y | d1_Y | d2_Y, join_futures)
        new_join_2 = self.__dnf_literals(d_X, d_Y, d1_X, d1_Y, d2_X, d2_Y, sf1['Futures'])
        new_join_3 = self.__dnf_literals(d_X, d_Y, d2_X, d2_Y, d1_X, d1_Y, sf2['Futures'])
        return new_join_1, new_join_2, new_join_3
            
    def __join_futures(self, future1, future2):
        if future1 == [set()] or future2 == [set()]:
            return [set()]
        if future1 == [{"True"}] or future2 == [{"True"}]:
            return [{"True"}]
        join_f = copy.copy(future1)
        for f2 in future2:
            added = False
            for f1 in future1:
                if f1 > f2 and f1 != set() and f2 != set():
                    if f1 in join_f:
                        join_f.remove(f1)
                    join_f.append(f2)
                    added = True
                elif f1 == f2:
                    added = True
                else:
                    continue
            if not added and f2!= set():    
                join_f.append(f2)
        return join_f
    

    def tnf(self):
        formula = copy.deepcopy(self.separated_formulas)
        all_hold_condition = False
        while not all_hold_condition:
            for index_i, separated_formula_i in enumerate(formula):
                changed = False
                for index_j, separated_formula_j in enumerate(formula):
                    if index_i == index_j:
                        continue
                    if not (self.__hold_condition(separated_formula_i['X'], separated_formula_j['X']) or self.__hold_condition(separated_formula_i['Y'], separated_formula_j['Y'])):
                        formula = [v for i, v in enumerate(formula) if i not in {index_i, index_j}]
                        new_sf_1, new_sf_2, new_sf_3 = self.__apply_join_rule(separated_formula_i, separated_formula_j)

                        formula.append(new_sf_1)
                        if new_sf_2:
                            for new_sf_2_i in new_sf_2:
                                formula.append(new_sf_2_i)
                        if new_sf_3:
                            for new_sf_3_i in new_sf_3:
                                formula.append(new_sf_3_i)
                        changed = True
                        break
                if changed:
                    break
            if not changed:
                all_hold_condition = True
        return formula