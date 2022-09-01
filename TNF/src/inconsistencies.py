
from TemporalFormula.src.temporal_formula import TemporalFormula


class Inconsistencies:

    def __init__(self):
        pass

    @staticmethod
    def are_inconsistent_formulas(formula1: str, formula2: str, strToAb = dict(), simple = False):
        if formula1 == formula2: 
            return False  

        if formula1 == "False" or formula2 == "False" or formula1 == "X[1]False" or formula2 == "X[1]False":
            return True

        formula1_list = TemporalFormula.push_negs(TemporalFormula.get_str_to_ab_in_bica(formula1, strToAb), changeNegAlwaysEventually=True)
        formula2_list = TemporalFormula.push_negs(TemporalFormula.get_str_to_ab_in_bica(formula2, strToAb), changeNegAlwaysEventually=True)


        formula1_literals = TemporalFormula.get_literals(formula1_list)
        formula2_literals = TemporalFormula.get_literals(formula1_list)


        if not formula1_literals.intersection(formula2_literals):
            return False


        if TemporalFormula.is_next(formula1_list[0]):
            formula1_list = TemporalFormula.include_next_to_formula(formula1_list)

        if TemporalFormula.is_next(formula2_list[0]):
            formula2_list = TemporalFormula.include_next_to_formula(formula2_list)

            
        
        if Inconsistencies.is_in_inconsistency_interval(formula1_list, formula2_list):

            if TemporalFormula.is_temp_op(formula1_list[0]):
                formula1_no_first_temp = formula1_list[1]
            else:
                formula1_no_first_temp = formula1_list

            if TemporalFormula.is_temp_op(formula2_list[0]):
                formula2_no_first_temp = formula2_list[1]
            else:
                formula2_no_first_temp = formula2_list
            if formula1_no_first_temp == ['-', formula2_no_first_temp] or formula2_no_first_temp == ['-', formula1_no_first_temp]:
                return True
            if not simple:
                f = ['&', formula1_no_first_temp, formula2_no_first_temp] 
                is_sat_f = TemporalFormula.is_sat(f)
                return not is_sat_f
             
        return False

        
    @staticmethod
    def is_in_inconsistency_interval(future1: list, future2: list):
        future1_limit_inf, future1_limit_sup = TemporalFormula.get_temporal_limits(future1)
        future2_limit_inf, future2_limit_sup = TemporalFormula.get_temporal_limits(future2)
        future_1_interval = [future1_limit_inf, future1_limit_sup]
        future_2_interval = [future2_limit_inf, future2_limit_sup]

        if future1_limit_inf == future2_limit_inf == future1_limit_sup == future2_limit_sup:
            return True
            
        if future1_limit_inf > future2_limit_sup or future2_limit_inf > future1_limit_sup:
            return False
        else:
            intersection_interval = [max(future1_limit_inf, future2_limit_inf), min(future1_limit_sup, future2_limit_sup)]

            if not TemporalFormula.is_eventually(future1[0]) and not TemporalFormula.is_eventually(future2[0]):
                return True
            elif  TemporalFormula.is_always(future1[0]) and future_2_interval == intersection_interval:
                return True
            elif TemporalFormula.is_always(future2[0]) and future_1_interval == intersection_interval:
                return True
            else:
                return False

    @staticmethod
    def is_inconsistent_set(futures: set, inconsistencies = dict(), strToAb = dict()):
        futures_list = list(futures)
        for i in range(0, len(futures_list)):
            future1 = futures_list[i]
            for j in range(i+1, len(futures_list)):
                future2 = futures_list[j]
                if Inconsistencies.is_in_inconsistencies_dict(future1, future2, inconsistencies):
                    return True
                are_inconsistent = Inconsistencies.are_inconsistent_formulas(future1, future2, strToAb)
                if are_inconsistent:
                    Inconsistencies.add_to_inconsistent_dict(future1, future2, inconsistencies)
                    Inconsistencies.add_to_inconsistent_dict(future2, future1, inconsistencies)
                    return True
        return False

    @staticmethod
    def add_to_inconsistent_dict(formula1, formula2, inconsistencies):
        if formula1 in inconsistencies:
            inconsistencies[formula1].append(formula2)
        else:
            inconsistencies[formula1] = [formula2]

    def is_in_inconsistencies_dict(formula1, formula2, inconsistencies: dict):
        if formula1 in inconsistencies and formula2 in inconsistencies[formula1]:
            return True
        if formula2 in inconsistencies and formula1 in inconsistencies[formula2]:
            return True
        return False




    @staticmethod
    def delete_inconsistent_sets(dnf: list, inconsistences = dict(), strToAb= dict()):
        consistent_dnf = list()
        for i, model in enumerate(dnf):
            if not Inconsistencies.is_inconsistent_set(model, inconsistences, strToAb):
                consistent_dnf.append(model)
            

        return consistent_dnf 
            
            


        