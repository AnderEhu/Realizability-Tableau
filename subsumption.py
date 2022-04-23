
import copy
from temporal_formula import delete_temp_ops, get_literals, getStrToList, include_next_to_formula, is_in_interval_success
from verifications import is_sat

def subsumes(future1, future2, subsumptions = None):
    #future1 subsumes future2
    if subsumptions:
        return future2 in subsumptions[future1]

    if future1 == future2:
        return True

    #Cuidado revisar
    if future1[0] == "X" and future1[1] != "[":
        print(future1)
        future1 = include_next_to_formula(future1[1:])
        print(future1)

    if future2[0] == "X" and future2[1] != "[":
        print(future2)
        future2 = include_next_to_formula(future2[1:])
        print(future2)


    future1List = getStrToList(future1)
    future1Literals = get_literals(future1List)

    future2List = getStrToList(future2)

    future2Literals = get_literals(future2List)

    if future1Literals >= future2Literals and is_in_interval_success(future1List, future2List):
            if is_in_interval_success(future1List, future2List):
                literal1WithOutTemp = delete_temp_ops(future1List)
                literal2WithOutTemp = delete_temp_ops(future2List)
                f = ['&', literal1WithOutTemp, ['-', literal2WithOutTemp]]
                is_sat_f = is_sat(f)
                if not is_sat_f:
                    return True                    
    return False



def calculate_subsumptions(formula):
    subsumptions = dict()
    futures = set()
    for formula_i in formula:
        for formula_ij in formula_i:
            if "X" in formula_ij or "F[" in formula_ij or "G[" in formula_ij:
                subsumptions[formula_ij] = {formula_ij}
                futures.add(formula_ij)
    for key in subsumptions.keys():
        for future in list(futures):
            future1 = copy.deepcopy(key)
            future2 = copy.deepcopy(future)
            if subsumes(future1, future2):
                subsumptions[key].add(future)
    return subsumptions

def print_subsumptions(s):
    for key in s.keys():
        print(" ", key, " subsumes ", s[key])