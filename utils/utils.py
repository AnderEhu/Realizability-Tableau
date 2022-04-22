from os import remove
from z3 import *
from tools import MiniSAT
from circuit import Circuit


    




    



    

def print_bica(formula):
    formulaStr = ""
    for f in formula:
        modelStr = ""
        print(f)
        for l in list(f):
            print(l)
            if modelStr == "":
                modelStr += l
            else:
                modelStr += " ∧ " + l
        if formulaStr == "":
                formulaStr += l
        else:
            formulaStr += " v " +l
    return formulaStr











def post_processing_bica_models(models, subsumptions):
    from temporal_formula import TemporalFormula
    processing_models = []
    for model in models:
        literals = set()
        futures = set()
        for l in list(model):
            if "X" in l or "F[" in l or "G[" in l:
                if not futures:
                    futures.add(l)
                    continue
                delete_futures = set()
                for fi in list(futures):
                    if TemporalFormula.subsumes(fi, l, subsumptions):
                        break
                    elif TemporalFormula.subsumes(l, fi, subsumptions):
                        for fj in list(futures):
                            if TemporalFormula.subsumes(l, fj, subsumptions):
                                delete_futures.add(fj)
                        
                        futures.add(l)
                        break
                    else:
                        futures.add(l)
                futures = futures - delete_futures
                       
            else:
                literals.add(l)
        if futures == set():
            futures = {"True"}
        processing_models.append([literals, [futures]])
    return processing_models










def print_subsumptions(s):
    for key in s.keys():
        print(" ", key, " subsumes ", s[key])





def print_separated_formula(formula, AND = " ∧ ", OR = " v "):

        res = ""
        for fi in formula:
            literal_fi = fi[0]
            futures_fi = fi[1]
            literals_str = ""
            for li_fi in list(literal_fi):
                if literals_str == "":
                    literals_str += li_fi
                else:
                    literals_str += AND +li_fi
            futures_str = ""
            for futuresi_fi in futures_fi:
                and_futures_ij = ""
                for futuresij_fi in futuresi_fi:
                    if and_futures_ij == "":
                        and_futures_ij = futuresij_fi
                    else:
                        and_futures_ij += AND +futuresij_fi

                if futures_str == "":
                    futures_str = and_futures_ij
                else:
                    futures_str = "(" + futures_str + ")" +  OR + "(" + and_futures_ij + ")"
            
            futures_str = "(" + futures_str + ")"
            
            if res == "":
                if literals_str ==  "":
                    res += futures_str
                elif futures_str == "":
                    res += "(" + literals_str  + ")"
                else:
                    res += "(" + literals_str + AND + futures_str + ")"
            else:
                if literals_str ==  "":
                    res += OR + "(" + futures_str + ")"
                elif futures_str == "":
                    res += OR + "(" + literals_str  + ")"
                else:
                    res += OR + "(" + literals_str + AND + futures_str + ")"
            res += "\n"
            
        return res





