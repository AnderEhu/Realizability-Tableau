from errno import EHOSTUNREACH
import random
import sys

from matplotlib import lines
from dnf_formula import calculate_dnf
from separated_formula import are_equal_formulas, calculate_separated_formulas, separated_formula_to_ab
from subsumption import calculate_subsumptions
from temporal_formula import TemporalFormula
from tnf import TNF


def automatic_benchmark_generator(n):
    path = "benchmarks/all_formulas.txt"
    
    with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            formulasStr = "(True)"
            nline = 1
            validLines = random.sample(range(1, 370), n)
            print("Lineas: ", validLines)
            for formulaStr in f:
                if nline in validLines:
                    if formulaStr == "\n" or formulaStr=="":
                        continue
                    formulaStr = "&("+formulaStr.replace("\n", "").replace(" ", "")+")"
                    formulasStr+=formulaStr
                nline+=1

            formula = TemporalFormula(formulasStr)
            formula_ab = formula.ab
            parseFormulas.append(formula_ab)
    f.close()  
    return parseFormulas, validLines



def leer_fichero(n = False):

    path = sys.argv[1]
    with open(path, 'r') as f:
        lines = f.readlines()
        if n:
            selected_to_read = random.sample(range(0, len(lines)-1), n)
            print(selected_to_read, "\n")
            new_f = [line for i, line in enumerate(lines) if i in selected_to_read]
            sf = str_to_sf(new_f)
        else:
            sf = str_to_sf(lines)
    f.close()  
    return sf

def str_to_sf(f):
    ab = TemporalFormula(f).ab
    dnf = calculate_dnf(ab)
    subsumptions = calculate_subsumptions(ab)
    sf = calculate_separated_formulas(dnf, subsumptions)
    return sf

def ejecute(automatic = True):

    sf = leer_fichero()
    #print(parseFormulas)
    #TNF(parseFormulas, selected_formulas)
    tnf = TNF(sf).calculate_tnf()
    if not are_equal_formulas(sf, tnf):
        exit(0)
    if automatic:
        ejecute()


ejecute()