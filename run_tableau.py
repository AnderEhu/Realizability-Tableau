import random
import sys

from matplotlib.pyplot import close
from tableau import Tableau
from temporal_formula import TemporalFormula


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
        split_lines = split_formulas(lines)
    f.close()  
    return split_lines


def split_formulas(lines):

    I = list()
    G = list()
    C = list()
    
    for line in lines:
        if line == "\n" or line=="":
            continue
        line = line.replace("\n", "").replace(" ", "")
        if line == "InitialFormula":
            activate = "I"

        elif line == "SafetyFormula":
            activate = "G"

        elif line == "EnvironmentGlobalConstraints":
            activate = "C"
        else: 
            if activate == "I":
                I.append(line) 
            elif activate == "G":
                G.append(line)
            elif activate == "C":
                C.append(line)
            else:
            
                print("Error en la  line : ", line)

    return I, G, C


def print_log_time(log_time):
    log_time_sorted_keys = sorted(log_time, key=log_time.get, reverse=True)
    with open("log_time.txt", "w") as f:
        for r in log_time_sorted_keys:
            f.write(f'Function {r} : {log_time[r]:.8f} seconds\n')
    f.close()


def execute():
    log_time = {}
    initial_formula, safety_formula, env_constraints = leer_fichero()
    Tableau(initial_formula, safety_formula, env_constraints, log_time = log_time)
    print_log_time(log_time)



execute()