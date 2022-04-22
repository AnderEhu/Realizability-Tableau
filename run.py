import random
import sys
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



def leer_fichero():
        if len(sys.argv) == 1:
            path = "tnf/benchmarks/Overleaf/bench2"
        else:
            path = sys.argv[1]
        mode = 1
        if len(sys.argv) == 3:
            mode = sys.argv[2]
        with open(path, 'r') as f:
            parseFormulas = ['&', 'True']
            formulasStr = "(True)"
            for formulaStr in f:
                if formulaStr == "\n" or formulaStr=="":
                    continue
                formulaStr = "&("+formulaStr.replace("\n", "").replace(" ", "")+")"
                formulasStr+=formulaStr

            formula = TemporalFormula(formulasStr)
            formula_ab = formula.ab
            parseFormulas.append(formula_ab)

        f.close()  
        return parseFormulas

def ejecute(automatic = False):
    
    validLines = False
    if automatic:
        parseFormulas, validLines = automatic_benchmark_generator(2)
    else:
        parseFormulas = leer_fichero()
    print(parseFormulas)
    TNF(parseFormulas, validLines)
    if automatic:
        ejecute()


ejecute()