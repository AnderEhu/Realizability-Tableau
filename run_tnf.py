import random
import sys
from tableau import Tableau
from temporal_formula import TemporalFormula
from tnf import TNF



def leer_fichero(n = False):

    path = sys.argv[1]
    with open(path, 'r') as f:
        lines = f.readlines()
        if n:
            valid_lines = random.sample(range(0, len(lines)-1), n)
            print("Lines: ", valid_lines)
        else:
            valid_lines = list()
        split_lines = split_formulas(lines, valid_lines)
    f.close()  
    return split_lines


def split_formulas(lines, valid_lines):

    selected_lines = list()
    
    for i, line in enumerate(lines):
        if line == "\n" or line=="":
            continue
        if valid_lines:
            if i in valid_lines:
                selected_lines.append(line.replace("\n", "").replace(" ", ""))
        else:
            selected_lines.append(line.replace("\n", "").replace(" ", ""))

    return selected_lines




def execute(automatic = False):

    formulas = leer_fichero()
    temporal_formulas = TemporalFormula(formulas)
    TNF(temporal_formulas.ab, env_vars=temporal_formulas.env_vars, info=temporal_formulas.info)
    if automatic:
        execute(automatic)

execute(automatic=False)