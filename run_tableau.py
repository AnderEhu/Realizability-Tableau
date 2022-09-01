import sys
from Tableau.src.tableau import Tableau
from tools import read_benchmark_file



def execute():

    initial_formula, safety_formula, env_constraints = read_benchmark_file(sys.argv[1])
    tableau = Tableau(initial_formula, safety_formula, env_constraints)
    print("IS OPEN TABLEAU? ", tableau.is_open)

execute()