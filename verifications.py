from os import remove
from circuit import Circuit
from tools import MiniSAT


def is_sat(formulaAB):
    "True if given formula is satisfiable"
    C = Circuit()
    C.list_to_circ(formulaAB)
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)
    is_sat = (MiniSAT("pos.cnf") == "SAT")
    remove("pos.cnf")
    return is_sat 