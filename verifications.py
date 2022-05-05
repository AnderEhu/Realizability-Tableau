from os import remove
from circuit import Circuit
from tools import MiniSAT


def is_sat(formula):

    """
    This procedure takes as input a Boolean formula and returns a list of sets,
    representing a DNF equivalent to the original formula, of minimal size.
    This is exactly a cover of the formula by prime implicants.

    It calls the tool Bica to do this.

    The input formula can be either an existential Boolean circuit, built by using
    the class Circuit, or a list of lists. For example,

        ['&', 'True', ['&', ['->', ['&', ['-', 'p'], ['&', ['X', 'p'], ['&', ['X', ['X', 'p'] ...

    The flags allow to display information and delete temporary files.

    - Created on Sat Jun 26 13:34:12 2021

    - Author: Noel Arteche


    """


    # Create a circuit object with the benchmark to be used.
    # (check first whether it is already a circuit, or whether you need
    # to convert it from a list format given as input).
    C = Circuit()
    if isinstance(formula, Circuit):
        C = formula
    else:
        C.list_to_circ(formula)

    # Create a DIMACS file tuned for BICA with the positive formula.
    C.write_in_DIMACS("pos.cnf", add_BICA_line=True)



    return MiniSAT("pos.cnf") == "SAT"
