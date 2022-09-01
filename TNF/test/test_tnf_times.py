from asyncio import futures
from pickle import TRUE
from time import daylight
import pytest
from sklearn.utils import shuffle
from Solver.bica import prime_cover_via_BICA
from TNF.src.separated_formula import SeparatedFormula

from TNF.src.tnf import TNF
from TemporalFormula.src.temporal_formula import TemporalFormula
from tools import read_benchmark_file



overleaf_benchmarks = [
    "Xp_e <--> Xs",
    "((c) & (-p_e -> G[0,9]c) & (G[0,9]c | F[0,2]-s))",
    "(a -> c) & (Xp_e -> F[1,2]a) & (-Xp_e -> F[1,10]-c)",
    "((r1_e -> F[0,3]g1) & (r2_e -> F[0,3]g2) & (-(g1 & g2)) & ((-r1_e & -r2_e) -> X-g2))",


]

@pytest.mark.parametrize(
    "formula_str", overleaf_benchmarks
)
def test_tfn_overleaf(formula_str):
    TNF(formula_str, info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=False)


random_benchmarks = [
    "((a & b & Xfuture1) | (-a & b & Xfuture2) | (a & -b & Xfuture3)) & (p_e | -p_e)",
    "((p_e & a & Xfuture1) | (b & Xfuture2) | (-a & Xfuture3))",
    "((a & Xfuture1) | (b & Xfuture2) | (-b & Xfuture3))",
    "((a & Xfuture1) | (-p_e & b & -a & Xfuture2) | (-b & Xfuture3))",
    "((a & Xfuture1) | (b & -a & Xfuture1) | (-b & Xfuture1))",
    "((a & Xfuture1) | (b & a & Xfuture2) | (b & Xfuture3))",
    "(a & Xfuture1)",
    "((a & Xfuture1) | (b & a & -Xfuture1) | (b & Xfuture3))",
    "((a & Xfuture1 & Xfuture2 & Xfuture3) | (b & -a &  Xfuture2 & Xfuture3) | (-b & Xfuture1))",
    "((b & Xfuture1 & Xfuture2 & Xfuture3) | (-b & -a &  Xfuture2 & Xfuture3))",
]

@pytest.mark.parametrize(
    "formula_str", random_benchmarks
)
def test_tfn_random(formula_str):
    TNF(formula_str, info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=False)




developair_benchmarks_path = {
    "benchmarks/Developair/benchmark4.txt",
    "benchmarks/Developair/benchmark5.txt",
    "benchmarks/Developair/benchmark6.txt",
    "benchmarks/Developair/benchmark8.txt",

}
@pytest.mark.parametrize(
    "path", developair_benchmarks_path
)

def test_tnf_developair(path):
    initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
    safety_specification = initial_formula + safety_formula + env_constraints
    safety_specification_ab = ['&']
    for f in safety_specification:
        f_ab = TemporalFormula(f, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=False).ab
        safety_specification_ab.append(f_ab)

    safety_specification_ab = TemporalFormula.fix_ab_list(safety_specification_ab)

    
    env_constraints_str = 'True'
    for env_constraint_str in env_constraints:
        env_constraints_str += "&(" + env_constraint_str + ")"
    


    tnf = TNF(safety_specification_ab, env_constraints_str=env_constraints_str, env_vars=list(), info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=False)