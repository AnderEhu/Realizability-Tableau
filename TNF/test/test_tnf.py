import pytest

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
    tnf = TNF(formula_str, info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=True)

    if tnf.verification:
        assert True
    else:
        assert False



developair_benchmarks_path = {
    "benchmarks/Developair/benchmark4.txt",
    "benchmarks/Developair/benchmark5.txt",
    "benchmarks/Developair/benchmark6.txt",
    "benchmarks/Developair/benchmark7.txt",
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
        f_ab = TemporalFormula(f, changeNegAlwaysEventually = True,  extract_negs_from_nexts = True, split_futures = False, strict_future_formulas=True).ab
        safety_specification_ab.append(f_ab)

    safety_specification_ab = TemporalFormula.fix_ab_list(safety_specification_ab)

    
    env_constraints_str = 'True'
    for env_constraint_str in env_constraints:
        env_constraints_str += "&(" + env_constraint_str + ")"
    


    tnf = TNF(safety_specification_ab, env_constraints_str=env_constraints_str, env_vars=list(), info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=True)

    if tnf.verification:
        assert True
    else:
        assert False
