import pytest
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
    tnf = TNF(formula_str, info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=True)

    if tnf.verification:
        assert True
    else:
        assert False


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
    tnf = TNF(formula_str, info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=True)
    if tnf.verification:
        assert True
    else:
        assert False




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
    


    tnf = TNF(safety_specification_ab, env_constraints_str=env_constraints_str, env_vars=list(), info=dict(), activated_apply_subsumptions=False, activated_print_info=False, activated_print_tnf=True, activate_verification=True)
    assert tnf.verification
    if tnf.verification:
        assert True
    else:
        assert False

sf1 = [
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn1'}]), 
    SeparatedFormula.set_separated_formula(set(), {'b'}, [{'Xn2'}]),
    SeparatedFormula.set_separated_formula(set(), {'-a'}, [{'Xn3'}]),

]

sf2 = [
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn1'}]), 
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn2'}]),
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn3'}]),

]

sf3 = [
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn1'}]), 
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn2'}]),
    SeparatedFormula.set_separated_formula(set(), {'a'}, [{'Xn3'}]),
    SeparatedFormula.set_separated_formula(set(), {'-a'}, [{'Xn3'}]),


]


index_stack_1 = [0, 1]
literal_stack_1 = [{'a'}, {'a', 'b'}]
futures_stack_1 = [{'Xn1'}, {'Xn2'}]
i_sf1 = len(sf1)
skip_1 = list()

index_stack_2 = [0, 2]
literal_stack_2 = [{'a'}, {'-a'}]
futures_stack_2 = [{'Xn1'}, {'Xn3'}]
i_sf1 = len(sf1)
skip_1 = list()

index_stack_3 = [0]
literal_stack_3 = [{'a'}]
futures_stack_3 = [{'Xn1'}, {'Xn2'}, {'Xn3'}]
i_sf2 = len(sf2)
skip_2 = [{'a'}]

index_stack_4 = [0]
literal_stack_4 = [{'a'}]
futures_stack_4 = [{'Xn1'}, {'Xn2'}, {'Xn3'}]
i_sf4 = len(sf3)
skip_4 = [{'a'}]

index_stack_5 = [3]
literal_stack_5 = [{'-a'}]
futures_stack_5 = [{'Xn3'}]
i_sf5 = len(sf3)
skip_5 = [{'a'}, {'-a'}]


get_valid_i_data = {
    1: {
        'formula': sf1,
        'index_stack': index_stack_1,
        'literal_stack': literal_stack_1,
        'futures_stack': futures_stack_1,
        'i': i_sf1,
        'skip': skip_1,
        'valid_i': 2,
    },
    2: {
        'formula': sf1,
        'index_stack': index_stack_1,
        'literal_stack': literal_stack_1,
        'futures_stack': futures_stack_1,
        'i': i_sf1,
        'skip': skip_1,
        'valid_i': 1,
    },
    3: {
        'formula': sf2,
        'index_stack': index_stack_3,
        'literal_stack': literal_stack_3,
        'futures_stack': futures_stack_3,
        'i': i_sf2,
        'skip': skip_2,
        'valid_i': -1,
    },
    4: {
        'formula': sf3,
        'index_stack': index_stack_4,
        'literal_stack': literal_stack_4,
        'futures_stack': futures_stack_4,
        'i': i_sf4,
        'skip': skip_4,
        'valid_i': 3,
    },
    5: {
        'formula': sf3,
        'index_stack': index_stack_5,
        'literal_stack': literal_stack_5,
        'futures_stack': futures_stack_5,
        'i': i_sf5,
        'skip': skip_5,
        'valid_i': -1,
    },
}

@pytest.mark.parametrize(
    "data", [value for _, value in get_valid_i_data.items()]
)
def test_1_valid_i(data):
    formula = data['formula']
    index_stack = data['index_stack']
    futures_stack = data['futures_stack']
    literal_stack = data['literal_stack']
    i = data['i']
    skip = data['skip']
    expected_valid_i = data['valid_i']

    valid_i = TNF.get_valid_i(i, formula, index_stack, literal_stack, futures_stack, skip)
    
    print(valid_i, index_stack, futures_stack)

    if valid_i == expected_valid_i:
        assert True
    else:
        assert False

