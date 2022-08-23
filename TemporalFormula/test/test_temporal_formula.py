import pytest
from TemporalFormula.src.temporal_formula import AND_OPERATOR, TemporalFormula, OR_OPERATOR

test_1_expected_formulas = {
    "a|b": [OR_OPERATOR, "a", "b"],
    "a&b": [AND_OPERATOR, "a", "b"],
    "X(a&b)": [AND_OPERATOR, ['X[1]', "a"], ['X[1]', "b"]],
    "-X(a&b)": [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]],
    "a->b": [OR_OPERATOR, ['-', 'a'], 'b'],
    "a<-->b": [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']],
    "-X-(a&b)": [AND_OPERATOR, ['X[1]', "a"], ['X[1]', "b"]],
    "---X(a&b)": [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]],
    "XXXXXXXXXXa": ["X[10]", "a"],
    "XXXX-XXXX-XX(a|b)":  [OR_OPERATOR, ["X[10]", "a"], ["X[10]", "b"]],
    "-XXXX-XXXX-XX(a|b)": [AND_OPERATOR, ["X[10]", ['-', "a"]], ["X[10]", ['-', "b"]]],
    "F[0,1]a": ['F[0,1]', "a"],
    "-F[0,1]a": ['-', ['F[0,1]', "a"]],
    "-F[100,500](a<-->b)": ['-', ['F[100,500]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]]],
    "G[10000,50000]((-a|b)&(-b|a))": ['G[10000,50000]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]],
    "(---X(a&b)) | G[10000,50000]((-a|b)&(-b|a))": [OR_OPERATOR, [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]], ['G[10000,50000]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]]],
    "(---X(a&b)) & F[2,5]((-a|b)&(-b|a))": [AND_OPERATOR, [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]], ['F[2,5]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]]],
    "((---X(a&b)) | G[10000,50000]((-a|b)&(-b|a))) | ((---X(a&b)) & F[2,5]((-a|b)&(-b|a)))": [OR_OPERATOR, [OR_OPERATOR, [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]], ['G[10000,50000]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]]], [AND_OPERATOR, [OR_OPERATOR, ['X[1]', ['-', "a"]], ['X[1]', ['-', "b"]]], ['F[2,5]', [AND_OPERATOR, [OR_OPERATOR, ['-', 'a'], 'b'],  [OR_OPERATOR, ['-', 'b'], 'a']]]]]
}

@pytest.mark.parametrize (
    "formula", list(test_1_expected_formulas.keys())
)
def test_1_general_parse_formula(formula):
    formula_ab = TemporalFormula(formula, changeNegAlwaysEventually = False, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False).ab
    assert formula_ab == test_1_expected_formulas[formula]


test_2_expected_formulas = {
    "-F[0,1]a": ['G[0,1]', ['-', 'a']], 
    "-F[100,500](a<-->b)": ['G[100,500]', [OR_OPERATOR, [AND_OPERATOR, 'a', ['-','b']],  [AND_OPERATOR, 'b', ['-', 'a']]]],
    "-((F[0,1]a) & (F[100,500](a<-->b)))": [OR_OPERATOR, ['G[0,1]', ['-', 'a']], ['G[100,500]', [OR_OPERATOR, [AND_OPERATOR, 'a', ['-','b']],  [AND_OPERATOR, 'b', ['-', 'a']]]]],
    "-G[0,1]a": ['F[0,1]', ['-', 'a']], 
    "-G[100,500](a<-->b)": ['F[100,500]', [OR_OPERATOR, [AND_OPERATOR, 'a', ['-','b']],  [AND_OPERATOR, 'b', ['-', 'a']]]],
    "-((G[0,1]a) & (G[100,500](a<-->b)))": [OR_OPERATOR, ['F[0,1]', ['-', 'a']], ['F[100,500]', [OR_OPERATOR, [AND_OPERATOR, 'a', ['-','b']],  [AND_OPERATOR, 'b', ['-', 'a']]]]]

}

@pytest.mark.parametrize (
    "formula", list(test_2_expected_formulas.keys())
)
def test_2_general_parse_formula(formula):
    formula_ab = TemporalFormula(formula, changeNegAlwaysEventually = True, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False).ab
    assert formula_ab == test_2_expected_formulas[formula]



test_3_expected_formulas = {
    "-Xa": ['-',['X[1]', 'a']],
    "-X(a&b)": [OR_OPERATOR, ['-', ["X[1]", "a"]], ['-', ["X[1]", "b"]]],
    "-X(a|b)": [AND_OPERATOR, ['-', ["X[1]", "a"]], ['-', ["X[1]", "b"]]]
}

@pytest.mark.parametrize (
    "formula", list(test_3_expected_formulas.keys())
)
def test_3_general_parse_formula(formula):
    formula_ab = TemporalFormula(formula, changeNegAlwaysEventually = True, extract_negs_from_nexts = True, split_futures = False, strict_future_formulas = False).ab
    assert formula_ab == test_3_expected_formulas[formula]


test_4_expected_formulas = {
    "F[0,1]a": [OR_OPERATOR, 'a', ['X[1]', 'a']],
    "G[0,1]a": [AND_OPERATOR, 'a', ['X[1]', 'a']],
    "F[99,100]a": [OR_OPERATOR, ['X[99]', 'a'], ['X[100]', 'a']],
    "G[99,100]a": [AND_OPERATOR, ['X[99]', 'a'], ['X[100]', 'a']],
    "F[0,100]a": [OR_OPERATOR, 'a', ['X[1]', ['F[0,99]','a']]],
    "G[0,100]a": [AND_OPERATOR, 'a', ['X[1]', ['G[0,99]','a']]],
    "F[110,199]a": [OR_OPERATOR, ['X[110]', 'a'], ['X[1]', ['F[110,198]','a']]],
    "G[110,199]a": [AND_OPERATOR, ['X[110]', 'a'], ['X[1]', ['G[110,198]','a']]],


}

@pytest.mark.parametrize (
    "formula", list(test_4_expected_formulas.keys())
)
def test_4_general_parse_formula(formula):
    formula_ab = TemporalFormula(formula, changeNegAlwaysEventually = True, extract_negs_from_nexts = True, split_futures = True, strict_future_formulas = True).ab
    assert formula_ab == test_4_expected_formulas[formula]




test_get_temporal_limits_expected = {
    "F[0,1]": (0,1),
    "F[0,10]": (0,10),
    "F[10,100]": (10,100),
    "F[100,99999]": (100,99999),
    "G[0,1]": (0,1),
    "G[0,11]": (0,11),
    "G[15,101]": (15,101),
    "G[20098,999998]": (20098,999998)

}

@pytest.mark.parametrize (
    "bounded_temporal_operator", list(test_get_temporal_limits_expected.keys())
)
def test_get_temporal_limits(bounded_temporal_operator):
    interval = TemporalFormula.get_temporal_op_limits(bounded_temporal_operator)
    assert interval == test_get_temporal_limits_expected[bounded_temporal_operator]

test_get_next_n_expected = {
    "X": 1,
    "X[1]": 1,
    "X[2]": 2,
    "X[11]": 11,
    "X[111111111111111111]": 111111111111111111
}

@pytest.mark.parametrize (
    "next_operator", list(test_get_next_n_expected.keys())
)
def test_get_temporal_limits(next_operator):
    n = TemporalFormula.get_next_n(next_operator)
    assert n == test_get_next_n_expected[next_operator]


subsumptions = {
    "F[2,3]a": "F[0,5](a|b)",
    "G[0,5]a": "G[2,3](a|b)",
    "G[0,5]b": "F[2,3](a|b)",
    "a": "F[0,1000]a",
    "Xa": "F[0,3]a",
    "Xb": "F[1,1]b",
    "Xc": "G[1,1]c",
    "F[1,1]a": "Xa",
    "G[1,1]a": "Xa",
    "F[20,30](a&b)": "F[0,50](a|b)",
    "G[0,500](c&Xb)": "G[200,300](Xb)",
    "c": "F[0,10](a|b|c)",
    "s": "F[0,10]((a&b)|s)",

}

@pytest.mark.parametrize (
    "phi, alpha", 
    [ 
        (key, value) for key, value in subsumptions.items()
    ]
)
def test_is_in_interval_success(phi, alpha):
    phiAb = TemporalFormula(phi, changeNegAlwaysEventually = True, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False).ab
    alphaAb = TemporalFormula(alpha, changeNegAlwaysEventually = True, extract_negs_from_nexts = False, split_futures = False, strict_future_formulas = False).ab
    is_in = TemporalFormula.is_in_interval_success(phiAb, alphaAb)
    if is_in and phi in subsumptions and subsumptions[phi] == alpha:
        assert True
    else:
        assert False




@pytest.mark.parametrize (
    "future1, future2", 
    [ 
        (key, value) for key, value in subsumptions.items()
    ]
)
def test_success_subsumptions(future1, future2):
    subsumes = TemporalFormula.subsumes(future1, future2)
    if subsumes and future1 in subsumptions and subsumptions[future1] == future2:
        assert True
    else:
        assert False



no_subsumptions = {
    "F[20,30]a": "F[0,5](a|b)",
    "G[0,50]a": "G[200,3000](a|b)",
    "G[0,5]b": "F[4,10](a|b)",
    "a": "G[0,1000]a",
    "Xa": "G[0,3]a",
    "Xb": "F[2,5]b",
    "Xc": "XXc",
    "F[1,1]a": "XXa",
    "G[1,1]a": "XXXXa",
    "F[20,30](a&b)": "G[0,50](a|b)",
    "G[0,500](c&Xb)": "G[200,3000](Xb)",
    "F[0,500](c&Xb)": "G[200,3000](Xb)",
    "c": "F[1,10](a|b|c)",
    "p": "c",
    "pp": "F[1,10](a|s)",
}


@pytest.mark.parametrize (
    "future1, future2", 
    [ 
        (key, value) for key, value in no_subsumptions.items()
    ]

)
def test_no_subsumptions(future1, future2):
    subsumes = TemporalFormula.subsumes(future1, future2)
    print(subsumes)
    if not subsumes and future1 in no_subsumptions and no_subsumptions[future1] == future2:
        assert True
    else:
        assert False









    