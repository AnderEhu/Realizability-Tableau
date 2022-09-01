import pytest

from TNF.src.separated_formula import SeparatedFormula


equal_sf = {

    1: [
            [{
                'X': {'p_e'}, 
                'Y': {'s'},
                'Futures': [{'Xb'}]
            }],
            [{
                'X': {'p_e'}, 
                'Y': {'s'},
                'Futures': [{'Xb'}]
            }],

        ],
    2: [
            [{
                'X': {'p_e'}, 
                'Y': {},
                'Futures': [{'Xb'}]
            }],
            [{
                'X': {'p_e'}, 
                'Y': {},
                'Futures': [{'Xb'}]
            }],

        ],
    3: [
            [{
                'X': {}, 
                'Y': {},
                'Futures': [{'Xb'}]
            }],
            [{
                'X': {}, 
                'Y': {},
                'Futures': [{'Xb'}]
            }],

        ],

    4: [
            [{
                'X': {}, 
                'Y': {},
                'Futures': []
            }],
            [{
                'X': {}, 
                'Y': {},
                'Futures': []
            }],

        ],

    5: [
            [{
                'X': {'p_e'}, 
                'Y': {'s'},
                'Futures': []
            }],
            [{
                'X': {'p_e'}, 
                'Y': {'s'},
                'Futures': []
            }],

        ],

}

@pytest.mark.parametrize (
    "sf1, sf2", [(value[0], value[1]) for _, value in equal_sf.items()]
)
def test_1_are_equal_separated_formulas(sf1, sf2):
    are_equal = SeparatedFormula.are_equal_separated_formulas(sf1, sf2,is_sf2_tnf=False)
    if are_equal:
        assert True
    else:
        assert False


equal_2_sf = {

    1: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[5]s'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'G[1, 10]p'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'G[1, 10]t'}]
                },

            ],
            [   
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'},{'X[5]s'}, {'G[1, 10]p'}, {'G[1, 10]t'}]
                }
            ],

        ],
        2: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                },

            ],
            [   
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'}, {'-X[1]True'}]
                }
            ],

        ],
        3: [
            [
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}]
                },
                { 
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'G[3,5]b', 'Xs', 'X[10]t'}]
                },


            ],
            [   
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}, {'G[3,5]b', 'Xs', 'X[10]t'}]
                },
                { 
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs', 'Xt'}]
                },
            ],

        ],

        4: [
            [
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'G[3,5]b', 'Xs', 'X[10]t'}]
                },


            ],
            [   
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}, {'G[3,5]b', 'Xs', 'X[10]t'}]
                },
            ],

        ],
}

@pytest.mark.parametrize (
    "sf1, sf2", [(value[0], value[1]) for _, value in equal_2_sf.items()]
)
def test_2_are_equal_separated_formulas(sf1, sf2):
    are_equal = SeparatedFormula.are_equal_separated_formulas(sf1, sf2,is_sf2_tnf=False)
    if are_equal:
        assert True
    else:
        assert False


equal_3_sf = {

    1: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[5]s'}]
                },

            ],
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[1]True'}, {'X[5]s'}]
                },

            ]
    ],
    2: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[5]s'}]
                },

            ],
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'-X[1]True'}, {'X[5]s'}]
                },

            ]
    ],
    3: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                },

            ],
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[1]False'}]
                },

            ]
    ],
    
}

@pytest.mark.parametrize (
    "sf1, sf2", [(value[0], value[1]) for _, value in equal_3_sf.items()]
)
def test_3_are_not_equal_separated_formulas(sf1, sf2):
    are_equal = SeparatedFormula.are_equal_separated_formulas(sf1, sf2,is_sf2_tnf=False)
    if  are_equal:
        assert True
    else:
        assert False



not_equal_1_sf = {

    1: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[5]s'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'G[1, 10]p'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'G[1, 10]t'}]
                },

            ],
            [   
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'},{'X[5]s'}, {'-G[1, 10]p'}, {'G[1, 10]t'}]
                }
            ],

        ],
        2: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'Xb'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                },

            ],
            [   
                {
                    'X': {'-p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                }
            ],

        ],
        3: [
            [
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}]
                },
                { 
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'G[3,5]b', 'Xs', 'X[10]t'}]
                },


            ],
            [   
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'Xt'}, {'G[3,5]b', 'Xs', '-X[10]t'}]
                },
                { 
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', 'F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs', 'Xt'}]
                },
            ],

        ],
        4: [
            [
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': []
                },
                { 
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', 'G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', '-F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'G[3,5]b', 'Xs', 'X[10]t'}]
                },


            ],
            [   
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': []
                },
                { 
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'s','t', 'p'},
                    'Futures': [{'Xb', '-G[10,20]s', 'Xt'}]
                },
                {
                    'X': {'p_e', 'r_e'}, 
                    'Y': {'-s','t', 'p'},
                    'Futures': [{'Xb', 'Xs', '-F[9,19]t'}]
                },
                {
                    'X': {'-p_e', 'r_e'}, 
                    'Y': {'s','-t', 'p'},
                    'Futures': [{'X[10]b', 'Xs'}]
                },
            ],

        ],
}

@pytest.mark.parametrize (
    "sf1, sf2", [(value[0], value[1]) for _, value in not_equal_1_sf.items()]
)
def test_1_are_not_equal_separated_formulas(sf1, sf2):
    are_equal = SeparatedFormula.are_equal_separated_formulas(sf1, sf2,is_sf2_tnf=False)
    if not are_equal:
        assert True
    else:
        assert False


not_equal_2_sf = {

    1: [
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': [{'X[5]s'}]
                },

            ],
            [
                {
                    'X': {'p_e'}, 
                    'Y': {'s'},
                    'Futures': []
                },

            ]
    ],
    
}

@pytest.mark.parametrize (
    "sf1, sf2", [(value[0], value[1]) for _, value in not_equal_2_sf.items()]
)
def test_2_are_not_equal_separated_formulas(sf1, sf2):
    are_equal = SeparatedFormula.are_equal_separated_formulas(sf1, sf2,is_sf2_tnf=False)
    if not are_equal:
        assert True
    else:
        assert False


dnf_to_sf = {
    
        1: [
            [
                {'p_e', 'pppp_e', 's', 'sssss', 'X[1]s', 'X[10]p_e', 'G[1, 10](a|b)','F[10, 20](a&b)', 'G[1, 10](r_e|b)','F[10, 20](a&r_e)'},
                {'p_e'},
                {'s'},
                {'X[1]s'}


            ],
            [   
                {
                    'X': {'p_e', 'pppp_e'}, 
                    'Y': {'s', 'sssss'},
                    'Futures': [{'X[1]s', 'X[10]p_e', 'G[1, 10](a|b)','F[10, 20](a&b)', 'G[1, 10](r_e|b)','F[10, 20](a&r_e)'}]
                },
                {
                    'X': {'p_e'}, 
                    'Y': set(),
                    'Futures': [{'X[1]True'}]
                },
                {
                    'X': set(), 
                    'Y': {'s'},
                    'Futures': [{'X[1]True'}]
                },
                {
                    'X': set(), 
                    'Y': set(),
                    'Futures': [{'X[1]s'}]
                }
            ],

        ],
       
}
@pytest.mark.parametrize (
    "dnf, sfs", [(value[0], value[1]) for _, value in dnf_to_sf.items()]
)
def test_1_dnf_to_Sf(dnf, sfs):
    possible_sfs = SeparatedFormula.dnf_to_sf(dnf)

    if possible_sfs == sfs:
        assert True
    else:
        assert False


consistent_set_variables = {
    1 : [{'p_e', 's', 'l'}, {'r_e', 'p', 'k'}],
    2 : [{'p_e', 's', 'l'}, {'p_e', 'p', 'k'}],
    3 : [{'pppppp_e', 'sssss', 'llllll'}, {'rrrrr_e', 'plasdfas', 'kferfefe'}],
    4 : [{'pppppp_e', 'sssss', 'llllll', 'p_e', 's', 'l'}, {'rrrrr_e', 'plasdfas', 'kferfefe','r_e', 'p', 'k', 'p_e', 's', 'l'}],
    5 : [{'p_e'}, {}],
    6 : [{}, {}],


}

@pytest.mark.parametrize(
    "set_literals_1, set_literals_2", [(value[0], value[1]) for _, value in consistent_set_variables.items()]
)
def test_consistent_set_variables(set_literals_1, set_literals_2):
    is_consistent_sets = SeparatedFormula.is_consistent(set_literals_1, set_literals_2)
    if is_consistent_sets:
        assert True
    else:
        assert False


inconsistent_set_variables = {
    1 : [{'p_e', 's', 'l'}, {'-p_e', 'p', 'k'}],
    2 : [{'pppppp_e', '-sssss', 'llllll', 'p_e', 's', 'l'}, {'rrrrr_e', 'sssss', 'kferfefe','r_e', 'p', 'k', 'p_e', 's', 'l'}],

}

@pytest.mark.parametrize(
    "set_literals_1, set_literals_2", [(value[0], value[1]) for _, value in inconsistent_set_variables.items()]
)
def test_inconsistent_set_variables(set_literals_1, set_literals_2):
    is_consistent_sets = SeparatedFormula.is_consistent(set_literals_1, set_literals_2)
    if not is_consistent_sets:
        assert True
    else:
        assert False

