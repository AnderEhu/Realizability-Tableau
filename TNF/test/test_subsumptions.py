import pytest

from TNF.src.subsumptions import Subsumptions


subsumptions_list_futures_set_with_futures_set = {
    1: {
        'union_futures': [{'Xs','Xp','Xg'}, {'Xs', 'Xp'}],
        'futures_i':    {'Xs'},
        'res_union_futures': [{'Xs'}],
    },
    2: {
        'union_futures': [{'Xs'}],
        'futures_i':    {'Xs','Xp','Xg'},
        'res_union_futures': [{'Xs'}],
    },
    3: {
        'union_futures': [{'X[1]True'}],
        'futures_i':    {'Xs','Xp','Xg'},
        'res_union_futures': [{'X[1]True'}],
    },
    4: {
        'union_futures': [{'Xs','Xp','Xg'}],
        'futures_i':    {'X[1]True'},
        'res_union_futures': [{'X[1]True'}],
    },
    5: {
        'union_futures': [{'X[1]True'}],
        'futures_i':    {'X[1]True'},
        'res_union_futures': [{'X[1]True'}],
    },
    6: {
        'union_futures': [{'Xs','Xg'}, {'Xs', 'Xp'}, {'Xl'}],
        'futures_i':    {'Xs'},
        'res_union_futures': [{'Xl'},{'Xs'}],
    },
    7: {
        'union_futures': [{'Xs', 'Xg'}, {'Xl'}, {'Xs', 'Xp'}],
        'futures_i':    {'Xs'},
        'res_union_futures': [{'Xl'},{'Xs'}],
    },
    8: {
        'union_futures': [{'Xl'}, {'Xs', 'Xg'}, {'Xs', 'Xp'}],
        'futures_i':    {'Xs'},
        'res_union_futures': [{'Xl'},{'Xs'}],
    },
    9: {
        'union_futures': [{'Xl'}, {'Xs','Xg'}, {'Xs', 'Xp'}],
        'futures_i':    {'Xs', 'Xl', 'Xg', 'Xp'},
        'res_union_futures': [{'Xl'}, {'Xs','Xg'}, {'Xs', 'Xp'}],
    },
}

@pytest.mark.parametrize(
    "data", [value for _, value in subsumptions_list_futures_set_with_futures_set.items()]
)
def test_1_subsumptions_list_futures_set_with_futures_set(data):
    union_futures = data['union_futures']
    futures_i = data['futures_i']
    res_union_futures = data['res_union_futures']

    Subsumptions.list_futures_set_with_futures_set(union_futures, futures_i)

    if union_futures == res_union_futures:
        assert True
    else:
        assert False


is_list_futures_set_weaker_data = {
    1: {
        'list_futures_set_1': [{'Xs', 'Xl'}],
        'list_futures_set_2': [{'Xs', 'Xp', 'Xl'}],
        'expected_result': True,
    },
    2: {
        'list_futures_set_1': [{'Xs', 'Xp', 'Xl'}],
        'list_futures_set_2': [{'Xs', 'Xl'}],
        'expected_result': False,
    },
    3: {
        'list_futures_set_1': [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'list_futures_set_2': [{'Xs', 'Xp', 'Xl'}],
        'expected_result': True,
    },
    4: {
        'list_futures_set_1': [{'Xs', 'Xp', 'Xl', 'Xa'}, {'Xk', 'Xa'}, {'Xa'}],
        'list_futures_set_2': [{'Xs', 'Xp', 'Xl'}],
        'expected_result': False,
    },
    5: {
        'list_futures_set_1': [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'list_futures_set_2': [{'Xa'}, {'Xs', 'Xp', 'Xl'}],
        'expected_result': True,
    },
    6: {
        'list_futures_set_1': [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'list_futures_set_2': [{'Xa'}, {'Xs', 'Xp', 'Xl'}, {'Xh'}],
        'expected_result': False,
    },
    7: {
        'list_futures_set_1': [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'list_futures_set_2':  [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'expected_result': True,
    },
    8: {
        'list_futures_set_1': [{'Xs', 'Xl'}, {'Xl', 'Xa'}, {'Xa'}],
        'list_futures_set_2':  [{'Xss', 'Xll'}, {'Xll', 'Xaa'}, {'Xaaa'}],
        'expected_result': False,
    },



}
@pytest.mark.parametrize(
    "data", [value for _, value in is_list_futures_set_weaker_data.items()]
)
def test_1_is_list_futures_set_weaker(data):
    list_futures_set_1 = data['list_futures_set_1']
    list_futures_set_2 = data['list_futures_set_2']
    expected_result = data['expected_result']

    result = Subsumptions.is_list_futures_set_weaker(list_futures_set_1, list_futures_set_2)

    if expected_result == result:
        assert True
    else:
        assert False

move_lists_with_move_data = {
    1: {
        'list_of_moves': [[set(), [{'Xs', 'Xl'}]]],
        'new_move': [set(),[{'Xs', 'Xp', 'Xl'}]],
        'expected_result': [[set(), [{'Xs', 'Xl'}]]]
    },
    2: {
        'list_of_moves': [[set(),[{'Xs', 'Xp', 'Xl'}]]],
        'new_move': [set(),[{'Xs', 'Xl'}]],
        'expected_result': [[set(), [{'Xs', 'Xl'}]]]
    },
    3: {
        'list_of_moves': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xa'}]]],
        'new_move': [set(),[{'Xs', 'Xl'}]],
        'expected_result': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xa'}]], [set(),[{'Xs', 'Xl'}]]],
    },
    4: {
        'list_of_moves': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xa'}]]],
        'new_move': [set(),[{'Xs'}, {'Xa'}]],
        'expected_result': [[set(),[{'Xs'}, {'Xa'}]]],
    },
    5: {
        'list_of_moves': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xa'}]], [set(),[{'Xs', 'Xp', 'Xl'}, {'Xp'}]]],
        'new_move': [set(),[{'Xs'}, {'Xa'}]],
        'expected_result': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xp'}]], [set(),[{'Xs'}, {'Xa'}]]],
    },
    6: {
        'list_of_moves': [ [set(),[{'Xs', 'Xp', 'Xl'}, {'Xp'}]], [set(),[{'Xs', 'Xp', 'Xl'}, {'Xa'}]]],
        'new_move': [set(),[{'Xs'}, {'Xa'}]],
        'expected_result': [[set(),[{'Xs', 'Xp', 'Xl'}, {'Xp'}]], [set(),[{'Xs'}, {'Xa'}]]],
    },
}

@pytest.mark.parametrize(
    "data", [value for _, value in move_lists_with_move_data.items()]
)
def test_1_move_lists_with_move_data(data):
    list_of_moves = data['list_of_moves']
    new_move = data['new_move']
    expected_result = data['expected_result']

    Subsumptions.move_lists_with_move(list_of_moves, new_move)

    if expected_result == list_of_moves:
        assert True
    else:
        assert False
