from doctest import FAIL_FAST
import pytest

from TNF.src.inconsistencies import Inconsistencies



inconsistencies_data = {
    1: ['X[1](G[0,1]a)', 'X[2]-a'],
    2: ['X[1](G[0,1]a)', '-X[2]a'],
    3: ['G[2,3](a&b)', 'G[2,10]-b'],
    4: ['-F[2,3]-(a&b)', 'G[2,10]-b'],
    5: ['-F[2,3]-(a&b)', 'G[2,10]-(a|b)'],
    6: ['G[10,100](a&b)', 'F[100,100]-(a&b)'],
    7: ['F[100,100]-(a&b)', 'G[10,100](a&b)'],
    8: ['a', 'G[0,1]-a'],
    9: ['X[99](c)', 'X[1](G[10,98](-c))']



}
@pytest.mark.parametrize(
    "data", [value for _, value in inconsistencies_data.items()]
)
def test_1_inconsistencies(data):
    are_inconsistent = Inconsistencies.are_inconsistent_formulas(data[0], data[1], simple = False)
    assert are_inconsistent

simple_inconsistencies_data = {
    1: ['X[1](G[0,1](a))', 'X[2](-a)'],
    2: ['X[1](G[0,1]a)', '-X[2]a'],
    3: ['G[2,3](b)', 'G[2,10]-b'],
    4: ['-F[2,3](-b)', 'G[2,10](-b)'],
    5: ['-F[2,3](-b)', 'G[2,10](-b)'],
    6: ['G[10,100](-a)', 'F[100,100](a)'],
    7: ['F[100,100](b)', 'G[10,100](-b)'],
    8: ['a', 'G[0,1](-a)'],
    9: ['X[99](c)', 'X[1](G[10,98](-c))'],
    10: ['F[99,99](c)', 'X[1](G[10,98](-c))']




}
@pytest.mark.parametrize(
    "data", [value for _, value in simple_inconsistencies_data.items()]
)
def test_1_inconsistencies_simple(data):
    are_inconsistent = Inconsistencies.are_inconsistent_formulas(data[0], data[1], simple=True)
    assert are_inconsistent


# not_inconsistencies_data = {
#     1: ['X[1](G[0,1]a)', 'X[2]a'],
#     2: ['X[1](G[0,1]a)', 'X[2]a'],
#     3: ['G[2,3]-(a&b)', 'G[2,10]b'],
#     4: ['-F[2,3](a&b)', 'G[2,10]-b'],
#     5: ['-F[2,3](a&b)', 'G[2,10]-(a|b)'],
#     6: ['G[10,100](a&b)', 'F[100,100](a&b)'],
#     7: ['F[100,100]-(a&b)', '-G[10,100](a&b)'],
#     8: ['-a', 'G[0,1]-a'],
#     9: ['X[1](G[10,20]a)', 'X[2]-a'],
#     10: ['X[1](G[1,2]a)', '-X[1]a'],
#     11: ['G[20,30](a&b)', 'G[2,10]-b'],
#     12: ['-F[2,3]-(a&b)', 'G[4,10]-b'],
#     13: ['-F[20,30]-(a&b)', 'G[2,10]-(a|b)'],
#     14: ['G[101,1000](a&b)', 'F[100,100]-(a&b)'],
#     15: ['F[100,100]-(a&b)', 'G[10,99](a&b)'],
#     16: ['a', 'G[1,10]-a']

# }
# @pytest.mark.parametrize(
#     "data", [value for _, value in not_inconsistencies_data.items()]
# )
# def test_1_not_inconsistencies(data):
#     are_inconsistent = Inconsistencies.are_inconsistent_formulas(data[0], data[1])
#     assert not are_inconsistent


# not_inconsistencies_data_2 = {
#     1: ['X[1](G[0,1]b)', 'X[2]-a'],
#     2: ['X[1](G[0,1](a&c))', '-X[2]b'],
#     3: ['G[2,3](a&b&c)', 'G[2,10](e|d|l)'],
#     4: ['-F[2,3]-(a&b&c)', 'G[2,10]-t'],
#     5: ['-F[2,3]-(a&b&c)', 'G[2,10]-(g|k)'],
#     6: ['G[10,100](a&b&c)', 'F[100,100]-(q&k)'],
#     7: ['F[100,100]-(a&b&c)', 'G[10,100](h&k)'],
#     8: ['(a&c)', 'G[0,1]-b']


# }
# @pytest.mark.parametrize(
#     "data", [value for _, value in not_inconsistencies_data_2.items()]
# )
# def test_1_not_inconsistencies(data):
#     are_inconsistent = Inconsistencies.are_inconsistent_formulas(data[0], data[1])
#     assert not are_inconsistent


# inconsistencies_in_dnf = {
#     1: [[{'a', 'G[1,3]a', 'b'}, {'-Xa', 'G[1,3]a', 'b'}], [{'a', 'G[1,3]a', 'b'}]],
#     2: [[{'a', 'G[0,3]-(a|b)', 'b'}, {'-Xa', 'G[1,3]a', 'b'}], []],
#     3: [[{}], [{}]],
#     4: [[{'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[20,30](a&b)', 'G[2,10]-b'}, {'G[10,100](a&b)', 'F[100,100]-(a&b)'}, {'X[1](G[0,1]a)', '-X[2]a'}], [{'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[20,30](a&b)', 'G[2,10]-b'}]],
#     5: [[{'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[10,100](a&b)', 'F[100,100]-(a&b)'}, {'X[1](G[0,1]a)', '-X[2]a'}, {'G[20,30](a&b)', 'G[2,10]-b'} ], [{'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[20,30](a&b)', 'G[2,10]-b'}]],
#     6: [[{'G[10,100](a&b)', 'F[100,100]-(a&b)'}, {'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[20,30](a&b)', 'G[2,10]-b'},  {'X[1](G[0,1]a)', '-X[2]a'}], [{'F[100,100]-(a&b&c)', 'G[10,100](h&k)'}, {'G[20,30](a&b)', 'G[2,10]-b'}]],
    

# }
# @pytest.mark.parametrize(
#     "data", [value for _, value in inconsistencies_in_dnf.items()]
# )
# def test_1_dnf_inconsistencies_fix(data):
#     dnf = data[0]
#     expected_result = data[1]
#     incon = dict()
#     result = Inconsistencies.delete_inconsistent_sets(dnf, incon)
#     print(incon)
#     assert result == expected_result