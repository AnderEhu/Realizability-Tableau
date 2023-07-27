import pytest
from Tableau.src.tableau import Tableau

from tools import read_benchmark_file


developair_benchmarks_path = {
    "benchmarks/Automatic/Realizable/benchmark_8_8_[1,10].txt",


}
@pytest.mark.parametrize(
    "path", developair_benchmarks_path
)

def test_tnf_overleaf(path):
    initial_formula, safety_formula, env_constraints = read_benchmark_file(path)
    tableau = Tableau(initial_formula, safety_formula, env_constraints)
    assert tableau.is_open