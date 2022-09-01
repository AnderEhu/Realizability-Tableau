class AutomaticBenchMarkGenerator:

    def __init__(self):
        pass

    @staticmethod
    def automatic_benchmark(n_env, m_sys, sys_interval, realizable = True):
        sys_interval_str = "["+ str(sys_interval[0]) + ","+str(sys_interval[1])+"]"
        if realizable:
            path = "benchmarks/Automatic/Realizable/benchmark_"+str(n_env)+"_"+str(m_sys)+"_"+sys_interval_str+".txt"
        else:
            path = "benchmarks/Automatic/Unrealizable/benchmark_"+str(n_env)+"_"+str(m_sys)+"_"+sys_interval_str+".txt"
            
        f = open(path, "w")
        formula_i_left_part = "("
        for i in range(0, n_env):
            env_var = "p" + str(i) + "_e"            
            #formula_i_left_part = "(-" + env_var + " & " + always_env + ")"
            formula_i_left_part += env_var + " & "
        formula_i_left_part = formula_i_left_part[:-2] + ")"

        formula_i_right_part = "("
        for j in range(0, m_sys):
            sys_var = "s" + str(j)
            always_sys =  "G" + sys_interval_str + "(" + sys_var + ")"
            formula_i_right_part += always_sys + " & " 
        formula_i_right_part = formula_i_right_part[:-2] + ")"
        formula_i = formula_i_left_part + " -> "+ formula_i_right_part

        f.write(formula_i)
        
        if not realizable:
            formula_for_unrealizability = "F" + sys_interval_str + "(-" + sys_var + ")"
            f.write("\n")
            f.write(formula_for_unrealizability)

        f.close()



def create_file_with_automatic_benchmarks(n_env_list, m_sys_list, sys_interval_list):

    for n_env in range(1, n_env_list+1):
        for m_sys in range(1, m_sys_list+1):
            for sys_interval in sys_interval_list:
                AutomaticBenchMarkGenerator.automatic_benchmark(n_env, m_sys, sys_interval, realizable=True)
                AutomaticBenchMarkGenerator.automatic_benchmark(n_env, m_sys, sys_interval, realizable=False)




create_file_with_automatic_benchmarks(10, 10, [[1,10], [1,1000]])
        


