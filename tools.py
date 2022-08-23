#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed May 12 19:21:33 2021

@author: alephnoell
"""
from cmath import inf
import csv
from os import popen, remove
import sys
import time

#################################################
### ================= Tools ================= ###
#################################################

def ander_to_str(formula):
    """
        Ander's to_str function, used to convert atomic formulas
        to strings when translating from the list of lists format
        to a circuit.
    """
    if isinstance(formula, str):
        return formula
    elif len(formula) == 2:
        if formula[0] == "-":
            return  formula[0] + ander_to_str(formula[1])
        else:
            sub_str = ander_to_str(formula[1])
            if sub_str.startswith('-') and 'X' in formula[0]:
                return '-' + formula[0] + "(" + sub_str[1:] +")"
            else:
                return formula[0] + "(" + sub_str +")"
    else:
        leftFormula = ander_to_str(formula[1])
        rightFormula = ander_to_str(formula[2])
        res = "(" + leftFormula + ")" + formula[0] + "(" + rightFormula + ")"
        if len(formula) > 3:
            for f in formula[3:]:
                extra_formula =  ander_to_str(f)
                res = res + formula[0] + "(" + extra_formula + ")"

        return res


def execute_command(command):
    """
        Executes the Linux command given in the input string
        and returns the string with the output.
    """
    call = popen(command)
    output = call.read()
    call.close()
    return output

def call_solver(file_name, solver="depqbf"):
    """
        Calls a QBF solver (either depQBF or QuAbS) to solve the formula
        given the file whose name is provided.
    """
    if solver == "quabs":
        call_output = execute_command("./solvers/quabs/build/quabs" + " --partial-assignment " + file_name)
        #print("the call output is: {}".format(call_output))
        if call_output == "" or "dumped" in call_output:
            print("Error in QUABS!")
            return []
        split = call_output.split("r ")
        sat = split[1][:-1]
        if sat == "UNSAT":
            return []
        else:
            return [int(v) for v in split[0][2:-3].split(" ")]
    elif solver == "depqbf":
        call_output = execute_command("./solvers/quabs/build/qcir2qdimacs " + file_name + 
                                      " | depqbf --qdo")
        split = call_output.split("V ")
        split = split[1:]
        cert = [int(ass[:-2])for ass in split]
        return cert
    else:
        print("Other solvers not yet supported.")

def MiniSAT(file_name):
    res = execute_command("minisat " + file_name)
    if "UNSAT" in res:
        return "UNSAT"
    elif "SAT" in res:
        return "SAT"
    else:
        print("MiniSAT could not determine satisfiability. Printing trace:")
        print(res)
    
def BICA(pos_name, neg_name, C):
    """
        Calls the formula minimization tools BICA on the files with names pos_name
        and neg_name.
    """
    bica_output = execute_command("python3 ./solvers/bica/bica.py -d -vv {} {}".format(pos_name, neg_name))

    bica = open("bica_file.txt", "w")
    bica.write(bica_output)
    bica.close()
    bica = open("bica_file.txt", "r")
    essential_primes = []
    n_primes = 0
    primes_found = 0
    for i, line in enumerate(bica):
        if line.startswith("c1 primes found: "):
            primes_found = line.split(' ')[-1][:-1]
        if n_primes > 0:
            prime = line.split(" ")
            prime = prime[:-1]
            prime = [int(l) for l in prime]
            pi = []
            for l in prime:
                if l > 0:
                    pi.append(C.inverse_names[l])
                else:
                    pi.append("-" + C.inverse_names[abs(l)])
            essential_primes.append(set(pi))
            n_primes -= 1
        if line.startswith("p"):
            info = line.split(" ") # p dnf vars primes
            n_primes = int(info[3][:-1])    
    bica.close()
    remove("bica_file.txt")
    return essential_primes, primes_found    

def print_info_map(info):
    print("=========================== INFO ===========================\n")
    for key, value in info.items():
        print(">>", key, ": ", value, "\n")        
    print("=========================== INFO ===========================") 

def add_info(info, key, value):
    if isinstance(value, float):
        info[key] = round(value, 6)
    else:    
        info[key] = value


def analysis(method):
    def timed(*args, **kwargs):
        start_time = time.perf_counter()
        result = method(*args, **kwargs)
        end_time = time.perf_counter()
        total_time = float("{:.8f}".format(end_time - start_time))
        name = kwargs.get('log_name', method.__name__.upper())
        if 'log_time' in kwargs:
            if name in kwargs['log_time']:
                kwargs['log_time'][name] = float("{:.8f}".format(kwargs['log_time'][name] + total_time))
            else:
                kwargs['log_time'][name] = total_time
        return result
    return timed


def correct_bica_formula(formula):
    if isinstance(formula, str):
        if formula == 'True'  or  formula == '-False':
            return ['|', 'aux_var', ['-', 'aux_var']]
        elif formula == 'False' or formula == '-True':
            return ['&', 'aux_var', ['-', 'aux_var']]
        elif formula == "X[1]False":
            return ['-', 'X[1]True']
        elif formula[0] == "-" and len(formula) > 1:
            return ['-', formula[1:]]
        else:
            return formula
    elif len(formula) == 2:
        return  [formula[0], correct_bica_formula(formula[1])]
    else:
        assert len(formula) >= 3
        leftFormula = correct_bica_formula(formula[1])
        rightFormula = correct_bica_formula(formula[2])
        op = formula[0]
        res = [op, leftFormula, rightFormula]
        if len(formula) > 3:
            for f in formula[3:]:
                extra_formula =  correct_bica_formula(f)
                res.append(extra_formula)

        return res

def read_benchmark_file(path):
    with open(path, 'r') as f:
        lines = f.readlines()
        split_lines = split_formulas(lines)
    f.close()  
    return split_lines


def split_formulas(lines):

    I = list()
    G = list()
    C = list()
    
    for line in lines:
        if line == "\n" or line=="":
            continue
        line = line.replace("\n", "").replace(" ", "")
        if line == "InitialFormula":
            activate = "I"

        elif line == "SafetyFormula":
            activate = "G"

        elif line == "EnvironmentGlobalConstraints":
            activate = "C"
        else: 
            if activate == "I":
                I.append(line) 
            elif activate == "G":
                G.append(line)
            elif activate == "C":
                C.append(line)
            else:
            
                print("Error en la  line : ", line)

    return I, G, C