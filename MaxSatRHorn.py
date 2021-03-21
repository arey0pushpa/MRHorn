#!/usr/bin/env python3

# Copyright (C) 2018
# Johannes Kepler University Linz, Austria
# Institute for Formal Models and Verification
# Armin Biere, Martina Seidl, Ankit Shukla

# [Todo's]
# 1. Enforce the program to satisfy the larger clauses.
#    - Give incentive of satisfying larger clauses.
# 2. Improved parsing: 
#   - Avoid complete line grab. Do it one word at a time.
#   - Avoid loading whole list in a memory.
# 3. Improved Error handling.
#   - use enum and clearer interface
# 4. Add the Test cases for the code.
# 5. Add the LOG encoding 

# [START program]
# [START import]
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.card import *

import argparse
import itertools
import re
import os
import sys
import math
import time
import hashlib
import subprocess

# [END import]

def ERR(mode, t, input_filename, line):
    if mode == 2:
        print_rline(input_filename, 0, 0, 0, 0, 0, 0)
        sys.exit(0)
    elif mode == 3:
        print("E")
    else:
        if t == 1:
            sys.exit("Input File has multiple p lines! Exiting.")
        elif t == 2:
            print("Value Error due to input line.", line)
            sys.exit(
                "Value greater than the number of var. Input format error. Exiting."
            )
        elif t == 3:
            print("Value Error due to input line.", line)
            sys.exit("Value other than an integer. Input format error. Exiting.")
        elif t == 4:
            sys.exit(
                "Number of clauses are not same as in p line. Input format error. Exiting."
            )
        elif t == 5:
            sys.exit("No p line before a clause. Input format error. Exiting.")
        else:
            sys.exit(0)


def print_rline(
    input_filename,
    no_of_vars,
    no_of_cls,
    input_horn_cls_count,
    maxcost,
    p_rhorn,
    p_rincr_horn,
):
    rline = (
        input_filename
        + " "
        + str(no_of_vars)
        + " "
        + str(no_of_cls)
        + " "
        + str(input_horn_cls_count)
        + " "
        + str(maxcost)
        + " "
        + str("{0:.2f}".format(p_rhorn))
        + " "
        + str("{0:.2f}".format(p_rincr_horn))
        + " "
        + str("{0:.2f}".format(time.time() - start_time))
        
    )
    print(rline)


def horn_cls(cls):
    tmp = 0
    for l in cls:
        if l < 0:
            continue
        elif tmp >= 1:
            return 0
        else:
            tmp += 1
    return 1

def compute(input_path, encoding, mode, typee):
    # Pairwise ATMostOne Encoding. This will allow no new variable use for the encoding.
    # One to one mapping with the original input dimacs
    def pairwise_amo(varset, new_var):
        amo = []
        for i in range(len(varset)):
            for j in range(i + 1, len(varset)):
                wcnf_dimacs.append([new_var, -varset[i], -varset[j]])
        return 0

    # Linear AtMostOne Encoding Function: Commander Var
    def linear_amo(varset, new_var):
        vset_size = len(varset)
        cls_var = c_vars[-1]
        if vset_size <= 4:
            pairwise_amo(varset, cls_var)
            return new_var
        varset.reverse()
        l1 = varset.pop()
        l2 = varset.pop()
        l3 = varset.pop()
        pairwise_amo([l1, l2, l3], cls_var)
        # Commander variable constraint
        new_var += 1
        wcnf_dimacs.append([cls_var, -l1, new_var])
        wcnf_dimacs.append([cls_var, -l2, new_var])
        wcnf_dimacs.append([cls_var, -l3, new_var])
        # uep constraint
        wcnf_dimacs.append([cls_var, -new_var, l1, l2, l3])
        varset.append(new_var)
        return linear_amo(varset, new_var) 

    # Lograthemic (Bitwise) encoding of the AtMostOne constraints
    # Unfinished: buggy
    def bitwise_amo(varset, aux_var):      
        n = len(varset)
        aux_var += 1
        m = int (math.ceil(math.log(n,2)))
        log_varset = list(range(aux_var, aux_var + m + 1))
        cls_var = c_vars[-1]
        aux_var += m - 1
        for i in range(n):  
            for j in range(m):
                if (i & (1 << j)):
                    wcnf_dimacs.append([cls_var, -varset[i], log_varset[j]])
                else:
                    wcnf_dimacs.append([cls_var, -varset[i], -log_varset[j]]) 
        return aux_var

    # Filename input
    input_filename = input_path.split("/")[-1]
    hash_object = hashlib.md5(input_filename.encode())
    if mode == 1:
        print("c Input filename: ", input_filename)
        if encoding == 1:
            print ("c Encoding used for AMO: Binary Encoding")
        elif encoding == 2:
            print ("c Encoding used for AMO: LOG Encoding")
        else:
            print ("c Encoding used for AMO: Linear Encoding")

    # Global variables
    wcnf_dimacs = []
    input_horn_cls_count = 0
    p_line_seen = 0
    c_vars = []

    # [START parse_dimacs]
    if not os.path.exists(input_path):
        if mode == 2:
            print_rline(input_filename, 0, 0, 0, 0, 0, 0)
        if mode == 3:
            print("E")
        else:
            print("File path {} does not exist.".format(input_path))
        sys.exit()
    with open(input_path) as cnf_file:
        for line in cnf_file:
            line = line.strip()
            if not line:
                if (mode == 2 or mode == 3):
                    continue
                else:
                    print("There is an empty line in the input file. Ignoring.")
            elif line[0] == "c":
                continue
            elif line[0] == "p":
                if p_line_seen > 0:
                    ERR(mode, 1, input_filename, [0])
                else:
                    p_line_seen = 1
                # Extract the number of variables and initialize the graph with it
                no_of_vars = int(line.split()[2])
                no_of_cls = int(line.split()[3])
                aux_var = no_of_vars + 1
                # [START variables]
            else:
                if p_line_seen != 1:
                    ERR(mode, 5, input_filename, [0])
                # Take all integers in the line and remove the tralling zero
                constraints = []
                for lit in line.split():
                    try:
                        ilit = int(lit)
                        if ilit > no_of_vars:
                            ERR(mode, 2, input_filename, line)
                        constraints.append(ilit)
                    except ValueError:
                        ERR(mode, 3, input_filename, line)
                del constraints[-1]
                constraint_size = len(constraints)
                input_horn_cls_count += horn_cls(constraints)
                # [START constraints]
                # cnf = CardEnc.atmost(lits=constraints, encoding=EncType.pairwise)
                c_vars.append(aux_var)
                if encoding == 1:
                    pairwise_amo(constraints, aux_var)
                    aux_var += 1
                elif encoding == 2:
                    aux_var = bitwise_amo(constraints, aux_var)
                    aux_var += 1
                else:
                    aux_var = linear_amo(constraints, aux_var)
                    aux_var += 1
                # [END constraints]

    if no_of_cls != (len(c_vars)):
        ERR(mode, 4, input_filename, [0])
    if mode == 1:
        print("Number if vars: ", no_of_vars)
        print("Total no.of clauses: ", no_of_cls)
        print("Total horn clause count in input fml: ", input_horn_cls_count)
    if no_of_cls == 0:
        if mode == 1:
            print("Total clause count is 0. No work day :) ")
        elif mode == 3:
            print("S")
        else:
            print_rline(input_filename, no_of_vars, no_of_cls, 0, 0, 0, 0)
        sys.exit(0)
    if no_of_cls == input_horn_cls_count:
        if mode == 1:
            print("Every clause is already Horn. No work day :) ")
        elif mode == 3:
            print("S")
        else:
            print_rline(input_filename, no_of_vars, no_of_cls, input_horn_cls_count, 0, 0, 0)
        sys.exit(0)
    
    if (typee != 1):
        print("x "+ str(no_of_vars) +  ' ' + str(no_of_cls))

    # [END parse_dimacs] :

    # Choose the top value for the maxsat
    top = no_of_cls * 100

    # [START create wcnf file]
    #maxsat_path = "/tmp/" + hash_object.hexdigest() + ".wcnf"
    maxsat_path = "/tmp/" + input_filename + ".wcnf"
    #print (maxsat_path)
    #print ("No.of aux var: ", aux_var)
    with open(maxsat_path, "w") as out:
        out.write(
            "p wcnf "
            + str(aux_var - 1)
            + " "
            + str(len(wcnf_dimacs) + len(c_vars))
            + " "
            + str(top)
            + "\n"
        )
        for cls in wcnf_dimacs:
            out.write(str(top) + " ")
            for l in cls:
                out.write(str(l) + " ")
            out.write(str(0) + "\n")
        for lit in c_vars:
            out.write(str(1) + " " + str(-lit) + " " + str(0) + "\n")

    # [END wcnf file]

    # [START MAX-SAT]
    if (typee == 1): 
        wcnf = WCNF(from_file=maxsat_path)
    else:
        cmd1 = ["timeout", "20", "../Open-WBO-Inc/open-wbo-inc_static", "-no-complete", "-ca=1", "-c=100000", "-algorithm=6", maxsat_path]
        subprocess.call(cmd1)
    # [END MAX-SAT]

    if mode == 1:
        print ("Solving...\n")

    # [START print_solution]
    if (typee == 1):
        with RC2(wcnf) as rc2:
            opt_model = rc2.compute()
            maxcost = no_of_cls - rc2.cost
            p_rhorn = (maxcost / no_of_cls) * 100
            if mode == 1:
                print("The model is: ", opt_model)
                print("The Maximum cost is: ", maxcost)
                print("Percentage of RHorn in total: {0:.2f}".format(p_rhorn))
                print("Total no.of horn clauses in input fml: ", input_horn_cls_count)
            if input_horn_cls_count > 0:
                p_rincr_horn = (
                    (maxcost - input_horn_cls_count) / input_horn_cls_count
                ) * 100
            else:
                p_rincr_horn = 10000
            if mode == 1:
                print(
                    "Percenatge increase in Horn cls wrt input horn count: {0:.2f}".format(
                        p_rincr_horn
                    )
                )
                print("Program took in total: " + str("{0:.2f}".format(time.time() - start_time)) + " s")

            if mode == 2:
                print_rline(
                    input_filename,
                    no_of_vars,
                    no_of_cls,
                    input_horn_cls_count,
                    maxcost,
                    p_rhorn,
                    p_rincr_horn,
                )
            if (mode == 3):
                # take first number of clauses integers
                cls_model = opt_model[-no_of_cls:]
                print (str(cls_model)[1:-1])

            # for m in rc2.enumerate():
            #    print('model {0} has cost {1}'.format(m, rc2.cost))
        # [END print_solution]
        ## Try to delete the file ##
        try:
            print ("Nachoo...")
            # print ("c Deleting file: " + maxsat_path)
        #    os.remove(maxsat_path)
        except OSError as e:  ## if failed, report it back to the user ##
            print ("c Error: %s - %s." % (e.filename, e.strerror))


# [START main]
def main():
    # [START parsing_args]
    # Create the parser
    parser = argparse.ArgumentParser(
        description="List the command line input for the centrality measure"
    )

    # Add the arguments
    parser.add_argument(
        "-i", "--path", metavar="path", type=str, help="the path to input dimacs file"
    )
    parser.add_argument(
        "-e",
        "--encoding",
        type=int,
        default=1,
        help="At Most One-AMO encoding choice. [1: Quadratic (default), 2: Lograthemic, 3: Linear]",
    )
    parser.add_argument(
        "-m",
        "--mode",
        type=int,
        default=1,
        help="Simple Run or Experimental mode. [1: Simple (default), 2: Experimental, 3: Solver Mode]",
    )
    parser.add_argument(
        "-t", "--type", type=int, default = 1, help="Complete or incomplete MaxSAT Selection."
    )
    # Execute the parse_args() method
    args = parser.parse_args()
    input_path = args.path
    encoding = args.encoding
    mode = args.mode
    typee = args.type

    # Fetch filename
    if not input_path:
        if mode == 3:
            print("E") 
        else:
            print("Please specify the input file [-i filename].")
        sys.exit(0)
    # [END parsing_args]

    compute(input_path, encoding, mode, typee)
# [END MAIN]

if __name__ == "__main__":
    start_time = time.time()
    main()

# [END program]
