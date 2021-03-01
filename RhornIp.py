#!/usr/bin/python

# Copyright (C) 2018
# Johannes Kepler University Linz, Austria
# Institute for Formal Models and Verification
# Armin Biere, Martina Seidl, Ankit Shukla

## [TODO]
# 1. Add better parsing.
# 2. Add error handling in the program. use ASSERT.
# 3. Pretty Printing:
#   -  Better printing of the eqn and solution.
#   -  More statistics
# 4. Add test cases.

# [START program]

# [START import]
# Import the linear solver wrapper
from __future__ import print_function
from ortools.sat.python import cp_model
from google.protobuf import text_format

import argparse
import itertools
import re
import os
import sys
import time
# [END import]


def ERR(mode, t, input_filename, line):
    if mode == 2:
        print_rline(input_filename, 0, 0, 0, 0, 0, 0)
        sys.exit(0)
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
        "-m",
        "--mode",
        type=int,
        default=1,
        help="Simple Run or Experimental mode. [1: Simple (default), 2: Experimental]",
    )

    # Execute the parse_args() method
    args = parser.parse_args()
    input_path = args.path
    mode = args.mode

    # Fetch filename
    if not input_path:
        print("Please specify the input file [-i filename].")
        sys.exit(0)
    input_filename = input_path.split("/")[-1]
    if mode == 1:
        print("Input filename: ", input_filename)
    # [END parsing_args]lines

    # Global variables
    input_horn_cls_count = 0
    p_line_seen = 0

    # [START solver]
    model = cp_model.CpModel()
    # [END solver]

    # [START parse_dimacs]
    if not os.path.exists(input_path):
        if mode == 2:
            print_rline(input_filename, 0, 0, 0, 0, 0, 0)
        else:
            print("File path {} does not exist.".format(input_path))
        sys.exit()
    with open(input_path) as cnf_file:
        for line in cnf_file:
            line = line.strip()
            if not line:
                if mode == 2:
                    continue
                else:
                    print("There is an empty line in the input file.")
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
                # [START variables]
                cvars = [bool("v_{}".format(i)) for i in range(no_of_vars)]
                x = [None] * no_of_vars
                c = []
                c_index = 0
                for i in range(no_of_vars):
                    x[i] = model.NewBoolVar("x_%i" % i)
                for j in range(no_of_cls):
                    c.append(model.NewBoolVar("c_%i" % j))
                # [END variables]
                # assert (solver.NumVariables() == no_of_vars, "Achtung!!")
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
                actual_constraints = []
                for val in constraints:
                    indx = abs(val) - 1
                    if val > 0:
                        actual_constraints.append(x[indx])
                    else:
                        actual_constraints.append(1 - x[indx])
                lhs = 0
                for ac in actual_constraints:
                    lhs = lhs + ac
                lin_eq = lhs <= (constraint_size - (c[c_index] * (constraint_size - 1)))
                # print ("The Linear eqn is: ", lin_eq)
                model.Add(lin_eq)
                c_index += 1
                # [END constraints]

    if no_of_cls != (c_index):
        ERR(mode, 4, input_filename, [0])
    if mode == 1:
        print("Number if vars: ", no_of_vars)
        print("Total no.of clauses: ", no_of_cls)
        print("All constraints are added.")
    if no_of_cls == 0:
        if mode == 1:
            print("Total clause count is 0. No work day :) ")
        else:
            print_rline(input_filename, no_of_vars, no_of_cls, 0, 0, 0, 0)
        sys.exit(0)
    if no_of_cls == input_horn_cls_count:
        if mode == 1:
            print("Every clause is already Horn. No work day :) ")
        else:
            print_rline(
                input_filename, no_of_vars, no_of_cls, input_horn_cls_count, 0, 0, 0
            )
        sys.exit(0)

    # [END parse_dimacs]

    # [START objective]
    obj_func = 0
    for i in c:
        obj_func = obj_func + i
    model.Maximize(obj_func)
    # [END objective]

    # [START solve]
    solver = cp_model.CpSolver()
    if mode == 1:
        print("Solving...")
    status = solver.Solve(model)
    # [END solve]

    # [START print_solution]
    if status == cp_model.OPTIMAL:
        maxcost = solver.ObjectiveValue()
        p_rhorn = (maxcost / no_of_cls) * 100
        if mode == 1:
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
            # [START advanced]
            print()
            print("Statistics")
            print("  - conflicts       : %i" % solver.NumConflicts())
            print("  - branches        : %i" % solver.NumBranches())
            print("  - wall time       : %f s" % solver.WallTime())
            # print('  - solutions found : %i' % solution_printer.solution_count())
            # [END advanced]
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

        # print('Printing the model: ')
        # for i in c:
        #    print(' ', i, '=', solver.Value(i))
    # [END print_solution]


if __name__ == "__main__":
    start_time = time.time()
    main()

# [END program]
