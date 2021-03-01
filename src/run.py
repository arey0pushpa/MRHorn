#!/usr/bin/python3

import sys
import glob
import os
import re
import shutil
import subprocess
import hashlib
from pathlib import Path
from multiprocessing import Process
if len(sys.argv) != 2:
    print("Incorrect number of arguments. use -h for more help.")
    sys.exit(0)

if sys.argv[1] == "-h" or sys.argv[1] == "--help":
    print("./RunExperiments [-h] [cnf_instances_directory]")
    sys.exit(0)

inputpath = sys.argv[1]
heuristic = 4

print ("c Starting Experiments...")
#for dirpath, dirnames, filenames in os.walk(inputpath):
#for fname in filenames:
#fname = "../testdb/unsat_benchmarks/mulcom008.cnf"
#print("Input filename is: ", fname)
cnt = 0
#fff = os.path.splitext(fname)[0] + "_" + str(heuristic) + ".out"
fff = "res.out" 
print("FFF is: ", fff)
#f = dirpath + fname 
with open(fff, "w") as out:
    while cnt < 1000:
        cmd = ["./a.out", inputpath, str(heuristic)] 
        subprocess.call(cmd,stdout=out)
        cnt += 1

print ("c Experiments completed.")
