#!/usr/bin/python3

# TODO:
# 1. Handle STDERR during the subprocess call.

import sys
import glob
import subprocess
from subprocess import Popen, PIPE
import os
import re

if len(sys.argv) == 1:
    print("Incorrect number of arguments. use -h for more help.")
    sys.exit(0)

if sys.argv[1] == "-h" or sys.argv[1] == "--help":
    print("./RunExperiments [-h] [cnf_data_directory] [statistics_file] [type: IP=1, MAXSAT=2]")
    sys.exit(0)

if len(sys.argv) != 4:
    print("Incorrect number of arguments. use -h for more help.")
    sys.exit(0)

database = sys.argv[1]
stat_file = sys.argv[2]
ip_or_max = sys.argv[3]

with open(stat_file, "w") as out:
    out.write("filename pn pc hcount maxcost p_rhorn p_incrhorn timing\n")

with open(stat_file, "a") as out:
    if os.path.isfile(database):
        command_1 = ["timeout", "1200", "./RhornIp.py", "-i", database, "-m", "2"]
        command_2 = ["timeout", "1200", "./MaxSatRHorn.py", "-i", database, "-m", "2"]
        if ip_or_max == '1':  
            cmd = command_1
        else:
            cmd = command_2
        subprocess.call(cmd, stdout=out)
    else:
        for x in os.walk(database):
            for file in glob.glob(os.path.join(x[0], "*.cnf")):
                command_1 = ["timeout", "1200", "./RhornIp.py", "-i", file, "-m", "2"]
                command_2 = ["timeout", "1200", "./MaxSatRHorn.py", "-i", file, "-m", "2"]
                if ip_or_max == '1':  
                    cmd = command_1
                else:
                    cmd = command_2
                subprocess.call(cmd, stdout=out, stderr=subprocess.PIPE)                

"""
   ./RunExperiments.py ../cnfs/test/ RunTestIP.R 1             try:
                    proc = subprocess.run(command_1, stdout = out)
                except subprocess.CalledProcessError as error:
                    print("Exception:")
                    print("output : " + error.output)
                    print("stderr : " + error.stderr)

                proc = subprocess.Popen(command_1, stdout=out, stderr=subprocess.PIPE)
# subprocess.call(["./RhornIp.py", "-i", file, "-m", "2"], stdout=out, stderr=subprocess.PIPE)
# proc = subprocess.Popen(["./MaxSatRHorn.py", "-i", file, "-m", "2"], stdout=out, stderr=subprocess.PIPE)
# stdout, stderr = proc.communicate("this is some input")
# subprocess.call(["./MaxSatRHorn.py", "-i", file, "-m", "2"], stdout=out)
"""
