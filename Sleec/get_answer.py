
from argparse import ArgumentParser
import os


if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument('--dir', help="output directory", type=str)    
    args = parser.parse_args()    
    path = "/home/mudathir/Desktop/LEGOS/Sleec/z3_quantifiers_results"
    files = [
        os.path.join(dp, f)
        for dp, _, filenames in os.walk(path)
        for f in filenames
        if os.path.splitext(f)[1] == ".smt2"
    ]
    
    (sat, unsat, unknown, error)  = (0,0,0, 0)    
    for file in files:        
      with open(file) as f:
        lines = f.readlines()
        answer = lines[1].strip()
        if answer == "sat":
          sat = sat + 1
        elif answer == "unsat":
          unsat = unsat + 1
        elif answer == "unknown":
          unknown = unknown + 1
        else:
          error = error + 1
        time = lines[-1].replace(":total-time","").replace(")", "").strip()
        print("{},{},{}".format(file, answer, time))

    print("{} : sat = {}, unsat = {}, unknown = {}, error = {}"
          .format(args.dir, sat, unsat, unknown, error))
