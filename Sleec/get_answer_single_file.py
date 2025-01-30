
from argparse import ArgumentParser
import math
    
#file = "Sleec/cvc5_quantifiers_result.txt"
file = "Sleec/cvc5_quantifiers_result_mbqi.txt"

(sat, unsat, unknown, error)  = (0,0,0, 0)    
with open(file) as f:  
  while line := f.readline():
        line = line.strip()        
        if line == "unknown" or line == "unsat" or line == "sat":
           f.readline() # skip a line
           duration = f.readline().replace("real", "").strip()
           f.readline()
           f.readline()
           print("{},{}".format(line, duration))
        else:           
           print("timeout,20.00")
           f.readline()
           f.readline()
           f.readline()
           f.readline()
           f.readline()


  # for i in range(0, math.floor(len(lines)/5.0)):
  #   j = i * 5
  #   answer = lines[j].strip()
  #   duration = lines[j + 2].replace("real", "").strip()
  #   print("{},{}".format(answer, duration))
    
#   if answer == "sat":
#     sat = sat + 1
#   elif answer == "unsat":
#     unsat = unsat + 1
#   elif answer == "unknown":
#     unknown = unknown + 1
#   else:
#     error = error + 1
#   time = lines[-1].replace(":total-time","").replace(")", "").strip()
#   print("{},{},{}".format(file, answer, time))

# print("{} : sat = {}, unsat = {}, unknown = {}, error = {}"
#     .format(args.dir, sat, unsat, unknown, error))
