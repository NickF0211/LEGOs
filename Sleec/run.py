import subprocess
import os
import ntpath

csv_file = open("relation.csv", 'w')
csv_file.write("file, mode, rule, result, duration\n")
csv_file.close()

modes = ["redundancy", "conflict", "concern"]
path = "../test_files_z3" # assuming current directory Sleec
files = [
    os.path.join(dp, f)
    for dp, _, filenames in os.walk(path)
    for f in filenames
    if os.path.splitext(f)[1] == ".sleec"
]
for file in files:
  for mode in modes:    
    dir, name = ntpath.split((file))
    name = name.replace(".sleec", "")
    path = "{}/{}/{}".format(os.getcwd(),dir, name)
    output_file = "{}/output_{}.txt".format(path, mode)
    command = "python3 sleec_z3.py --filename {} --analysis {}".format(file, mode)
    print(command)
    p = subprocess.run(["python3", "sleec_z3.py", "--filename", file, "--analysis",  mode],capture_output=True, text=True)    
    out = open(output_file, 'w')
    out.write(p.stdout)
    out.close()
