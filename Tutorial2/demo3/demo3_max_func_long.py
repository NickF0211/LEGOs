import sys
from os.path import dirname, join

'''
we are going to go over the example on SRI-3 slide 48 here,
In addition, we are going to show the proof of FOL* UNSAT 

First thing, like before, we impoirt the FOL* interface
'''

sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from shortcut import *

'''
let's define the two classes of relational objects:

Class: Data(val: N)
Class: Fun(input:N, output:N)
'''

# this is the example for slides 48 in SRI-3
Data = create_action("Data", [("val", "int")])
Func = create_action("Func", [("input", "int"), ("output", "int")])



'''
C1a: forall every function, there exists an data that correspond to its input and a data correspond to its output
'''

add_constraint(forall(Func, lambda f: exists ([Data, Data], lambda d1, d2:
                      AND(EQ(d1.val, f.input),
                          EQ(d2.val, f.output)))
                      ))

'''
C1b: forall every function, its output is greater than its input

Note that we purposely split C1 in slides 48 into two constraints C1a and C1b, so that their usage for 
derving UNSAT (shown later) will be more clear
'''

add_constraint(forall(Func, lambda f: f.output > f.input))

'''
C2: There exists a data which is an upper-bound on the function's outputs
'''
add_constraint(exists(Data, lambda d: forall(Func, lambda f: d.val > f.output)))

'''
C3: Every data must be defined on Func
'''
add_constraint(forall(Data, lambda d: exists(Func, lambda f: EQ(f.input, d.val))))


'''
Let's try to solve the formula with proof production.
Action: run this python file
'''

solve(TRUE(), proof_mode=True)

'''
The proof is stored in "proof.txt", we can automatically check and trim the proof.
If the proof is successfully checked, a trimmed version will be store in "simple.txt".
In addition, an UNSAT core will be returned.
Let's talk a look at the UNSAT core
'''

UNSAT, _ = check_and_minimize("proof.txt", "simple.txt")
for r in UNSAT:
    print(r)

'''
Marsha 8:

Take a look at the UNSAT core:
Input || R2 || (forall p_Func_1 Func (p_Func_1_input < p_Func_1_output))
Input || R4 || (forall p_Data_1 Data (exists p_Func_3 Func (p_Func_3_input = p_Data_1_val)))
Input || R3 || (exists p_Data_0 Data (forall p_Func_2 Func (p_Func_2_output < p_Data_0_val)))

R1 wich correspond to C1a is not in UNSAT core, and it is not required for the derivation of UNSAT
'''

'''
Marsha 9:
You can inspect the trimmed proof (simple.txt) to see how the UNSAT is derived"

Input || R2 || (forall p_Func_1 Func (p_Func_1_input < p_Func_1_output))
Def || L4 || c2 <-> (forall p_Func_1 Func (p_Func_1_input < p_Func_1_output))
DeriveFact || F3 || c2 || L4 R2
Input || R3 || (exists p_Data_0 Data (forall p_Func_2 Func (p_Func_2_output < p_Data_0_val)))
Def || L6 || c3 <-> (exists p_Data_0 Data (forall p_Func_2 Func (p_Func_2_output < p_Data_0_val)))
DeriveFact || F4 || c3 || L6 R3
Input || R4 || (forall p_Data_1 Data (exists p_Func_3 Func (p_Func_3_input = p_Data_1_val)))
Def || L8 || c4 <-> (forall p_Data_1 Data (exists p_Func_3 Func (p_Func_3_input = p_Data_1_val)))
DeriveFact || F5 || c4 || L8 R4
DeriveLemma || EI L6  [p_Data_0:Data<-t_Data_0] || L9 || c3 -> (t_Data_0_presence & (forall p_Func_6 Func (p_Func_6_output < t_Data_0_val))) || L6
Def || L10 || c5 <-> (t_Data_0_presence & (forall p_Func_6 Func (p_Func_6_output < t_Data_0_val)))
DeriveFact || F8 || c3 -> c5 || L10 L9
AddFact || F10 || c6 <-> t_Data_0_presence
Def || L11 || c7 <-> (forall p_Func_6 Func (p_Func_6_output < t_Data_0_val))
DeriveFact || F12 || c5 -> (c6) || F10 L10
DeriveFact || F13 || c5 -> (c7) || L11 L10
DeriveLemma || UI L8  [p_Data_1:Data<-t_Data_0] || L12 || c4 -> ((! t_Data_0_presence) | (exists p_Func_8 Func (p_Func_8_input = t_Data_0_val))) || L8 L9
Def || L13 || c8 <-> ((! t_Data_0_presence) | (exists p_Func_8 Func (p_Func_8_input = t_Data_0_val)))
DeriveFact || F15 || c4 -> c8 || L13 L12
AddFact || F16 || c9 <-> (! t_Data_0_presence)
Def || L14 || c10 <-> (exists p_Func_8 Func (p_Func_8_input = t_Data_0_val))
DeriveLemma || EI L14  [p_Func_8:Func<-t_Func_3] || L15 || c10 -> (t_Func_3_presence & (t_Func_3_input = t_Data_0_val)) || L14
AddFact || F17 || c11 <-> (t_Func_3_presence & (t_Func_3_input = t_Data_0_val))
DeriveFact || F18 || c10 -> c11 || F17 L15
DeriveFact || F20 || c8 -> (c9 | c10) || F16 L14 L13
DeriveLemma || UI L4  [p_Func_1:Func<-t_Func_3] || L23 || c2 -> ((! t_Func_3_presence) | (t_Func_3_input < t_Func_3_output)) || L4 L15
AddFact || F32 || c19 <-> ((! t_Func_3_presence) | (t_Func_3_input < t_Func_3_output))
DeriveFact || F33 || c2 -> c19 || F32 L23
DeriveLemma || UI L11  [p_Func_6:Func<-t_Func_3] || L24 || c7 -> ((! t_Func_3_presence) | (t_Func_3_output < t_Data_0_val)) || L11 L15
AddFact || F34 || c20 <-> ((! t_Func_3_presence) | (t_Func_3_output < t_Data_0_val))
DeriveFact || F35 || c7 -> c20 || F34 L24
UNSAT || F34 F15 F18 F17 F32 F10 F12 F4 F3 F8 F5 F20 F13 F35 F16 F33
Vars || c4:Bool c9:Bool c2:Bool t_Data_0_presence:Bool t_Func_3_presence:Bool c5:Bool t_Data_1_presence:Bool t_Data_0_val:Int t_Data_2_presence:Bool c8:Bool c10:Bool c19:Bool t_Func_1_presence:Bool c11:Bool c6:Bool t_Func_0_presence:Bool c20:Bool t_Func_2_presence:Bool t_Func_3_input:Int c7:Bool t_Data_3_presence:Bool c3:Bool t_Func_3_output:Int
AXIOM || True

'''


