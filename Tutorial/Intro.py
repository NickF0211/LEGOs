'''
In this very first tutorial, we will illustrate for to use the python interface to:
1. encode FOL* constraint (focus)
2. call LEGOS to solve constraint satisfiability
3. Check and trim the proof of UNSAT returned by LEGOS
'''

# input the interface
import sys
from os.path import dirname, join
sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
from shortcut import *

'''
Section 1: FOL* modelling
A FOL* model is defined by two parts: signature and constraints. 

The signature contains:
1. the declaration of types (int, bool or int with customized constraints)
2. the declaration of classes for relational objects
Intuitively, the declaration of classes define the attributes for different kind of
relational object, and the data type of attribute can be declared in the declaration of types
'''

'''
Section 1.1: declaration of type
There are three default types we support (you can use them without additional declaration):
nat: natural number
bool: Boolean
int: Integer

You can define your own data types as the follows
'''

# we can create a type with name "bounded int" that is bounded both from above and below
create_type("bounded_int", lower_bound=-100, upper_bound=100)

# We can also create a type with name "linear_int such that this integer always satisfy the linear constraint 2x+5 <0
create_type("cut_int", customized_func=lambda x: 2 * x + 5 < 0)

'''
Section 1.2: declaration of Class (of relational object)

FOL* allows you to define quantifiered expression over classes of relational object:
e.g., forall a: Class_A. p(a) 
Here, you can define the signature of each class, include:
1. name: str
2. attribute List[(attribute_name: str, attribute_data_type:str)] 
'''

# we can define a class Data with a single attribute value of type nat
Data = create_action("Data", [("value", "nat")])  # nat is a declared type

# we can also define a class Addition that adds two numbers together
Addition = create_action("Add", [("lhs", "int"), ("rhs", "int"), ("result", "int")])

# now, suppose we want to model an action of Study which contains the following information:

# 1. the student who studied, let's represent it with an ID (natural number)
create_type("ID", lower_bound=0)

# 2. the course being studied, let's represent it with the course id bounded from 0 to 100
create_type("courseID", upper_bound=100, lower_bound=0)

# 3. the time when the student starts to study, represented as nat
create_type("time", lower_bound=0)

# 4. the duration of the student, which also represent as a nat

# 5. If the student is studying alone, a boolean

Study = create_action("Study", [("student", "ID"), ("course", "courseID"), ("time", "time"),
                                ("duration", "nat"), ("alone", "bool")])


'''
Section 1.* extra tips (optional) 
With Classes being declared, you can create relational object of certain class and access its attributes
'''
study_1 = Study()
print(study_1.student)

# you can also fix some value while create the relational object, e.g., fix the student to be 0
study_2= Study(input_subs={"student": Int(0)})

# you can later use them in constructing FOL* rules

'''
Section 2: encode FOL* constraints 
In this part, we will show you how to encode constraints via examples
'''


'''
Basic usage, let's encode a constraint saying that every application of Addition (a Class declared in 1.2)
must be valid: lhs + rhs = result
we can encode the constraint in FOL*: forall a:Addition a.lhs + a.rhs = a.result
using the interface, we can use the construct, forall (Addition, func) 
where func is a function that takes a single relational object of Addition and output a FOL* formula
'''
add_constraint(forall(Addition, lambda a: EQ(a.lhs + a.rhs, a.result)))


'''
We can further adds a constraint saying that the there must exists a data that contains the 
lhs, rhs and result of every Addition
'''
add_constraint(forall(Addition, lambda a: exists(Data, lambda d: EQ(d.value, a.result))))
add_constraint(forall(Addition, lambda a: exists(Data, lambda d: EQ(d.value, a.lhs))))
add_constraint(forall(Addition, lambda a: exists(Data, lambda d: EQ(d.value, a.rhs))))


'''
We can add a constraint saying that every data must be applied either as LHS or RHS in some addition
'''
add_constraint(forall(Data, lambda d: exists(Addition, lambda a:
                                             OR(
                                                 EQ(a.lhs, d.value),
                                                 EQ(a.rhs, d.value)
                                             ))))

'''
We can add a constraint saying that there exists a data point that holds the maximum value among all data
'''

add_constraint(exists(Data, lambda data_max: forall(Data, lambda d:
                                                    data_max.value >= d.value
                                                    )))

'''
With all the constraints being defined, we can check the satisfiability of the constraints.
You can call solve(assumption) where assumption is some FOL* constraints that you would like to
assume 
'''

solve(TRUE())
print("*"*100)

'''
You probably see an uninteresting example, let's now saying that all Data must hold value greater than 0
'''

non_zero = forall(Data, lambda data: data.value > 0)
solve(non_zero)

'''
You will unsat, meaning there will not be a consistent domain of relational objects from class Addition and Data 
Satisfying the constraint.  In fact, we can ask the solver to print out the proof of UNSAT while solving with the argument:
proof_mode = True
'''

solve(non_zero, proof_mode=True)

'''
The proof will be written in the file "proof.txt", you can inspect the proof, but here we call an analyzer to analyze 
and trim the proof.
'''

UNSAT_core, _ = check_and_minimize("proof.txt", "simple_proof.txt")

'''
The UNSAT core is returned, and you can inspect what is in there
'''
for related in UNSAT_core:
    print(related)

'''
Between each call to the solver, you can manage the constraints that were previously added 
The constraints are stored in a global variable Constraints
e.g., we can clear all constraints
'''
Constraints.clear()


'''
We can also reset the signature that were previously defined with the comamnd clear(reset_signature=True)
'''
clear(reset_signature=True)

'''
This concludes the your very first tutorial on FOL*, feel free to navigate to other sections in this folder.

'''

