# Mini-Dafny

A baby brother to Microsoft’s Dafny, this mix of scala and python parsing generates verification 
conditions for programs written in a toy language IMP – these conditions are formatted as input 
to Z3, a state of the art theorem prover, to determine whether a program satisfies its 
postconditions (i.e. its specification).

Taken all together, this is a command line tool which can determine whether or not complex
IMP programs and algorithms satisfy their specifications and have no bugs, provided one is 
willing to write the preconditions, postconditions, and loop invariants.

# Install

~~~~
# mini-dafny relies on scala, z3, and python. On mac,
# brew is an easy way to get these installed
brew install scala
brew install z3

# clone the repo
git clone
cd Mini-Dafny
make
~~~~

# Usage

To check a file, run the following command.

~~~~
./mini-dafny file.imp
~~~~

The mini-dafny script calls a scala parser to turn the program into a formatted string.
If the program does not adhere to the IMP specification, the parser will throw an error
(see lang.txt, and the example files, for the IMP specification).

The string is built into a tree in python, converted to a list of guarded commands, and
finally transformed into a logical assertion called the 'weakest precondition' of the
program. This precondition is formatted as Z3 input.

Mini-dafny finally pipes the Z3 input to the Z3 theorem prover, which will spit out
whether or not the program is valid.  If the output is VALID, then the program will
satisfy its postcondition in every case.  If the output is INVALID, then the program
is incorrect (does not meet its specification).

# Examples

Read lang.txt if you want to write your own IMP programs. See the examples directory
for examples of programs.  The 'valid' subdirectory contains correct algorithms which
mini-dafny will report as valid, while the 'invalid' subdirectory contains buggy 
(but syntactically correct!) programs which mini-dafny will report as invalid.

Verification condition generation requires preconditions, post conditions, and loop
invariants in order to a) determine what, exactly, the correct program is 'supposed'
to do, and b) aid the verification condition generator in converting the program
to a logical statement.  Preconditions, postconditions, and invariants are written
in an assertion logic described in lang.txt, and a strong understanding of invariants
is needed in order to write correct and verifiable IMP programs.
