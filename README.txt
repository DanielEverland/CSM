The program can be executed as stated in the documentation for the assignment: https://gitlab.gbar.dtu.dk/02141/mandatory-assignment/blob/master/getting-started-fs.md
We have used a .bat file to easily build and run the project. It requires a path setup to fsi.exe, has only been tested on Windows, and is expected to lie in the root of the project:
"%~dp0\bin\fslex\fslex.exe" "%~dp0\Task1Lexer.fsl" --unicode
"%~dp0\bin\fsyacc\fsyacc.exe" "%~dp0\Task1Parser.fsp" --module Task1Parser
fsi.exe "%~dp0\Task1.fsx"
PAUSE

The input expects a valid GCL program and will output a "pretty" parsed version of it. Here's an example:
Enter an input program: y:=1; do x>0 -> y:=x*y; x:=x-1 od
Result:
y := 1 ;
do x > 0 -> y := x * y ;
x := x - 1
od

If the program couldn't be parsed, an error message will be displayed, and the program will terminate:
Enter an input program: df
Couldn't parse program