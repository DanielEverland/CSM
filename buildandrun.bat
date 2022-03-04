"%~dp0\bin\fslex\fslex.exe" "%~dp0\Task1Lexer.fsl" --unicode
"%~dp0\bin\fsyacc\fsyacc.exe" "%~dp0\Task1Parser.fsp" --module Task1Lexer
fsi.exe "%~dp0\Task1.fsx"
PAUSE