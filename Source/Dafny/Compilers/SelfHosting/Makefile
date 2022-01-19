default: CSharp/Compiler.dfy.cs

CSharpDafnyAST.dfy: ../../AST/DafnyAst.cs ../../AST/ASTExport/Program.cs
	dotnet run --project ../../AST/ASTExport/ASTExport.csproj -- "$<" "CSharpDafnyAST" > "$@"

%.dfy.cs: %.dfy CSharpCompat.dfy CSharpDafnyAST.dfy
	../../../../Binaries/Dafny /spillTargetCode:3 /compile:0 /noVerify $<
