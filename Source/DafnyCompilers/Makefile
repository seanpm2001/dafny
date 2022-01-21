default: CSharp/Compiler.dfy.cs

ASTExport = ../ASTExport
DafnyPipeline = ../Dafny/DafnyPipeline
DafnyAST = ../Dafny/AST/DafnyAst

CSharpDafnyAST.dfy: Makefile $(DafnyPipeline).csproj $(DafnyAST).cs $(ASTExport)/Program.cs
	dotnet run --project $(ASTExport)/ASTExport.csproj -- \
		$(DafnyPipeline).csproj $(DafnyAST).cs "Microsoft.Dafny." "CSharpDafnyAST" > "$@"

%.dfy.cs: %.dfy CSharpCompat.dfy CSharpDafnyAST.dfy
	../../../../Binaries/Dafny /spillTargetCode:3 /compile:0 /noVerify $<
