ASTExport = ../../Source/ASTExport

cAST.cs.dfy: Makefile SelfHosting.csproj cAST.cs $(ASTExport)/Program.cs
	dotnet run --project $(ASTExport)/ASTExport.csproj --\
		SelfHosting.csproj cAST.cs "SelfHosting.CSharpAST" "CSharpAST" > "$@"

CSharpCompat.dfy: ../../Source/DafnyCompilers/CSharpCompat.dfy
	cp "$<" "$@"

dAST.cs: dAST.dfy CSharpCompat.dfy cAST.cs.dfy
	../../Binaries/Dafny /spillTargetCode:3 /noVerify $<

dll := bin/Debug/net6.0/SelfHosting.dll

$(dll): dAST.cs $(wildcard *.cs) $(wildcard *.g4)
	dotnet build

input := example.calc

run: $(dll) $(input)
	dotnet $^

# ../Dafny.sln ../Dafny/DafnyPipeline.csproj ../Dafny/AST/DafnyAst.cs DafnyCSharpAST

# antlr4 -no-listener -visitor Simple.a4
