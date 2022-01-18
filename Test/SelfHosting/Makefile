cAST.cs.dfy: cAST.cs
	dotnet run --project ../../Source/Dafny/AST/ASTExport/ASTExport.csproj -- "$<" > "$@"

dAST.cs: dAST.dfy cAST.cs.dfy
	../../Binaries/Dafny /spillTargetCode:3 /noVerify $<

dll := bin/Debug/net6.0/SelfHosting.dll

$(dll): dAST.cs $(wildcard *.cs) $(wildcard *.g4)
	dotnet build

input := example.calc

run: $(dll) $(input)
	dotnet $^

# antlr4 -no-listener -visitor Simple.a4
