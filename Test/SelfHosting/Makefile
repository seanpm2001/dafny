ASTExport = ../../Source/ASTExport
DafnyDriver = ../../Source/DafnyDriver/DafnyDriver

cAST.cs.dfy: SelfHosting.csproj cAST.cs $(ASTExport)/Program.cs
	dotnet run --project $(ASTExport)/ASTExport.csproj --\
		SelfHosting.csproj cAST.cs "SelfHosting.CSharpAST" "CSharpAST" > "$@"
	sed -i 's/import opened SelfHosting.CSharpAST//g' "$@"

CSharpCompat.dfy: ../../Source/DafnyCompilers/CSharpCompat.dfy
	cp "$<" "$@"

CSharpUtils.cs: ../../Source/DafnyCompilers/CSharpUtils.cs
	cp "$<" "$@"

dAST.cs: dAST.dfy CSharpCompat.dfy DafnyCompat.dfy cAST.cs.dfy
	dotnet run --project $(DafnyDriver).csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify $<
	sed -i 's/__AUTOGEN__//g' "$@"

dll := bin/Debug/net6.0/SelfHosting.dll

$(dll): dAST.cs CSharpUtils.cs $(wildcard *.cs) $(wildcard *.g4)
	dotnet build

input := example.calc

run: $(dll) $(input)
	dotnet $^

# ../Dafny.sln ../Dafny/DafnyPipeline.csproj ../Dafny/AST/DafnyAst.cs DafnyCSharpAST

# antlr4 -no-listener -visitor Simple.a4
