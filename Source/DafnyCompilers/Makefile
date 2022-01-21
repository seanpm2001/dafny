default: build

ASTExport = ../ASTExport
DafnyDriver = ../DafnyDriver/DafnyDriver
DafnyPipeline = ../Dafny/DafnyPipeline
DafnyAST = ../Dafny/AST/DafnyAst

CSharpDafnyAST.dfy: $(DafnyPipeline).csproj $(DafnyAST).cs $(ASTExport)/Program.cs
	dotnet run --project $(ASTExport)/ASTExport.csproj -- \
		$(DafnyPipeline).csproj $(DafnyAST).cs "Microsoft.Dafny" "CSharpDafnyAST" > "$@"

%.cs: %.dfy CSharpCompat.dfy CSharpDafnyAST.dfy
	dotnet run --project $(DafnyDriver).csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify $<
	sed -i 's/__AUTOGEN__//g' "$@"

CSharp/CSharpUtils.cs: CSharpUtils.cs
	cp $< $@

build: CSharp/Compiler.cs CSharp/CSharpUtils.cs
	dotnet build CSharp/CSharpCompiler.csproj
