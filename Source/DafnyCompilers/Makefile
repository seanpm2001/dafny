default: build

ASTExport = ../ASTExport
DafnyDriver = ../DafnyDriver/DafnyDriver
DafnyPipeline = ../Dafny/DafnyPipeline
DafnyAST = ../Dafny/AST/DafnyAst
DafnyRuntime := ../DafnyRuntime/DafnyRuntime.cs

CSharpDafnyAST.dfy: $(DafnyPipeline).csproj $(DafnyAST).cs $(ASTExport)/Program.cs
	dotnet run --project $(ASTExport)/ASTExport.csproj -- \
		$(DafnyPipeline).csproj $(DafnyAST).cs "Microsoft.Dafny" "CSharpDafnyAST" > "$@"

%.cs: %.dfy CSharpCompat.dfy CSharpDafnyAST.dfy $(DafnyRuntime)
	dotnet run --project $(DafnyDriver).csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify $<
	sed -i 's/__AUTOGEN__//g' "$@"

CSharp/CSharpUtils.cs: CSharpUtils.cs
	cp $< $@

dll := CSharp/bin/Debug/net6.0/CSharpCompiler.dll

$(dll): CSharp/Compiler.cs CSharp/CSharpUtils.cs $(DafnyRuntime)
	dotnet build CSharp/CSharpCompiler.csproj

build: $(dll)

run: $(dll) $(DafnyRuntime)
	dotnet run --project ../DafnyDriver/DafnyDriver.csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify /compileTarget:$(dll) \
		minimal.dfy
