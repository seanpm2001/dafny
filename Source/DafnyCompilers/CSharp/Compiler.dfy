include "../CSharpDafnyAST.dfy"
include "../CSharpCompat.dfy"

// import opened CSharpSystem

module {:extern "Microsoft.Dafny.Compilers.SelfHosting.CSharp"} CSharpCompiler {
  import opened Dafny
  import CSharpSystem
  import CSharpDafnyAST

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyAST.Program,
      output: ConcreteSyntaxTree)
    {

    }

    method EmitCallToMain(mainMethod: CSharpDafnyAST.Method,
      baseName: CSharpSystem.String,
      output: ConcreteSyntaxTree) {
    }
  }
}
