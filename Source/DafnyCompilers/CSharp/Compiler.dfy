include "../CSharpDafnyAST.dfy"
include "../CSharpCompat.dfy"

// import opened CSharpSystem

module {:extern "Microsoft.Dafny.Compilers.SelfHosting.CSharp"} CSharpDafnyCompiler {
  import System
  import CSharpDafnyAST
  import opened Microsoft.Dafny

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyAST.Program, output: ConcreteSyntaxTree)
    {

    }

    method EmitCallToMain(mainMethod: CSharpDafnyAST.Method,
      baseName: System.String,
      output: ConcreteSyntaxTree) {
    }
  }
}
