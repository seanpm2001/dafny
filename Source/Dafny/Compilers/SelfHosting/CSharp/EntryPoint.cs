using System.Collections.ObjectModel;

namespace Microsoft.Dafny.Compilers.SelfHosting.CSharp;

class Factory : Microsoft.Dafny.Compilers.Csharp.Factory {
  public override ICompiler CreateInstance(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    return new SelfHostingCsharpCompiler(this, reporter);
  }
}

internal class SelfHostingCSharpCompiler : SelfHostingCompiler {
  private readonly DafnyCSharpCompiler Compiler;

  public SelfHostingCSharpCompiler(Factory factory, ErrorReporter reporter)
    : base(factory, reporter) {
    Compiler = new DafnyCSharpCompiler();
  }

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    Compiler.Compile(dafnyProgram, output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    Compiler.EmitCallToMain(mainMethod, baseName, output);
  }
}