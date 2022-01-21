using System.Collections.ObjectModel;

namespace Microsoft.Dafny.Compilers.SelfHosting.CSharp;

public class Factory : Microsoft.Dafny.Compilers.Csharp.Factory {
  public override ICompiler CreateInstance(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    return new SelfHostingCSharpCompiler(this, reporter);
  }
}

internal class SelfHostingCSharpCompiler : SelfHostingCompiler {
  private readonly DafnyCSharpCompiler compiler;

  public SelfHostingCSharpCompiler(Factory factory, ErrorReporter reporter)
    : base(factory, reporter) {
    compiler = new DafnyCSharpCompiler();
  }

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    compiler.EmitCallToMain(mainMethod, baseName, output);
  }
}