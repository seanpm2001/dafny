using System;
using System.Collections.ObjectModel;
using System.IO;

namespace Microsoft.Dafny.Compilers.SelfHosting;

public abstract class SelfHostingCompiler : ICompiler {
  public CompilerFactory Factory { get; }
  public ErrorReporter Reporter;

  protected SelfHostingCompiler(CompilerFactory factory, ErrorReporter reporter) {
    Factory = factory;
    Reporter = reporter;
  }

  public abstract void Compile(Program dafnyProgram, ConcreteSyntaxTree output);

  public abstract void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output);

  public bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter,
    out object compilationResult) {
    throw new NotImplementedException();
  }

  public bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult,
    TextWriter outputWriter) {
    throw new NotImplementedException();
  }

  public virtual void WriteCoverageLegendFile() {}
}