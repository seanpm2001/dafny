#nullable enable
using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Reflection;

namespace Microsoft.Dafny;

public abstract class CompilerFactory {
  public abstract IReadOnlySet<string> SupportedExtensions { get; }

  public abstract string TargetLanguage { get; }
  public abstract string TargetExtension { get; }
  public virtual string Basename(string dafnyProgramName) => Path.GetFileNameWithoutExtension(dafnyProgramName);
  public virtual string TargetBaseDir(string baseName) => "";
  /// <summary>
  /// Transforms a legal file name (without extension or directory) into
  /// a legal class name in the target language
  /// </summary>
  public virtual string TransformToClassName(string baseName) => baseName;

  public abstract string PublicIdProtect(string name);
  public virtual string GetCompileName(bool isDefaultModule, string moduleName, string compileName) {
    return PublicIdProtect(moduleName) + "." + PublicIdProtect(compileName);
  }

  public virtual IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "ulong", "long" };

  public abstract bool TextualTargetIsExecutable { get; }
  public abstract bool SupportsInMemoryCompilation { get; }

  public virtual void CleanSourceDirectory(string pathsSourceDirectory) {
  }

  public abstract ICompiler CreateInstance(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames);

  public static CompilerFactory Load(string compileTarget) {
    // Start with built-in backends
    switch (compileTarget) {
      case "cs":
        return new Compilers.Csharp.Factory();
      case "js":
        return new Compilers.Js.Factory();
      case "go":
        return new Compilers.Go.Factory();
      case "java":
        return new Compilers.Java.Factory();
      case "py":
        return new Compilers.Python.Factory();
      case "cpp":
        return new Compilers.Cpp.Factory();
    }

    // Otherwise, load from disk
    if (!compileTarget.EndsWith(".dll")) {
      throw new ArgumentException($"Unknown /compileTarget: {compileTarget}");
    }

    var asm = Assembly.LoadFrom(compileTarget);
    var factoryType = asm.GetTypes().FirstOrDefault(t => t.IsAssignableTo(typeof(CompilerFactory)));
    if (factoryType == null) {
      var found = asm.GetTypes().Select(t => t.FullName);
      throw new ArgumentException($"Assembly does not contain a compiler factory class; found {String.Join(", ", found)}");
    }
    return (CompilerFactory?)Activator.CreateInstance(factoryType)
           ?? throw new ArgumentException("Could not instantiate the compiler factory class");
  }
}