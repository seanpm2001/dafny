using Antlr4.Runtime;

namespace SelfHosting.CSharp;

public class SimpleVisitor : SimpleBaseVisitor<AST> {
  public override AST VisitProg(SimpleParser.ProgContext context) {
    return new Prog(context._s.Select((s, _) => (Stmt)Visit(s)).ToList());
  }

  public override AST VisitPrint(SimpleParser.PrintContext context) {
    return new Print((Expr)Visit(context.e));
  }

  public override AST VisitAdd(SimpleParser.AddContext context) {
    return new Add((Expr)Visit(context.l), (Expr)Visit(context.r));
  }

  public override AST VisitConst(SimpleParser.ConstContext context) {
    return new Const(int.Parse(context.c.Text));
  }
}

public class ErrorListener : BaseErrorListener {
  public void SyntaxError(
    IRecognizer recognizer, int offendingSymbol,
    int line, int charPositionInLine, string msg,
    RecognitionException e)
  {
    Console.WriteLine($"{e}:{line}:{charPositionInLine}: {msg}");
  }
}

class Program {
  private static AST parse(string fname) {
    using (var fstream = new StreamReader(fname)) {
      var lexer = new SimpleLexer(new AntlrInputStream(fstream));
      var parser = new SimpleParser(new CommonTokenStream(lexer));

      // parser.RemoveErrorListeners();
      parser.AddErrorListener(new ErrorListener()); // add ours

      var visitor = new SimpleVisitor();
      return (Prog)visitor.Visit(parser.prog());
    }
  }

  public static void Main(string[] args) {
    Console.WriteLine("# Step 1: Parse");
    var ast = (Prog)parse(args[0]);
    Console.WriteLine($"cAST =\n  {ast}");

    Console.WriteLine("\n# Step 2: Compile (using Dafny)");
    var pp = SelfHosting.DafnyCompiler.CompileAndExport(ast);

    Console.WriteLine("\n# Step 3: Print (using C#)");
    pp.ForEach(s => Console.WriteLine($"  {s}"));
  }
}
