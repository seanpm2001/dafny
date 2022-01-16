using System;
using Antlr4.Runtime;

namespace SelfHosting.CSharp {
  public class SimpleVisitor : SimpleBaseVisitor<AST> {
    public override AST VisitSeq(SimpleParser.SeqContext context) {
      return new Seq(context.s.children.Select((s, _) => (Stmt)Visit(s)).ToList());
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

  public class ErrorListener : BaseErrorListener
  {
    public void SyntaxError(IRecognizer recognizer, int offendingSymbol, int line, int charPositionInLine, string msg, RecognitionException e)
    {
      Console.WriteLine("{0}: line {1}/column {2} {3}", e, line, charPositionInLine, msg);
    }
  }


  class Main {
    AST parse(string fname) {
      using (var fstream = new StreamReader(fname)) {
        var lexer = new SimpleLexer(new AntlrInputStream(fstream));
        var parser = new SimpleParser(new CommonTokenStream(lexer));

        // parser.RemoveErrorListeners();
        parser.AddErrorListener(new ErrorListener()); // add ours

        var visitor = new SimpleVisitor();
        return (Seq)visitor.Visit(parser.seq());
      }
    }

    void main() {
      var ast = parse("example");

    }
  }
}
