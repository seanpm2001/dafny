include "../CSharpDafnyAST.dfy"
include "../CSharpCompat.dfy"
include "../Library.dfy"

module {:extern "Microsoft.Dafny.Compilers.SelfHosting.CSharp"} CSharpDafnyCompiler {
  import System
  import CSharpDafnyAST
  import opened CSharpUtils
  import opened Microsoft.Dafny

  module AST {
    import opened Microsoft
    import C = CSharpDafnyAST

    datatype Tokd<T> =
      Tokd(tok: Boogie.IToken, val: T)

    // public class LiteralExpr : Expression
    datatype LiteralExpr =
      | LitBool(b: bool)
      | LitInt(i: int)
      | LitReal(r: real)
      | LitChar(c: string) // FIXME should this use a char?
      | LitString(s: string)

    datatype Expression =
      | LiteralExpr(lit: LiteralExpr)
      | InvalidExpr(msg: string)
      | UnsupportedExpr(expr: C.Expression)

    datatype Stmt =
      | PrintStmt(exprs: seq<Expression>)
      | InvalidStmt

    type BlockStmt = seq<Stmt>

    datatype Method = Method(methodBody: BlockStmt)

    datatype Program = Program(mainMethod: Method)
  }

  module Translator {
    import opened Lib
    import opened CSharpUtils
    import opened CSharpUtils.System
    import opened CSharpUtils.Microsoft
    import C = CSharpDafnyAST
    import D = AST

    // function method TranslateExpression(c: C.Expression) : D.Expression reads * {
    //   match c {
    //   case c: C.LiteralExpr =>
    //     match c.Value {
    //     case s: System.String =>
    //       var str := StringUtils.OfCString(s);
    //       match c {
    //       case c: C.CharLiteralExpr =>
    //         D.LiteralExpr(D.LitChar(str))
    //       case c: C.StringLiteralExpr =>
    //         D.LiteralExpr(D.LitString(str))
    //       case _ =>
    //         D.InvalidExpr("LiteralExpr with .Value of type string must be a char or a string.")
    //       }
    //     case _ => D.UnsupportedExpr(c)
    //     }
    //   case _ => D.UnsupportedExpr(c)
    //   }
    // }

    // function method TranslateExpression'(c: C.Expression) : D.Expression reads * {
    //   match c {
    //   | c: C.LiteralExpr =>
    //     match c.Value {
    //     | s: System.String =>
    //       var str := StringUtils.OfCString(s);
    //       match c {
    //       | c: C.CharLiteralExpr =>
    //         D.LiteralExpr(D.LitChar(str))
    //       | c: C.StringLiteralExpr =>
    //         D.LiteralExpr(D.LitString(str))
    //       | _ =>
    //         D.InvalidExpr("LiteralExpr with .Value of type string must be a char or a string.")
    //       }
    //     | _ => D.UnsupportedExpr(c)
    //     }
    //   | _ => D.UnsupportedExpr(c)
    //   }
    // }

    function method TranslateExpression(c: C.Expression) : D.Expression reads * {
      if c is C.LiteralExpr then
        var l: C.LiteralExpr := c as C.LiteralExpr;

        if l.Value is Bool then
          D.LiteralExpr(D.LitBool(TypeConv.AsBool(l.Value)))
        else if l.Value is Numerics.BigInteger then
          D.LiteralExpr(D.LitInt(TypeConv.AsInt(l.Value)))
        else if l.Value is BaseTypes.BigDec then
          D.LiteralExpr(D.LitReal(TypeConv.AsReal(l.Value))) // TODO test
        else if l.Value is String then
          var str := TypeConv.AsString(l.Value);
          if l is C.CharLiteralExpr then
            D.LiteralExpr(D.LitChar(str))
          else if l is C.StringLiteralExpr then
            D.LiteralExpr(D.LitString(str))
          else
            D.InvalidExpr("LiteralExpr with .Value of type string must be a char or a string.")
        else D.UnsupportedExpr(l)
      else D.UnsupportedExpr(c)
    }

    function method TranslateStatement(s: C.Statement) : D.Stmt reads * {
      if s is C.PrintStmt then
        var p := s as C.PrintStmt;
        D.PrintStmt(Seq.Map(TranslateExpression, ListUtils.ToSeq(p.Args)))
      else D.InvalidStmt
    }

    function method TranslateBlock(b: C.BlockStmt) : D.BlockStmt reads * {
      Seq.Map(TranslateStatement, ListUtils.ToSeq(b.Body))
    }

    function method TranslateMethod(m: C.Method) : D.Method reads * {
      D.Method(TranslateBlock(m.methodBody))
    }

    function method TranslateProgram(p: C.Program) : D.Program reads * {
      D.Program(TranslateMethod(p.MainMethod))
    }
  }

  module Target {
    import opened Lib.Datatypes

    datatype StrTree =
      | Str(s: string)
      | SepSeq(sep: Option<string>, asts: seq<StrTree>)
      | Invalid

    function method Seq(asts: seq<StrTree>) : StrTree {
      SepSeq(None, asts)
    }

    function method Concat(sep: string, asts: seq<StrTree>) : StrTree {
      SepSeq(Some(sep), asts)
    }

    function method Call(fn: string, args: seq<StrTree>) : StrTree {
      Seq([Str(fn), Str("("), Concat(", ", args), Str(")")])
    }

    function method SingleQuote(s: StrTree): StrTree {
      Seq([Str("'"), s, Str("'")])
    }

    function method DoubleQuote(s: StrTree): StrTree {
      Seq([Str("\""), s, Str("\"")])
    }
  }

  module Compiler {
    import Lib
    import opened AST
    import opened Target
    import opened Lib.Datatypes
    import opened CSharpUtils

    function method CompileInt(i: int) : StrTree {
      var istr := Lib.Str.of_int(i, 10);
      Call("new BigInteger", [Str(istr)])
    }

    function method CompileExpression(s: Expression) : StrTree {
      match s {
        case LiteralExpr(l) =>
          match l {
            case LitBool(b: bool) => Str(if b then "true" else "false")
            case LitInt(i: int) => CompileInt(i)
            case LitReal(r: real) =>
              var n, d := TypeConv.Numerator(r), TypeConv.Denominator(r);
              Call("new BigRational", [CompileInt(n), CompileInt(d)])
            case LitChar(c: string) => SingleQuote(Str(c))
            case LitString(s: string) => DoubleQuote(Str(s))
          }
        case InvalidExpr => Invalid
      }
    }

    function method CompilePrint(e: Expression) : StrTree {
      Seq([Call("DafnyRuntime.Helpers.Print", [CompileExpression(e)]), Str(";")])
    }

    function method CompileStmt(s: Stmt) : StrTree {
      match s {
        case PrintStmt(exprs) =>
          Concat("\n", Lib.Seq.Map(CompilePrint, exprs))
        case InvalidStmt => Invalid
      }
    }

    function method CompileMethod(m: Method) : StrTree {
      match m {
        case Method(methodBody) => Concat("\n", Lib.Seq.Map(CompileStmt, methodBody))
      }
    }

    function method CompileProgram(p: Program) : StrTree {
      match p {
        case Program(mainMethod) => CompileMethod(mainMethod)
      }
    }
  }

  method WriteAST(output: ConcreteSyntaxTree, ast: Target.StrTree) {
    match ast {
      case Str(s) =>
        output.Write(StringUtils.ToCString(s));
      case SepSeq(sep, asts) =>
        var i := 0;
        while i < |asts| {
          if i != 0 && sep.Some? {
            output.Write(StringUtils.ToCString(sep.t));
          }
          WriteAST(output, asts[i]);
          i := i + 1;
        }
      case Invalid =>
    }
  }

  class {:extern} DafnyCSharpCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyAST.Program,
                   output: ConcreteSyntaxTree) {
      var translated := Translator.TranslateProgram(dafnyProgram);
      var compiled := Compiler.CompileProgram(translated);
      WriteAST(output, compiled);
    }

    method EmitCallToMain(mainMethod: CSharpDafnyAST.Method,
                          baseName: System.String,
                          output: ConcreteSyntaxTree) {
    }
  }
}