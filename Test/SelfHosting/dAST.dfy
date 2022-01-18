include "CSharpCompat.dfy"
include "cAST.cs.dfy"
include "Utils.dfy"

module Dafny {
  datatype Expr =
    | Const(n: int)
    | Add(e1: Expr, e2: Expr)

  datatype Stmt =
    | Skip
    | Print(e: Expr)
    | Seq(s1: Stmt, s2: Stmt)

  function method interpExpr(e: Expr): int {
    match e {
      case Const(n) => n
      case Add(e1, e2) => interpExpr(e1) + interpExpr(e2)
    }
  }

  function method interpStmt(s: Stmt): seq<int> {
    match s {
      case Skip => []
      case Print(e) => [interpExpr(e)]
      case Seq(s1, s2) => interpStmt(s1) + interpStmt(s2)
    }
  }
}

module Translator {
  import CSharp
  import Dafny
  import CSharpUtils
  import opened Global

  function method {:verify false} translateExpr(c: CSharp.Expr) : Dafny.Expr
    // TODO: Isn't there a way to assume termination for a function?
    reads *
  {
    if c is CSharp.Const then
      Dafny.Const((c as CSharp.Const).n)
    else if c is CSharp.Add then
      var c := c as CSharp.Add;
      Dafny.Add(translateExpr(c.e1), translateExpr(c.e2))
    else
      // assume false;
      unreachable<Dafny.Expr>() /* TODO: How do I model this properly? */
  }

  import opened LinkedList

  function method {:verify false} translateStmt(c: CSharp.Stmt) : Dafny.Stmt
    reads *
  {
    if c is CSharp.Print then
      var e := translateExpr((c as CSharp.Print).e);
      Dafny.Print(e)
    else
      // assume false;
      unreachable<Dafny.Stmt>()
  }

  function method {:verify false} translateProg(c: CSharp.Prog) : Dafny.Stmt
    reads *
  {
    if c is CSharp.Prog then
      CSharpUtils.ListUtils.FoldR(
        (c, ds) => Dafny.Seq(translateStmt(c), ds),
        Dafny.Skip, (c as CSharp.Prog).s)
    else
      // assume false;
      unreachable<Dafny.Stmt>()
  }

  // function method cExpr2dExpr(e: cExpr) : Dafny.Expr
  //   reads e
  //   decreases *
  // {
  //   if e is CSharp.Const then
  //     Dafny.Const((e as CSharp.Const).n)
  //   else if e is CSharp.Add then
  //     Dafny.Add(cExpr2dExpr((e as CSharp.Add).e1), cExpr2dExpr((e as CSharp.Add).e2))
  //   else
  //     unreachable<Dafny.Expr>() /* How can I seal a trait? */
  // }
}

module Rewriter {
  import opened Dafny

  function method simplExpr(e: Expr) : Expr {
    match e {
      case Const(n: int) => e
      case Add(e1: Expr, e2: Expr) =>
        match (simplExpr(e1), simplExpr(e2)) {
          case (Const(0), Const(0)) => Const(0)
          case (Const(0), e2) => e2
          case (e1, Const(0)) => e1
          case (e1, e2) => Add(e1, e2)
        }
    }
  }

  function method simplStmt(s: Stmt) : Stmt {
    match s {
      case Skip => Skip
      case Print(e) => Print(simplExpr(e))
      case Seq(s1, s2) =>
        match (simplStmt(s1), simplStmt(s2)) {
          case (s1, Skip) => s1
          case (Skip, s2) => s2
          case (s1, s2) => Seq(s1, s2)
        }
    }
  }
}

module StackMachine {
  import opened LinkedList
  import opened Global

  datatype Op =
    | PushConst(n: int)
    | PopAdd
    | PopPrint

  type Prog = List<Op>
  datatype State = State(stack: List<int>, output: seq<int>)

  const EmptyState := State(Nil, []);

  function method interpOp(op: Op, st: State) : State {
    match (op, st.stack) {
      case (PushConst(n), tl) =>
        State(Cons(n, tl), st.output)
      case (PopAdd, Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 + n2, tl), st.output)
      case (PopPrint, Cons(n, tl)) =>
        State(tl, st.output + [n])
      // Error cases
      case (PopAdd, _) => st
      case (PopPrint, _) => st
    }
  }

  function method interpProg'(p: Prog, st: State) : State {
    match p {
      case Nil => st
      case Cons(op, p) => interpOp(op, interpProg'(p, st))
    }
  }

  function method interpProg(p: Prog) : seq<int> {
    interpProg'(p, EmptyState).output
  }

  function method prettyPrintDigit(n: int) : string
    requires 0 <= n < 10
  {
    match n {
      case 0 => "0"
      case 1 => "1"
      case 2 => "2"
      case 3 => "3"
      case 4 => "4"
      case 5 => "5"
      case 6 => "6"
      case 7 => "7"
      case 8 => "8"
      case 9 => "9"
    }
  }

  // FIXME: it's very confusing that adding parentheses around a decrease clause changes its meaning
  function method prettyPrintNum(n: int, zero: string) : string
    decreases n < 0, if n < 0 then -n else n
  {
    if n == 0 then
      zero
    else if n < 0 then
      prettyPrintNum(-n, zero)
    else if n < 10 then
      prettyPrintDigit(n)
    else if n >= 10 then
      prettyPrintNum(n / 10, "") + prettyPrintNum(n % 10, "0")
    else unreachable<string>()
  }

  function method prettyPrintOp(op: Op) : string {
    match op {
      case PushConst(n) =>
        "PushConst(" + prettyPrintNum(n, "0") + ")"
      case PopAdd =>
        "PopAdd"
      case Print =>
        "Print"
    }
  }

  function method prettyPrint(p: Prog) : List<string> {
    match p {
      case Nil => Nil
      case Cons(op, p) => Cons(prettyPrintOp(op), prettyPrint(p))
    }
  }
}

module Compiler {
  import opened LinkedList

  import Dafny
  import opened StackMachine

  function method compileExpr(e: Dafny.Expr): Prog {
    match e {
      case Const(n) => Singleton(PushConst(n))
      case Add(e1, e2) => Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1)))
    }
  }

  function method compileStmt(s: Dafny.Stmt): Prog {
    match s {
      case Skip => Nil
      case Print(e) => Cons(PopPrint, compileExpr(e))
      case Seq(s1, s2) => Concat(compileStmt(s2), compileStmt(s1))
    }
  }

  lemma interpProg'_Concat(p1: Prog, p2: Prog, st: State)
    ensures interpProg'(LinkedList.Concat(p1, p2), st) ==
            interpProg'(p1, interpProg'(p2, st))
  {}

  lemma compileExprCorrect'(e: Dafny.Expr, st: State)
    ensures interpProg'(compileExpr(e), st) ==
            State(Cons(Dafny.interpExpr(e), st.stack), st.output)
  {
    match e {
      case Const(n) =>
      case Add(e1, e2) =>
        calc {
          interpProg'(compileExpr(e), st);
          interpProg'(Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1))), st);
          interpOp(PopAdd, interpProg'(Concat(compileExpr(e2), compileExpr(e1)), st));
          { interpProg'_Concat(compileExpr(e2), compileExpr(e1), st); }
          interpOp(PopAdd, interpProg'(compileExpr(e2), interpProg'(compileExpr(e1), st)));
          { compileExprCorrect'(e1, st); }
        }
    }
  }

  lemma compileStmtCorrect'(s: Dafny.Stmt, st: State)
    ensures interpProg'(compileStmt(s), st) ==
            State(st.stack, st.output + Dafny.interpStmt(s))
  {
    match s {
      case Skip =>
      case Print(e) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(Dafny.Print(e)), st);
          interpProg'(Cons(PopPrint, compileExpr(e)), st);
          interpOp(PopPrint, interpProg'(compileExpr(e), st));
          { compileExprCorrect'(e, st); }
          interpOp(PopPrint, State(Cons(Dafny.interpExpr(e), st.stack), st.output));
          State(st.stack, st.output + [Dafny.interpExpr(e)]);
        }
      case Seq(s1, s2) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(Dafny.Seq(s1, s2)), st);
          interpProg'(Concat(compileStmt(s2), compileStmt(s1)), st);
          { interpProg'_Concat(compileStmt(s2), compileStmt(s1), st); }
          interpProg'(compileStmt(s2), interpProg'(compileStmt(s1), st));
        }
    }
  }

  lemma compileStmtCorrect(s: Dafny.Stmt, st: State)
    ensures interpProg(compileStmt(s)) == Dafny.interpStmt(s)
  {
    compileStmtCorrect'(s, EmptyState);
  }
}

module {:extern "SelfHosting"} Interop {
  import LinkedList
  import CSharp
  import Dafny
  import StackMachine
  import Translator
  import Rewriter
  import Compiler
  import CSharpGenerics
  import CSharpUtils

  class DafnyCompiler {
    static method CompileAndExport(cAST: CSharp.Prog)
      returns (output: CSharpGenerics.List<string>)
    {
      var translated: Dafny.Stmt := Translator.translateProg(cAST);
      var optimized: Dafny.Stmt := Rewriter.simplStmt(translated);
      var compiled: StackMachine.Prog := Compiler.compileStmt(translated);
      var prettyPrinted: LinkedList.List<string> := StackMachine.prettyPrint(compiled);

      print "translated = \n  "; print translated; print "\n";
      print "optimized = \n  "; print optimized; print "\n";
      print "compiled = \n  "; print compiled; print "\n";

      print "";
      print "interp(translated) = \n  "; print Dafny.interpStmt(translated); print "\n";
      print "interp(optimized) = \n  "; print Dafny.interpStmt(optimized); print "\n";
      print "interp(compiled) = \n  "; print StackMachine.interpProg'(compiled, StackMachine.EmptyState).output; print "\n";

      output := CSharpUtils.ListUtils.Mk<string>();
      CSharpUtils.ListUtils.AppendSeq(output, LinkedList.ToSeq(prettyPrinted));
    }
  }
}
