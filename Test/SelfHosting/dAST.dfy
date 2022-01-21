include "CSharpCompat.dfy"
include "cAST.cs.dfy"
include "Utils.dfy"

module DafnyAST {
  datatype BinOp =
    | Add
    | Sub

  datatype Expr =
    | Const(n: int)
    | Op(op: BinOp, e1: Expr, e2: Expr)

  datatype Stmt =
    | Skip
    | Print(e: Expr)
    | Seq(s1: Stmt, s2: Stmt)

  function method interpExpr(e: Expr): int {
    match e {
      case Const(n) => n
      case Op(Add, e1, e2) => interpExpr(e1) + interpExpr(e2)
      case Op(Sub, e1, e2) => interpExpr(e1) - interpExpr(e2)
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
  import CSharpAST
  import DafnyAST
  import CSharpUtils
  import opened Global

  function method {:verify false} translateOp(op: CSharpAST.Op__BinOp) : DafnyAST.BinOp {
    if op.Equals(CSharpAST.Op__BinOp.Add) then DafnyAST.Add // FIXME: Equals because `==` gets miscompiled
    else if op.Equals(CSharpAST.Op__BinOp.Sub) then DafnyAST.Sub
    else unreachable<DafnyAST.BinOp>()
  }

  function method {:verify false} translateExpr(c: CSharpAST.Expr) : DafnyAST.Expr
    // TODO: Isn't there a way to assume termination for a function?
    reads *
  {
    if c is CSharpAST.Const then
      DafnyAST.Const((c as CSharpAST.Const).n)
    else if c is CSharpAST.Op then
      var c := c as CSharpAST.Op;
      DafnyAST.Op(translateOp(c.op), translateExpr(c.e1), translateExpr(c.e2))
    else
      // assume false;
      unreachable<DafnyAST.Expr>() /* TODO: How do I model this properly? */
  }

  import opened LinkedList

  function method {:verify false} translateStmt(c: CSharpAST.Stmt) : DafnyAST.Stmt
    reads *
  {
    if c is CSharpAST.Print then
      var e := translateExpr((c as CSharpAST.Print).e);
      DafnyAST.Print(e)
    else
      // assume false;
      unreachable<DafnyAST.Stmt>()
  }

  function method {:verify false} translateProg(c: CSharpAST.Prog) : DafnyAST.Stmt
    reads *
  {
    if c is CSharpAST.Prog then
      CSharpUtils.ListUtils.FoldR(
        (c, ds) => DafnyAST.Seq(translateStmt(c), ds),
        DafnyAST.Skip, (c as CSharpAST.Prog).s)
    else
      // assume false;
      unreachable<DafnyAST.Stmt>()
  }

  // function method cExpr2dExpr(e: cExpr) : DafnyAST.Expr
  //   reads e
  //   decreases *
  // {
  //   if e is CSharpAST.Const then
  //     DafnyAST.Const((e as CSharpAST.Const).n)
  //   else if e is CSharpAST.Add then
  //     DafnyAST.Add(cExpr2dExpr((e as CSharpAST.Add).e1), cExpr2dExpr((e as CSharpAST.Add).e2))
  //   else
  //     unreachable<DafnyAST.Expr>() /* How can I seal a trait? */
  // }
}

module Rewriter {
  import opened DafnyAST

  function method simplifyExpr(e: Expr) : Expr {
    match e {
      case Const(n) => e
      case Op(op, e1, e2) =>
        match (op, simplifyExpr(e1), simplifyExpr(e2)) {
          case (_, Const(0), Const(0)) => Const(0)
          case (Add, Const(0), e2) => e2
          case (Add, e1, Const(0)) => e1
          case (_, e1, e2) => Op(op, e1, e2)
        }
    }
  }

  function method simplifyStmt(s: Stmt) : Stmt {
    match s {
      case Skip => Skip
      case Print(e) => Print(simplifyExpr(e))
      case Seq(s1, s2) =>
        match (simplifyStmt(s1), simplifyStmt(s2)) {
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

  datatype Instr =
    | PushConst(n: int)
    | PopAdd
    | PopSub
    | PopPrint

  type Prog = List<Instr>
  datatype State = State(stack: List<int>, output: seq<int>)

  const EmptyState := State(Nil, []);

  function method interpInstr(instr: Instr, st: State) : State {
    match (instr, st.stack) {
      case (PushConst(n), tl) =>
        State(Cons(n, tl), st.output)
      case (PopAdd, Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 + n2, tl), st.output)
      case (PopSub, Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 - n2, tl), st.output)
      case (PopPrint, Cons(n, tl)) =>
        State(tl, st.output + [n])
      // Error cases
      case (PopAdd, _) => st
      case (PopSub, _) => st
      case (PopPrint, _) => st
    }
  }

  function method interpProg'(p: Prog, st: State) : State {
    match p {
      case Nil => st
      case Cons(instr, p) => interpInstr(instr, interpProg'(p, st))
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

  function method prettyPrintInstr(instr: Instr) : string {
    match instr {
      case PushConst(n) =>
        "PushConst(" + prettyPrintNum(n, "0") + ")"
      case PopAdd =>
        "PopAdd"
      case PopSub =>
        "PopSub"
      case Print =>
        "Print"
    }
  }

  function method prettyPrint(p: Prog) : List<string> {
    match p {
      case Nil => Nil
      case Cons(instr, p) => Cons(prettyPrintInstr(instr), prettyPrint(p))
    }
  }
}

module Compiler {
  import opened LinkedList

  import DafnyAST
  import opened StackMachine

  function method compileExpr(e: DafnyAST.Expr): Prog {
    match e {
      case Const(n) => Singleton(PushConst(n))
      case Op(Add, e1, e2) => Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1)))
      case Op(Sub, e1, e2) => Cons(PopSub, Concat(compileExpr(e2), compileExpr(e1)))
    }
  }

  function method compileStmt(s: DafnyAST.Stmt): Prog {
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

  lemma compileExprCorrect'(e: DafnyAST.Expr, st: State)
    ensures interpProg'(compileExpr(e), st) ==
            State(Cons(DafnyAST.interpExpr(e), st.stack), st.output)
  {
    match e {
      case Const(n) =>
      case Op(Add, e1, e2) =>
        calc {
          interpProg'(compileExpr(e), st);
          interpProg'(Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1))), st);
          interpInstr(PopAdd, interpProg'(Concat(compileExpr(e2), compileExpr(e1)), st));
          { interpProg'_Concat(compileExpr(e2), compileExpr(e1), st); }
          interpInstr(PopAdd, interpProg'(compileExpr(e2), interpProg'(compileExpr(e1), st)));
          // { compileExprCorrect'(e1, st); }
          // { compileExprCorrect'(e2, st); }
          // interpInstr(PopAdd, State(Cons(DafnyAST.interpExpr(e2), Cons(DafnyAST.interpExpr(e1), st.stack)),
          //   st.output));
          // State(Cons(DafnyAST.interpExpr(e1) + DafnyAST.interpExpr(e2), st.stack),
          //   st.output);
        }
      case Op(Sub, e1, e2) => // FIXME: Can this be made simpler?
        calc {
          interpProg'(compileExpr(e), st);
          interpProg'(Cons(PopSub, Concat(compileExpr(e2), compileExpr(e1))), st);
          interpInstr(PopSub, interpProg'(Concat(compileExpr(e2), compileExpr(e1)), st));
          { interpProg'_Concat(compileExpr(e2), compileExpr(e1), st); }
          interpInstr(PopSub, interpProg'(compileExpr(e2), interpProg'(compileExpr(e1), st)));
        }
    }
  }

  lemma compileStmtCorrect'(s: DafnyAST.Stmt, st: State)
    ensures interpProg'(compileStmt(s), st) ==
            State(st.stack, st.output + DafnyAST.interpStmt(s))
  {
    match s {
      case Skip =>
      case Print(e) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(DafnyAST.Print(e)), st);
          interpProg'(Cons(PopPrint, compileExpr(e)), st);
          interpInstr(PopPrint, interpProg'(compileExpr(e), st));
          { compileExprCorrect'(e, st); }
          interpInstr(PopPrint, State(Cons(DafnyAST.interpExpr(e), st.stack), st.output));
          State(st.stack, st.output + [DafnyAST.interpExpr(e)]);
        }
      case Seq(s1, s2) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(DafnyAST.Seq(s1, s2)), st);
          interpProg'(Concat(compileStmt(s2), compileStmt(s1)), st);
          { interpProg'_Concat(compileStmt(s2), compileStmt(s1), st); }
          interpProg'(compileStmt(s2), interpProg'(compileStmt(s1), st));
        }
    }
  }

  lemma compileStmtCorrect(s: DafnyAST.Stmt, st: State)
    ensures interpProg(compileStmt(s)) == DafnyAST.interpStmt(s)
  {
    compileStmtCorrect'(s, EmptyState);
  }
}

module {:extern "SelfHosting"} Interop {
  import LinkedList
  import CSharpAST
  import DafnyAST
  import StackMachine
  import Translator
  import Rewriter
  import Compiler
  import CSharpUtils
  import Generics = System.Collections.Generic

  class DafnyCompiler {
    static method CompileAndExport(cAST: CSharpAST.Prog)
      returns (output: Generics.List<string>)
    {
      var translated: DafnyAST.Stmt := Translator.translateProg(cAST);
      var optimized: DafnyAST.Stmt := Rewriter.simplifyStmt(translated);
      var compiled: StackMachine.Prog := Compiler.compileStmt(translated);
      var prettyPrinted: LinkedList.List<string> := StackMachine.prettyPrint(compiled);

      print "translated = \n  "; print translated; print "\n";
      print "optimized = \n  "; print optimized; print "\n";
      print "compiled = \n  "; print compiled; print "\n";

      print "";
      print "interp(translated) = \n  "; print DafnyAST.interpStmt(translated); print "\n";
      print "interp(optimized) = \n  "; print DafnyAST.interpStmt(optimized); print "\n";
      print "interp(compiled) = \n  "; print StackMachine.interpProg'(compiled, StackMachine.EmptyState).output; print "\n";

      output := CSharpUtils.ListUtils.Mk<string>();
      CSharpUtils.ListUtils.AppendSeq(output, LinkedList.ToSeq(prettyPrinted));
    }
  }
}
