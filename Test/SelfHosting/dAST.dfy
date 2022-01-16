module {:extern "System.Collections.Generic"} CSharpGenerics {
  class {:extern "List"} List<T> {}
}

module {:extern "SelfHosting.CSharpListUtils"} CSharpListUtils {
  import opened CSharpGenerics
  function method {:extern "foldl"} foldl<A, B>(f: (B, A) -> B, b0: B, l: List<A>) : B

  method {:extern "Mk"} Mk<T>() returns (l: List<T>)
  method {:extern "Append"} Append<T>(l: List<T>, t: T)

  method AppendSeq<T>(l: List<T>, s:seq<T>) {
    var i := 0;
    while (i < |s|) {
      Append(l, s[i]);
      i := i + 1;
    }
  }
}

module {:extern "SelfHosting.CSharp"} CSharp {
  import CSharpGenerics

  trait {:compile false} {:extern "Expr"} Expr {}

  trait {:compile false} {:extern "Const"} Const extends Expr {
    var n: int
  }

  trait {:compile false} {:extern "Add"} Add extends Expr {
    var e1: Expr
    var e2: Expr
  }

  trait {:compile false} {:extern "Stmt"} Stmt {}

  trait {:compile false} {:extern "Print"} Print extends Stmt {
    var e: Expr
  }

  trait {:compile false} {:extern "Seq"} Seq extends Stmt {
    var s: CSharpGenerics.List<Stmt>
  }
}

module LinkedList {
  datatype List<T> =
    | Cons(hd: T, tl: List<T>)
    | Nil

  function method Singleton<T>(t: T) : List<T> {
    Cons(t, Nil)
  }

  function method Concat<T>(l1: List<T>, l2: List<T>) : List<T> {
    match l1 {
      case Nil => l2
      case Cons(h, t) => Cons(h, Concat<T>(t, l2))
    }
  }

  function method ToSeq<T>(l: List<T>) : seq<T> {
    match l {
      case Nil => []
      case Cons(h, t) => [h] + ToSeq(t)
    }
  }
}

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

module Global {
  function method unreachable<T>() : T
    requires false
  { match () {} }
}

module Translator {
  import CSharp
  import Dafny
  import CSharpListUtils
  import opened Global

  function method {:verify false} cExpr2dExpr(c: CSharp.Expr) : Dafny.Expr
    // TODO: It would be nice to be able to use the function syntax.
    //       Isn't there a way to assume termination for a function?
    reads *
  {
    if c is CSharp.Const then
      Dafny.Const((c as CSharp.Const).n)
    else if c is CSharp.Add then
      var c := c as CSharp.Add;
      Dafny.Add(cExpr2dExpr(c.e1), cExpr2dExpr(c.e2))
    else
      // assume false;
      unreachable<Dafny.Expr>() /* TODO: How do I model this properly? */
  }

  import opened LinkedList

  function method {:verify false} cStmt2dStmt(c: CSharp.Stmt) : Dafny.Stmt
    reads *
  {
    if c is CSharp.Seq then
      CSharpListUtils.foldl(
        (ds, c) => Dafny.Seq(cStmt2dStmt(c), ds),
        Dafny.Skip, (c as CSharp.Seq).s)
    else if c is CSharp.Print then
      var e := cExpr2dExpr((c as CSharp.Print).e);
      Dafny.Print(e)
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
    | PushAdd
    | Print

  type Prog = List<Op>
  datatype State = State(stack: List<int>, output: seq<int>)

  function method interpOp(op: Op, st: State) : State {
    match (op, st.stack) {
      case (PushConst(n), tl) =>
        State(Cons(n, tl), st.output)
      case (PushAdd, Cons(n1, Cons(n2, tl))) =>
        State(Cons(n1 + n2, tl), st.output)
      case (Print, Cons(n, _)) =>
        State(st.stack, st.output + [n])
      // Error cases
      case (PushAdd, _) => st
      case (Print, _) => st
    }
  }

  function method {:tailrecursive} interpProg(p: Prog, st: State) : State {
    match p {
      case Nil => st
      case Cons(op, p) => interpOp(op, interpProg(p, st))
    }
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
      case PushAdd =>
        "PushAdd"
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
      case Add(e1, e2) => Concat(compileExpr(e2), compileExpr(e1))
    }
  }

  function method compileStmt(s: Dafny.Stmt): Prog {
    match s {
      case Skip => Nil
      case Print(e) => Cons(Print, compileExpr(e))
      case Seq(s1, s2) => Concat(compileStmt(s2), compileStmt(s1))
    }
  }
}

module {:extern "SelfHosting.DafnyCompiler"} Interop {
  import LinkedList
  import CSharp
  import Dafny
  import StackMachine
  import Translator
  import Rewriter
  import Compiler
  import CSharpGenerics
  import CSharpListUtils

  method {:extern "CompileAndExport"} CompileAndExport(
    cAST: CSharp.Stmt,
    output: CSharpGenerics.List<string>
  ) {
    var translated: Dafny.Stmt := Translator.cStmt2dStmt(cAST);
    var optimized: Dafny.Stmt := Rewriter.simplStmt(translated);
    var compiled: StackMachine.Prog := Compiler.compileStmt(translated);
    var prettyPrinted: LinkedList.List<string> := StackMachine.prettyPrint(compiled);
    CSharpListUtils.AppendSeq(output, LinkedList.ToSeq(prettyPrinted));
  }
}
