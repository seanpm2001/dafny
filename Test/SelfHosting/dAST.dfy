module {:extern "SelfHosting.CSharp"} CSharp {
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
    var s1: Stmt
    var s2: Stmt
  }
}

module Dafny {
  datatype Expr =
    | Const(n: int)
    | Add(e1: Expr, e2: Expr)

  datatype Stmt =
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
      case Print(e) => [interpExpr(e)]
      case Seq(s1, s2) => interpStmt(s1) + interpStmt(s2)
    }
  }
}

module Conversion {
  import CSharp
  import Dafny

  method cExpr2dExpr(c: CSharp.Expr) returns (d: Dafny.Expr)
    decreases *
    // TODO: It would be nice to be able to use the function syntax.
    //       Isn't there a way to assume termination for a function?
  {
    if // TODO: What's the right way to write this, without having "as" cases everywhere?
    case c is CSharp.Const =>
      return Dafny.Const((c as CSharp.Const).n);
    case c is CSharp.Add =>
      var c := c as CSharp.Add;
      var d1 := cExpr2dExpr(c.e1);
      var d2 := cExpr2dExpr(c.e2);
      return Dafny.Add(d1, d2);
    case true =>
      // assume false;
      return unreachable<Dafny.Expr>(); /* TODO: How do I model this properly? */
  }

  method cStmt2dStmt(c: CSharp.Stmt) returns (d: Dafny.Stmt)
    decreases *
  {
    if
    case c is CSharp.Print =>
      var e := cExpr2dExpr((c as CSharp.Print).e);
      return Dafny.Print(e);
      case true =>
        // assume false;
        return unreachable<Dafny.Stmt>();
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

  function method unreachable<T>() : T
    requires false
  { match () {} }
}

module ASTTransforms {
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
      case Print(e) => Print(simplExpr(e))
    }
  }
}

module StackMachine {
  datatype Op =
    | PushConst(n: int)
    | PushAdd

  datatype List<T> =
    | Cons(hd: T, tl: List<T>)
    | Empty

  type Prog = List<Op>
  type State = List<int>

  function method interpOp(op: Op, st: State) : State {
    match (op, st) {
      case (PushConst(n), _) => Cons(n, st)
      case (PushAdd, Cons(n1, Cons(n2, st))) => Cons(n1 + n2, st)
    }
  }

  function method interpProg(p: Prog, st: State) : State {
    match p {
      case Empty => st
      case Cons(op, p) => interpProg(p, interpOp(op, st))
    }
  }
}

module Compile {
  import opened Dafny
  import opened StackMachine

  // function method compileExpr(e: Expr): Prog {
  //   match e {
  //     case Const(n) => [PushConst(n)]
  //     case Add(e1, e2) => compileExpr(e1) + compileExpr(e2)
  //   }
  // }

  // function method interpStmt(s: Stmt): seq<int> {
  //   match s {
  //     case Print(e) => [interpExpr(e)]
  //     case Seq(s1, s2) => interpStmt(s1) + interpStmt(s2)
  //   }
  // }
}
