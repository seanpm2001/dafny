include "CSharpCompat.dfy"

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

  trait {:compile false} {:extern "Prog"} Prog {
    var s: CSharpGenerics.List<Stmt>
  }
}
