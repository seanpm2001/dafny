namespace SelfHosting.CSharpAST;

public class AST { } // ANTLR root

public class Expr : AST { }

public class Const : Expr {
  public int n;

  public Const(int n) {
    this.n = n;
  }
}

public class Op : Expr {
  public enum BinOp { Add, Sub }

  public BinOp op;
  public Expr e1, e2;

  public Op(BinOp op, Expr e1, Expr e2) {
    this.e1 = e1;
    this.e2 = e2;
  }
}


public class Stmt : AST { }

public class Print : Stmt {
  public Expr e;

  public Print(Expr e) {
    this.e = e;
  }
}


public class Prog : AST {
  public List<Stmt> s;

  public Prog(List<Stmt> s) {
    this.s = s;
  }
}
