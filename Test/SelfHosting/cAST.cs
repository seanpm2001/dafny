namespace CSharpAST;

public class AST { } // ANTLR root

public class Expr : AST { }

public class Const : Expr {
  public int n;
  public Const(int n) {
    this.n = n;
  }
}

public class Add : Expr {
  public Expr e1, e2;

  public Add(Expr e1, Expr e2) {
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
