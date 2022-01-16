namespace SelfHosting.CSharp {
  public class Expr {}

  public class Const : Expr {
    public int n;
  }

  public class Add : Expr {
    public Expr e1, e2;
  }

  public class Stmt {}

  public class Print : Stmt {
    public Expr e;
  }
}
