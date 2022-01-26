module {:extern "System"} {:compile false} System {
  trait {:compile false} {:termination false} {:extern} IComparable {}
  class {:extern} {:compile false} Func<TArg, TRet>{}
  class {:extern} {:compile false} String {}
  class {:extern} {:compile false} Boolean {}
  class {:extern} {:compile false} ValueTuple {}

  module {:extern "System.Collections.Generic"} {:compile false} Collections.Generic {
    class {:extern} {:compile false} List<T> {}
    class {:extern} {:compile false} ISet<T> {}
    class {:extern} {:compile false} HashSet<T> {}
    class {:extern} {:compile false} Dictionary<TKey, TValue> {}
  }

  module {:extern "System.Numerics"} {:compile false} Numerics {
    class {:extern} {:compile false} BigInteger {}
  }
}

module {:extern "Microsoft.BaseTypes"} {:compile false} Microsoft.BaseTypes {
  class {:extern} {:compile false} BigDec {}
}

module {:extern "Microsoft.Dafny"} {:compile false} Microsoft.Dafny {
  import System

  class {:extern} {:compile false} FreshIdGenerator {}
  class {:extern} {:compile false} Graph<T> {}
  class {:extern} {:compile false} Translator {}
  class {:extern} {:compile false} VisibilityScope {}
  class {:extern} {:compile false} ErrorReporter {}

  class {:extern} {:compile false} Resolver {}
  class {:extern "Resolver.TypeConstraint"} Resolver__TypeConstraint {}

  class {:extern} {:compile false} ConcreteSyntaxTree {
    // Changed return type of methods returning `this` to void (we lose chaining
    // but stop Dafny from complaining about missing return parameters when we
    // don't chain).
    method {:extern} Write(value: System.String)
    method {:extern} WriteLine(value: System.String)
    method {:extern} NewBlock(header: System.String) returns (wr: ConcreteSyntaxTree)
  }
}

module {:extern "Microsoft.Boogie"} {:compile false} Microsoft.Boogie {
  trait {:compile false} {:extern} {:termination false} IToken {}
  class {:extern} {:compile false} ErrorReporter {}
  class {:extern} {:compile false} Expr {}
  class {:extern} {:compile false} Function {}
}

module {:extern "DafnyRuntime"} {:compile false} DafnyRuntime {
  class {:extern} {:compile false} BigRational {
    var num: int
    var den: int
  }
}

module {:extern "CSharpUtils"} CSharpUtils {
  import System
  import Microsoft
  import DafnyRuntime
  import opened System.Collections.Generic

  class {:extern} {:compile false} Tuple2<T1, T2> {}
  class {:extern} {:compile false} Tuple3<T1, T2, T3> {}

  class ListUtils {
    static function method {:extern} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method {:extern} Mk<T>() returns (l: List<T>)
    static method {:extern} Append<T>(l: List<T>, t: T)

    static function method ToSeq<T>(l: List<T>) : seq<T> {
      FoldR((t, s) => [t] + s, [], l)
    }

    static method AppendSeq<T>(l: List<T>, s:seq<T>) {
      var i := 0;
      while (i < |s|) {
        Append(l, s[i]);
        i := i + 1;
      }
    }
  }

  class StringUtils {
    static function method {:extern} ToCString(s: string) : System.String
    static function method {:extern} OfCString(s: System.String) : string
  }

  class SyntaxTreeAdapter {
    var wr: Microsoft.Dafny.ConcreteSyntaxTree

    constructor(wr: Microsoft.Dafny.ConcreteSyntaxTree) {
      this.wr := wr;
    }

    method Write(value: string) {
      wr.Write(StringUtils.ToCString(value));
    }

    method WriteLine(value: string) {
      wr.WriteLine(StringUtils.ToCString(value));
    }

    method NewBlock(header: string) returns (st': SyntaxTreeAdapter) {
      var wr' := wr.NewBlock(StringUtils.ToCString(header));
      st' := new SyntaxTreeAdapter(wr');
    }
  }

  class TypeConv {
    static function method {:extern}
      AsBool(o: System.Boolean) : bool
    static function method {:extern}
      AsInt(o: System.Numerics.BigInteger) : int
    static function method {:extern}
      AsReal(o: Microsoft.BaseTypes.BigDec) : real
    // static function method {:extern}
    //   BigDecNumerator(o: Microsoft.BaseTypes.BigDec) : int
    // static function method {:extern}
    //   BigDecDenominator(o: Microsoft.BaseTypes.BigDec) : int
    static function method {:extern}
      AsString(o: System.String) : string

    static function method {:extern} Numerator(r: real) : int
    static function method {:extern} Denominator(r: real) : int
  }
}
