module {:extern "System"} {:compile false} System {
  trait {:compile false} {:termination false} {:extern} IComparable {}
  class {:extern} Func<TArg, TRet>{}
  class {:extern} String {}
  class {:extern} ValueTuple {}

  module {:extern "System.Collections.Generic"} {:compile false} Collections.Generic {
    class {:extern} List<T> {}
    class {:extern} ISet<T> {}
    class {:extern} HashSet<T> {}
    class {:extern} Dictionary<TKey, TValue> {}
  }

  module {:extern "System.Numerics"} {:compile false} Numerics {
    class {:extern} BigInteger {}
  }
}

module {:extern "Microsoft.BaseTypes"} {:compile false} Microsoft.BaseTypes {
  class {:extern} BigDec {}
}

module {:extern "Microsoft.Dafny"} {:compile false} Microsoft.Dafny {
  import System

  class {:extern} FreshIdGenerator {}
  class {:extern} Graph<T> {}
  class {:extern} Translator {}
  class {:extern} VisibilityScope {}
  class {:extern} ErrorReporter {}

  class {:extern} Resolver {}
  class {:extern "Resolver.TypeConstraint"} Resolver__TypeConstraint {}

  class {:extern} ConcreteSyntaxTree {
    // Changed return type to void (we lose chaining but stop Dafny from
    // complaining about missing return parameters when we don't chain.
    method {:extern} Write(value: System.String)
  }
}

module {:extern "Microsoft.Boogie"} {:compile false} Microsoft.Boogie {
  trait {:compile false} {:extern} {:termination false} IToken {}
  class {:extern} ErrorReporter {}
  class {:extern} Expr {}
  class {:extern} Function {}
}

module {:extern "DafnyRuntime"} {:compile false} DafnyRuntime {
  class {:extern} BigRational {
    var num: int
    var den: int
  }
}

module {:extern "CSharpUtils"} CSharpUtils {
  import System
  import Microsoft
  import DafnyRuntime
  import opened System.Collections.Generic

  class {:extern} Tuple2<T1, T2> {}
  class {:extern} Tuple3<T1, T2, T3> {}

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

  class {:extern "bool"} Bool {}

  class TypeConv {
    static function method {:extern}
      AsBool(o: Bool) : bool
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
