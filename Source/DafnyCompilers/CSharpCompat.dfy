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

module {:extern "CSharpUtils"} CSharpUtils {
  import System
  import opened System.Collections.Generic

  class {:extern} Tuple2<T1, T2> {}
  class {:extern} Tuple3<T1, T2, T3> {}

  class ListUtils {
    static function method {:extern} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method {:extern} Mk<T>() returns (l: List<T>)
    static method {:extern} Append<T>(l: List<T>, t: T)

    static function method {:extern} ToSeq<T>(l: List<T>) : seq<T> {
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
}
