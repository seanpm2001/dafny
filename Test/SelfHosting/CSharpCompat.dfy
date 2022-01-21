module {:extern "System"} System {
  trait {:compile false} {:termination false} {:extern} IComparable {}
  class {:extern} Func<TArg, TRet>{}
  class {:extern} String {}

  module {:extern "System.Collections.Generic"} Collections.Generic {
    class {:extern} List<T> {}
    class {:extern} ISet<T> {}
    class {:extern} HashSet<T> {}
    class {:extern} Dictionary<TKey, TValue> {}
    class {:extern} Tuple2<T1, T2> {}
    class {:extern} Tuple3<T1, T2, T3> {}
  }
}

module {:extern "Microsoft.Dafny"} Dafny {
  class {:extern} FreshIdGenerator {}
  class {:extern} Graph<T> {}
  class {:extern} Translator {}
  class {:extern} VisibilityScope {}
}

module {:extern "Microsoft.Dafny.Resolver"} DafnyResolver {
  class {:extern} TypeConstraint {}
}

module {:extern "Microsoft.Boogie"} Boogie {
  trait {:compile false} {:extern} {:termination false} IToken {}
  class {:extern} ErrorReporter {}
  class {:extern} Expr {}
  class {:extern} Function {}
}

module {:extern "SelfHosting.CSharpUtils"} CSharpUtils {
  import opened System.Collections.Generic

  class ListUtils {
    static function method {:extern} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method {:extern} Mk<T>() returns (l: List<T>)
    static method {:extern} Append<T>(l: List<T>, t: T)

    static method AppendSeq<T>(l: List<T>, s:seq<T>) {
      var i := 0;
      while (i < |s|) {
        Append(l, s[i]);
        i := i + 1;
      }
    }
  }
}
