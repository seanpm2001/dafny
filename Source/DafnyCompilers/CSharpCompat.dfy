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

module {:extern "DafnyRuntime"} {:compile false} DafnyRuntime {
  class {:extern} {:compile false} BigRational {
    var num: int
    var den: int
  }
}

module {:extern "CSharpUtils"} CSharpUtils {
  import System
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

  class {:extern} StringUtils {
    static function method {:extern} ToCString(s: string) : System.String
    static function method {:extern} OfCString(s: System.String) : string
  }

  class {:extern} TypeConv {
    static function method {:extern} AsBool(o: System.Boolean) : bool
    static function method {:extern} AsInt(o: System.Numerics.BigInteger) : int
    static function method {:extern} AsString(o: System.String) : string

    static function method {:extern} Numerator(r: real) : int
    static function method {:extern} Denominator(r: real) : int
  }
}
