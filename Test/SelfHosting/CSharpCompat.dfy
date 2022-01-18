module {:extern "System.Collections.Generic"} CSharpGenerics {
  class {:extern "List"} List<T> {}
}

module {:extern "SelfHosting.CSharpUtils"} CSharpUtils {
  import opened CSharpGenerics

  class ListUtils {
    static function method {:extern "FoldR"} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method {:extern "Mk"} Mk<T>() returns (l: List<T>)
    static method {:extern "Append"} Append<T>(l: List<T>, t: T)

    static method AppendSeq<T>(l: List<T>, s:seq<T>) {
      var i := 0;
      while (i < |s|) {
        Append(l, s[i]);
        i := i + 1;
      }
    }
  }
}
