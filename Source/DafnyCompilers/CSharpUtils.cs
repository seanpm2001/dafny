using System.Numerics;

namespace CSharpUtils {
  public partial class ListUtils {
    public static List<T> Mk<T>() => new List<T>();

    public static void Append<T>(List<T> l, T t) => l.Add(t);

    public static B FoldL<A, B>(Func<B, A, B> f, B b0, List<A> lA) {
      for (int i = 0; i < lA.Count; i++) {
        b0 = f(b0, lA[i]);
      }
      return b0;
    }

    public static B FoldR<A, B>(Func<A, B, B> f, B b0, List<A> lA) {
      for (int i = lA.Count - 1; i >= 0; i--) {
        b0 = f(lA[i], b0);
      }
      return b0;
    }
  }

  public partial class StringUtils {
    public static string ToCString(DafnyRuntime.ISequence<char> s) {
      return s.ToString() ?? "null";
    }

    public static DafnyRuntime.ISequence<char> OfCString(string s) {
      return DafnyRuntime.Sequence<char>.FromString(s);
    }
  }

  public partial class TypeConv {
    public static readonly BigInteger ONE = new BigInteger(1);
    public static readonly BigInteger TEN = new BigInteger(10);

    public static bool AsBool(bool o) => o;

    public static System.Numerics.BigInteger AsInt(System.Numerics.BigInteger o) => o;

    public static DafnyRuntime.ISequence<char> AsString(System.String o) =>
      StringUtils.OfCString(o);

    public static BigInteger Numerator(DafnyRuntime.BigRational r) => r.num;
    public static BigInteger Denominator(DafnyRuntime.BigRational r) => r.den;
  }
}
