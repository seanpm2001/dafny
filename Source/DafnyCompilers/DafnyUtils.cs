using System.Numerics;

namespace DafnyUtils {
  public partial class TypeConv {
    public static readonly BigInteger ONE = new BigInteger(1);
    public static readonly BigInteger TEN = new BigInteger(10);

    public static DafnyRuntime.BigRational AsReal(Microsoft.BaseTypes.BigDec o) {
      if (o.Exponent >= 0) {
        return new DafnyRuntime.BigRational(o.Mantissa * BigInteger.Pow(TEN, o.Exponent), 1);
      } else {
        return new DafnyRuntime.BigRational(o.Mantissa, BigInteger.Pow(TEN, -o.Exponent));
      }
    }
  }
}
