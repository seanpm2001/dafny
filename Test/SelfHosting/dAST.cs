// Dafny program dAST.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.3.0.31104
// Command Line Options: /spillTargetCode:3 /noVerify dAST.dfy
// dAST.dfy


module LinkedList {
  datatype List<T> = Cons(hd: T, tl: List<T>) | Nil

  function method Singleton<T>(t: T): List<T>
  {
    Cons(t, Nil)
  }

  function method Concat<T>(l1: List<T>, l2: List<T>): List<T>
    decreases l1, l2
  {
    match l1 {
      case Nil() =>
        l2
      case Cons(h, t) =>
        Cons(h, Concat<T>(t, l2))
    }
  }

  function method ToSeq<T>(l: List<T>): seq<T>
    decreases l
  {
    match l {
      case Nil() =>
        []
      case Cons(h, t) =>
        [h] + ToSeq(t)
    }
  }
}

module {:extern ""SelfHosting.CSharp""} CSharp {

  import CSharpGenerics
  trait {:axiom} {:extern ""Expr""} Expr { }

  trait {:axiom} {:extern ""Const""} Const extends Expr {
    var n: int
  }

  trait {:axiom} {:extern ""Add""} Add extends Expr {
    var e1: Expr
    var e2: Expr
  }

  trait {:axiom} {:extern ""Stmt""} Stmt { }

  trait {:axiom} {:extern ""Print""} Print extends Stmt {
    var e: Expr
  }

  trait {:axiom} {:extern ""Prog""} Prog {
    var s: CSharpGenerics.List<Stmt>
  }
}

module Dafny {
  datatype Expr = Const(n: int) | Add(e1: Expr, e2: Expr)

  datatype Stmt = Skip | Print(e: Expr) | Seq(s1: Stmt, s2: Stmt)

  function method interpExpr(e: Expr): int
    decreases e
  {
    match e {
      case Const(n) =>
        n
      case Add(e1, e2) =>
        interpExpr(e1) + interpExpr(e2)
    }
  }

  function method interpStmt(s: Stmt): seq<int>
    decreases s
  {
    match s {
      case Skip() =>
        []
      case Print(e) =>
        [interpExpr(e)]
      case Seq(s1, s2) =>
        interpStmt(s1) + interpStmt(s2)
    }
  }
}

module Global {
  function method unreachable<T>(): T
    requires false
  {
    match () {
    }
  }
}

module Translator {

  import CSharp

  import Dafny

  import CSharpUtils

  import opened Global

  import opened LinkedList
  function method {:verify false} translateExpr(c: CSharp.Expr): Dafny.Expr
    reads *
    decreases {}, c
  {
    if c is CSharp.Const then
      Dafny.Const((c as CSharp.Const).n)
    else if c is CSharp.Add then
      var c: CSharp.Add := c as CSharp.Add;
      Dafny.Add(translateExpr(c.e1), translateExpr(c.e2))
    else
      unreachable<Dafny.Expr>()
  }

  function method {:verify false} translateStmt(c: CSharp.Stmt): Dafny.Stmt
    reads *
    decreases {}, c
  {
    if c is CSharp.Print then
      var e: Dafny.Expr := translateExpr((c as CSharp.Print).e);
      Dafny.Print(e)
    else
      unreachable<Dafny.Stmt>()
  }

  function method {:verify false} translateProg(c: CSharp.Prog): Dafny.Stmt
    reads *
    decreases {}, c
  {
    if c is CSharp.Prog then
      CSharpUtils.ListUtils.FoldR((c: Stmt, ds: Dafny.Stmt) => Dafny.Seq(translateStmt(c), ds), Dafny.Skip, (c as CSharp.Prog).s)
    else
      unreachable<Dafny.Stmt>()
  }
}

module Rewriter {

  import opened Dafny
  function method simplExpr(e: Expr): Expr
    decreases e
  {
    match e {
      case Const(n) =>
        e
      case Add(e1, e2) =>
        match (simplExpr(e1), simplExpr(e2)) {
          case (Const(0), Const(0)) =>
            Const(0)
          case (Const(0), e2) =>
            e2
          case (e1, Const(0)) =>
            e1
          case (e1, e2) =>
            Add(e1, e2)
        }
    }
  }

  function method simplStmt(s: Stmt): Stmt
    decreases s
  {
    match s {
      case Skip() =>
        Skip
      case Print(e) =>
        Print(simplExpr(e))
      case Seq(s1, s2) =>
        match (simplStmt(s1), simplStmt(s2)) {
          case (s1, Skip) =>
            s1
          case (Skip, s2) =>
            s2
          case (s1, s2) =>
            Seq(s1, s2)
        }
    }
  }
}

module StackMachine {

  import opened LinkedList

  import opened Global
  datatype Op = PushConst(n: int) | PopAdd | PopPrint

  type Prog = List<Op>

  datatype State = State(stack: List<int>, output: seq<int>)

  const EmptyState := State(Nil, [])

  function method interpOp(op: Op, st: State): State
    decreases op, st
  {
    match (op, st.stack) {
      case (PushConst(n), tl) =>
        State(Cons(n, tl), st.output)
      case (PopAdd(), Cons(n2, Cons(n1, tl))) =>
        State(Cons(n1 + n2, tl), st.output)
      case (PopPrint(), Cons(n, tl)) =>
        State(tl, st.output + [n])
      case (PopAdd(), _v0) =>
        st
      case (PopPrint(), _v1) =>
        st
    }
  }

  function method interpProg'(p: Prog, st: State): State
    decreases p, st
  {
    match p {
      case Nil() =>
        st
      case Cons(op, p) =>
        interpOp(op, interpProg'(p, st))
    }
  }

  function method interpProg(p: Prog): seq<int>
    decreases p
  {
    interpProg'(p, EmptyState).output
  }

  function method prettyPrintDigit(n: int): string
    requires 0 <= n < 10
    decreases n
  {
    match n {
      case 0 =>
        ""0""
      case 1 =>
        ""1""
      case 2 =>
        ""2""
      case 3 =>
        ""3""
      case 4 =>
        ""4""
      case 5 =>
        ""5""
      case 6 =>
        ""6""
      case 7 =>
        ""7""
      case 8 =>
        ""8""
      case 9 =>
        ""9""
    }
  }

  function method prettyPrintNum(n: int, zero: string): string
    decreases n < 0, if n < 0 then -n else n
  {
    if n == 0 then
      zero
    else if n < 0 then
      prettyPrintNum(-n, zero)
    else if n < 10 then
      prettyPrintDigit(n)
    else if n >= 10 then
      prettyPrintNum(n / 10, """") + prettyPrintNum(n % 10, ""0"")
    else
      unreachable<string>()
  }

  function method prettyPrintOp(op: Op): string
    decreases op
  {
    match op {
      case PushConst(n) =>
        ""PushConst("" + prettyPrintNum(n, ""0"") + "")""
      case PopAdd() =>
        ""PopAdd""
      case Print =>
        ""Print""
    }
  }

  function method prettyPrint(p: Prog): List<string>
    decreases p
  {
    match p {
      case Nil() =>
        Nil
      case Cons(op, p) =>
        Cons(prettyPrintOp(op), prettyPrint(p))
    }
  }
}

module Compiler {

  import opened LinkedList

  import Dafny

  import opened StackMachine
  function method compileExpr(e: Dafny.Expr): Prog
    decreases e
  {
    match e {
      case Const(n) =>
        Singleton(PushConst(n))
      case Add(e1, e2) =>
        Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1)))
    }
  }

  function method compileStmt(s: Dafny.Stmt): Prog
    decreases s
  {
    match s {
      case Skip() =>
        Nil
      case Print(e) =>
        Cons(PopPrint, compileExpr(e))
      case Seq(s1, s2) =>
        Concat(compileStmt(s2), compileStmt(s1))
    }
  }

  lemma /*{:_induction p1, p2, st}*/ interpProg'_Concat(p1: Prog, p2: Prog, st: State)
    ensures interpProg'(LinkedList.Concat(p1, p2), st) == interpProg'(p1, interpProg'(p2, st))
    decreases p1, p2, st
  {
  }

  lemma /*{:_induction e, st}*/ compileExprCorrect'(e: Dafny.Expr, st: State)
    ensures interpProg'(compileExpr(e), st) == State(Cons(Dafny.interpExpr(e), st.stack), st.output)
    decreases e, st
  {
    match e {
      case {:split false} Const(n) =>
      case {:split false} Add(e1, e2) =>
        calc {
          interpProg'(compileExpr(e), st);
          interpProg'(Cons(PopAdd, Concat(compileExpr(e2), compileExpr(e1))), st);
          interpOp(PopAdd, interpProg'(Concat(compileExpr(e2), compileExpr(e1)), st));
          {
            interpProg'_Concat(compileExpr(e2), compileExpr(e1), st);
          }
          interpOp(PopAdd, interpProg'(compileExpr(e2), interpProg'(compileExpr(e1), st)));
          {
            compileExprCorrect'(e1, st);
          }
        }
    }
  }

  lemma /*{:_induction s, st}*/ compileStmtCorrect'(s: Dafny.Stmt, st: State)
    ensures interpProg'(compileStmt(s), st) == State(st.stack, st.output + Dafny.interpStmt(s))
    decreases s, st
  {
    match s {
      case {:split false} Skip() =>
      case {:split false} Print(e) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(Dafny.Print(e)), st);
          interpProg'(Cons(PopPrint, compileExpr(e)), st);
          interpOp(PopPrint, interpProg'(compileExpr(e), st));
          {
            compileExprCorrect'(e, st);
          }
          interpOp(PopPrint, State(Cons(Dafny.interpExpr(e), st.stack), st.output));
          State(st.stack, st.output + [Dafny.interpExpr(e)]);
        }
      case {:split false} Seq(s1, s2) =>
        calc {
          interpProg'(compileStmt(s), st);
          interpProg'(compileStmt(Dafny.Seq(s1, s2)), st);
          interpProg'(Concat(compileStmt(s2), compileStmt(s1)), st);
          {
            interpProg'_Concat(compileStmt(s2), compileStmt(s1), st);
          }
          interpProg'(compileStmt(s2), interpProg'(compileStmt(s1), st));
        }
    }
  }

  lemma /*{:_induction s}*/ compileStmtCorrect(s: Dafny.Stmt, st: State)
    ensures interpProg(compileStmt(s)) == Dafny.interpStmt(s)
    decreases s, st
  {
    compileStmtCorrect'(s, EmptyState);
  }
}

module {:extern ""SelfHosting""} Interop {

  import LinkedList

  import CSharp

  import Dafny

  import StackMachine

  import Translator

  import Rewriter

  import Compiler

  import CSharpGenerics

  import CSharpUtils
  class DafnyCompiler {
    static method CompileAndExport(cAST: CSharp.Prog) returns (output: CSharpGenerics.List<string>)
      decreases cAST
    {
      var translated: Dafny.Stmt := Translator.translateProg(cAST);
      var optimized: Dafny.Stmt := Rewriter.simplStmt(translated);
      var compiled: StackMachine.Prog := Compiler.compileStmt(translated);
      var prettyPrinted: LinkedList.List<string> := StackMachine.prettyPrint(compiled);
      print ""translated = \n  "";
      print translated;
      print ""\n"";
      print ""optimized = \n  "";
      print optimized;
      print ""\n"";
      print ""compiled = \n  "";
      print compiled;
      print ""\n"";
      print """";
      print ""interp(translated) = \n  "";
      print Dafny.interpStmt(translated);
      print ""\n"";
      print ""interp(optimized) = \n  "";
      print Dafny.interpStmt(optimized);
      print ""\n"";
      print ""interp(compiled) = \n  "";
      print StackMachine.interpProg'(compiled, StackMachine.EmptyState).output;
      print ""\n"";
      output := CSharpUtils.ListUtils.Mk<string>();
      CSharpUtils.ListUtils.AppendSeq(output, LinkedList.ToSeq(prettyPrinted));
    }
  }
}

module {:extern ""System.Collections.Generic""} CSharpGenerics {
  class {:extern ""List""} List<T> { }
}

module {:extern ""SelfHosting.CSharpUtils""} CSharpUtils {

  import opened CSharpGenerics
  class ListUtils {
    static function method {:extern ""FoldR""} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>): B
      decreases l

    static method {:extern ""Mk""} Mk<T>() returns (l: List<T>)

    static method {:extern ""Append""} Append<T>(l: List<T>, t: T)
      decreases l

    static method AppendSeq<T>(l: List<T>, s: seq<T>)
      decreases l, s
    {
      var i := 0;
      while i < |s|
        decreases |s| - i
      {
        Append(l, s[i]);
        i := i + 1;
      }
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>();
      var toVisit = new Stack<ISequence<T>>();
      toVisit.Push(right);
      toVisit.Push(left);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        var cs = seq as ConcatSequence<T>;
        if (cs != null && cs.elmts.IsDefault) {
          toVisit.Push(cs.right);
          toVisit.Push(cs.left);
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
namespace _System {


  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }







} // end of namespace _System
namespace LinkedList_Compile {

  public interface _IList<T> {
    bool is_Cons { get; }
    bool is_Nil { get; }
    T dtor_hd { get; }
    LinkedList_Compile._IList<T> dtor_tl { get; }
  }
  public abstract class List<T> : _IList<T> {
    public List() { }
    public static _IList<T> Default() {
      return create_Nil();
    }
    public static Dafny.TypeDescriptor<LinkedList_Compile._IList<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<LinkedList_Compile._IList<T>>(LinkedList_Compile.List<T>.Default());
    }
    public static _IList<T> create_Cons(T hd, LinkedList_Compile._IList<T> tl) {
      return new List_Cons<T>(hd, tl);
    }
    public static _IList<T> create_Nil() {
      return new List_Nil<T>();
    }
    public bool is_Cons { get { return this is List_Cons<T>; } }
    public bool is_Nil { get { return this is List_Nil<T>; } }
    public T dtor_hd {
      get {
        var d = this;
        return ((List_Cons<T>)d).hd;
      }
    }
    public LinkedList_Compile._IList<T> dtor_tl {
      get {
        var d = this;
        return ((List_Cons<T>)d).tl;
      }
    }
  }
  public class List_Cons<T> : List<T> {
    public readonly T hd;
    public readonly LinkedList_Compile._IList<T> tl;
    public List_Cons(T hd, LinkedList_Compile._IList<T> tl) {
      this.hd = hd;
      this.tl = tl;
    }
    public override bool Equals(object other) {
      var oth = other as LinkedList_Compile.List_Cons<T>;
      return oth != null && object.Equals(this.hd, oth.hd) && object.Equals(this.tl, oth.tl);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.hd));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.tl));
      return (int) hash;
    }
    public override string ToString() {
      string s = "LinkedList_Compile.List.Cons";
      s += "(";
      s += Dafny.Helpers.ToString(this.hd);
      s += ", ";
      s += Dafny.Helpers.ToString(this.tl);
      s += ")";
      return s;
    }
  }
  public class List_Nil<T> : List<T> {
    public List_Nil() {
    }
    public override bool Equals(object other) {
      var oth = other as LinkedList_Compile.List_Nil<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "LinkedList_Compile.List.Nil";
      return s;
    }
  }

  public partial class __default {
    public static LinkedList_Compile._IList<__T> Singleton<__T>(__T t) {
      return LinkedList_Compile.List<__T>.create_Cons(t, LinkedList_Compile.List<__T>.create_Nil());
    }
    public static LinkedList_Compile._IList<__T> Concat<__T>(LinkedList_Compile._IList<__T> l1, LinkedList_Compile._IList<__T> l2)
    {
      LinkedList_Compile._IList<__T> _source0 = l1;
      if (_source0.is_Cons) {
        __T _1088___mcc_h0 = ((LinkedList_Compile.List_Cons<__T>)_source0).hd;
        LinkedList_Compile._IList<__T> _1089___mcc_h1 = ((LinkedList_Compile.List_Cons<__T>)_source0).tl;
        LinkedList_Compile._IList<__T> _1090_t = _1089___mcc_h1;
        __T _1091_h = _1088___mcc_h0;
        return LinkedList_Compile.List<__T>.create_Cons(_1091_h, LinkedList_Compile.__default.Concat<__T>(_1090_t, l2));
      } else {
        return l2;
      }
    }
    public static Dafny.ISequence<__T> ToSeq<__T>(LinkedList_Compile._IList<__T> l) {
      Dafny.ISequence<__T> _1092___accumulator = Dafny.Sequence<__T>.FromElements();
    TAIL_CALL_START: ;
      LinkedList_Compile._IList<__T> _source1 = l;
      if (_source1.is_Cons) {
        __T _1093___mcc_h0 = ((LinkedList_Compile.List_Cons<__T>)_source1).hd;
        LinkedList_Compile._IList<__T> _1094___mcc_h1 = ((LinkedList_Compile.List_Cons<__T>)_source1).tl;
        LinkedList_Compile._IList<__T> _1095_t = _1094___mcc_h1;
        __T _1096_h = _1093___mcc_h0;
        _1092___accumulator = Dafny.Sequence<__T>.Concat(_1092___accumulator, Dafny.Sequence<__T>.FromElements(_1096_h));
        LinkedList_Compile._IList<__T> _in0 = _1095_t;
        l = _in0;
        goto TAIL_CALL_START;
      } else {
        return Dafny.Sequence<__T>.Concat(_1092___accumulator, Dafny.Sequence<__T>.FromElements());
      }
    }
  }
} // end of namespace LinkedList_Compile
namespace System.Collections.Generic {


} // end of namespace System.Collections.Generic
namespace SelfHosting.CSharp {


  public interface Expr {
  }
  public class _Companion_Expr {
  }

  public interface Const : SelfHosting.CSharp.Expr {
    BigInteger n { get; set; }
  }
  public class _Companion_Const {
  }

  public interface Add : SelfHosting.CSharp.Expr {
    SelfHosting.CSharp.Expr e1 { get; set; }
    SelfHosting.CSharp.Expr e2 { get; set; }
  }
  public class _Companion_Add {
  }

  public interface Stmt {
  }
  public class _Companion_Stmt {
  }

  public interface Print : SelfHosting.CSharp.Stmt {
    SelfHosting.CSharp.Expr e { get; set; }
  }
  public class _Companion_Print {
  }

  public interface Prog {
    System.Collections.Generic.List<SelfHosting.CSharp.Stmt> s { get; set; }
  }
  public class _Companion_Prog {
  }

} // end of namespace SelfHosting.CSharp
namespace Dafny_Compile {

  public interface _IExpr {
    bool is_Const { get; }
    bool is_Add { get; }
    BigInteger dtor_n { get; }
    Dafny_Compile._IExpr dtor_e1 { get; }
    Dafny_Compile._IExpr dtor_e2 { get; }
  }
  public abstract class Expr : _IExpr {
    public Expr() { }
    private static readonly _IExpr theDefault = create_Const(BigInteger.Zero);
    public static _IExpr Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny_Compile._IExpr> _TYPE = new Dafny.TypeDescriptor<Dafny_Compile._IExpr>(Dafny_Compile.Expr.Default());
    public static Dafny.TypeDescriptor<Dafny_Compile._IExpr> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IExpr create_Const(BigInteger n) {
      return new Expr_Const(n);
    }
    public static _IExpr create_Add(Dafny_Compile._IExpr e1, Dafny_Compile._IExpr e2) {
      return new Expr_Add(e1, e2);
    }
    public bool is_Const { get { return this is Expr_Const; } }
    public bool is_Add { get { return this is Expr_Add; } }
    public BigInteger dtor_n {
      get {
        var d = this;
        return ((Expr_Const)d).n;
      }
    }
    public Dafny_Compile._IExpr dtor_e1 {
      get {
        var d = this;
        return ((Expr_Add)d).e1;
      }
    }
    public Dafny_Compile._IExpr dtor_e2 {
      get {
        var d = this;
        return ((Expr_Add)d).e2;
      }
    }
  }
  public class Expr_Const : Expr {
    public readonly BigInteger n;
    public Expr_Const(BigInteger n) {
      this.n = n;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny_Compile.Expr_Const;
      return oth != null && this.n == oth.n;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.Expr.Const";
      s += "(";
      s += Dafny.Helpers.ToString(this.n);
      s += ")";
      return s;
    }
  }
  public class Expr_Add : Expr {
    public readonly Dafny_Compile._IExpr e1;
    public readonly Dafny_Compile._IExpr e2;
    public Expr_Add(Dafny_Compile._IExpr e1, Dafny_Compile._IExpr e2) {
      this.e1 = e1;
      this.e2 = e2;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny_Compile.Expr_Add;
      return oth != null && object.Equals(this.e1, oth.e1) && object.Equals(this.e2, oth.e2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.Expr.Add";
      s += "(";
      s += Dafny.Helpers.ToString(this.e1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.e2);
      s += ")";
      return s;
    }
  }

  public interface _IStmt {
    bool is_Skip { get; }
    bool is_Print { get; }
    bool is_Seq { get; }
    Dafny_Compile._IExpr dtor_e { get; }
    Dafny_Compile._IStmt dtor_s1 { get; }
    Dafny_Compile._IStmt dtor_s2 { get; }
  }
  public abstract class Stmt : _IStmt {
    public Stmt() { }
    private static readonly _IStmt theDefault = create_Skip();
    public static _IStmt Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Dafny_Compile._IStmt> _TYPE = new Dafny.TypeDescriptor<Dafny_Compile._IStmt>(Dafny_Compile.Stmt.Default());
    public static Dafny.TypeDescriptor<Dafny_Compile._IStmt> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStmt create_Skip() {
      return new Stmt_Skip();
    }
    public static _IStmt create_Print(Dafny_Compile._IExpr e) {
      return new Stmt_Print(e);
    }
    public static _IStmt create_Seq(Dafny_Compile._IStmt s1, Dafny_Compile._IStmt s2) {
      return new Stmt_Seq(s1, s2);
    }
    public bool is_Skip { get { return this is Stmt_Skip; } }
    public bool is_Print { get { return this is Stmt_Print; } }
    public bool is_Seq { get { return this is Stmt_Seq; } }
    public Dafny_Compile._IExpr dtor_e {
      get {
        var d = this;
        return ((Stmt_Print)d).e;
      }
    }
    public Dafny_Compile._IStmt dtor_s1 {
      get {
        var d = this;
        return ((Stmt_Seq)d).s1;
      }
    }
    public Dafny_Compile._IStmt dtor_s2 {
      get {
        var d = this;
        return ((Stmt_Seq)d).s2;
      }
    }
  }
  public class Stmt_Skip : Stmt {
    public Stmt_Skip() {
    }
    public override bool Equals(object other) {
      var oth = other as Dafny_Compile.Stmt_Skip;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.Stmt.Skip";
      return s;
    }
  }
  public class Stmt_Print : Stmt {
    public readonly Dafny_Compile._IExpr e;
    public Stmt_Print(Dafny_Compile._IExpr e) {
      this.e = e;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny_Compile.Stmt_Print;
      return oth != null && object.Equals(this.e, oth.e);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.Stmt.Print";
      s += "(";
      s += Dafny.Helpers.ToString(this.e);
      s += ")";
      return s;
    }
  }
  public class Stmt_Seq : Stmt {
    public readonly Dafny_Compile._IStmt s1;
    public readonly Dafny_Compile._IStmt s2;
    public Stmt_Seq(Dafny_Compile._IStmt s1, Dafny_Compile._IStmt s2) {
      this.s1 = s1;
      this.s2 = s2;
    }
    public override bool Equals(object other) {
      var oth = other as Dafny_Compile.Stmt_Seq;
      return oth != null && object.Equals(this.s1, oth.s1) && object.Equals(this.s2, oth.s2);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s1));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s2));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Dafny_Compile.Stmt.Seq";
      s += "(";
      s += Dafny.Helpers.ToString(this.s1);
      s += ", ";
      s += Dafny.Helpers.ToString(this.s2);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static BigInteger interpExpr(Dafny_Compile._IExpr e) {
      Dafny_Compile._IExpr _source2 = e;
      if (_source2.is_Const) {
        BigInteger _1097___mcc_h0 = ((Dafny_Compile.Expr_Const)_source2).n;
        BigInteger _1098_n = _1097___mcc_h0;
        return _1098_n;
      } else {
        Dafny_Compile._IExpr _1099___mcc_h1 = ((Dafny_Compile.Expr_Add)_source2).e1;
        Dafny_Compile._IExpr _1100___mcc_h2 = ((Dafny_Compile.Expr_Add)_source2).e2;
        Dafny_Compile._IExpr _1101_e2 = _1100___mcc_h2;
        Dafny_Compile._IExpr _1102_e1 = _1099___mcc_h1;
        return (Dafny_Compile.__default.interpExpr(_1102_e1)) + (Dafny_Compile.__default.interpExpr(_1101_e2));
      }
    }
    public static Dafny.ISequence<BigInteger> interpStmt(Dafny_Compile._IStmt s) {
      Dafny_Compile._IStmt _source3 = s;
      if (_source3.is_Skip) {
        return Dafny.Sequence<BigInteger>.FromElements();
      } else if (_source3.is_Print) {
        Dafny_Compile._IExpr _1103___mcc_h0 = ((Dafny_Compile.Stmt_Print)_source3).e;
        Dafny_Compile._IExpr _1104_e = _1103___mcc_h0;
        return Dafny.Sequence<BigInteger>.FromElements(Dafny_Compile.__default.interpExpr(_1104_e));
      } else {
        Dafny_Compile._IStmt _1105___mcc_h1 = ((Dafny_Compile.Stmt_Seq)_source3).s1;
        Dafny_Compile._IStmt _1106___mcc_h2 = ((Dafny_Compile.Stmt_Seq)_source3).s2;
        Dafny_Compile._IStmt _1107_s2 = _1106___mcc_h2;
        Dafny_Compile._IStmt _1108_s1 = _1105___mcc_h1;
        return Dafny.Sequence<BigInteger>.Concat(Dafny_Compile.__default.interpStmt(_1108_s1), Dafny_Compile.__default.interpStmt(_1107_s2));
      }
    }
  }
} // end of namespace Dafny_Compile
namespace Global_Compile {

  public partial class __default {
    public static __T unreachable<__T>() {
      _System._ITuple0 _source4 = _System.Tuple0.create();
      throw new System.Exception("unexpected control point");
    }
  }
} // end of namespace Global_Compile
namespace SelfHosting.CSharpUtils {


  public partial class ListUtils {
    public ListUtils() {
    }
    public static void AppendSeq<__T>(System.Collections.Generic.List<__T> l, Dafny.ISequence<__T> s)
    {
      BigInteger _1109_i;
      _1109_i = BigInteger.Zero;
      while ((_1109_i) < (new BigInteger((s).Count))) {
        SelfHosting.CSharpUtils.ListUtils.Append<__T>(l, (s).Select(_1109_i));
        _1109_i = (_1109_i) + (BigInteger.One);
      }
    }
  }

} // end of namespace SelfHosting.CSharpUtils
namespace Translator_Compile {






  public partial class __default {
    public static Dafny_Compile._IExpr translateExpr(SelfHosting.CSharp.Expr c) {
      if (Dafny.Helpers.Let<SelfHosting.CSharp.Expr, bool>(c, _is_0 => _is_0 is SelfHosting.CSharp.Const)) {
        return Dafny_Compile.Expr.create_Const(((SelfHosting.CSharp.Const)(c)).n);
      } else if (Dafny.Helpers.Let<SelfHosting.CSharp.Expr, bool>(c, _is_1 => _is_1 is SelfHosting.CSharp.Add)) {
        SelfHosting.CSharp.Add _1110_c = ((SelfHosting.CSharp.Add)(c));
        return Dafny_Compile.Expr.create_Add(Translator_Compile.__default.translateExpr(_1110_c.e1), Translator_Compile.__default.translateExpr(_1110_c.e2));
      } else {
        return Global_Compile.__default.unreachable<Dafny_Compile._IExpr>();
      }
    }
    public static Dafny_Compile._IStmt translateStmt(SelfHosting.CSharp.Stmt c) {
      if (Dafny.Helpers.Let<SelfHosting.CSharp.Stmt, bool>(c, _is_2 => _is_2 is SelfHosting.CSharp.Print)) {
        Dafny_Compile._IExpr _1111_e = Translator_Compile.__default.translateExpr(((SelfHosting.CSharp.Print)(c)).e);
        return Dafny_Compile.Stmt.create_Print(_1111_e);
      } else {
        return Global_Compile.__default.unreachable<Dafny_Compile._IStmt>();
      }
    }
    public static Dafny_Compile._IStmt translateProg(SelfHosting.CSharp.Prog c) {
      if (true) {
        return SelfHosting.CSharpUtils.ListUtils.FoldR<SelfHosting.CSharp.Stmt, Dafny_Compile._IStmt>(((System.Func<SelfHosting.CSharp.Stmt, Dafny_Compile._IStmt, Dafny_Compile._IStmt>)((_1112_c, _1113_ds) => {
          return Dafny_Compile.Stmt.create_Seq(Translator_Compile.__default.translateStmt(_1112_c), _1113_ds);
        })), Dafny_Compile.Stmt.create_Skip(), c.s);
      } else {
        return Global_Compile.__default.unreachable<Dafny_Compile._IStmt>();
      }
    }
  }
} // end of namespace Translator_Compile
namespace Rewriter_Compile {


  public partial class __default {
    public static Dafny_Compile._IExpr simplExpr(Dafny_Compile._IExpr e) {
      Dafny_Compile._IExpr _source5 = e;
      if (_source5.is_Const) {
        BigInteger _1114___mcc_h0 = ((Dafny_Compile.Expr_Const)_source5).n;
        BigInteger _1115_n = _1114___mcc_h0;
        return e;
      } else {
        Dafny_Compile._IExpr _1116___mcc_h1 = ((Dafny_Compile.Expr_Add)_source5).e1;
        Dafny_Compile._IExpr _1117___mcc_h2 = ((Dafny_Compile.Expr_Add)_source5).e2;
        Dafny_Compile._IExpr _1118_e2 = _1117___mcc_h2;
        Dafny_Compile._IExpr _1119_e1 = _1116___mcc_h1;
        _System._ITuple2<Dafny_Compile._IExpr, Dafny_Compile._IExpr> _source6 = _System.Tuple2<Dafny_Compile._IExpr, Dafny_Compile._IExpr>.create(Rewriter_Compile.__default.simplExpr(_1119_e1), Rewriter_Compile.__default.simplExpr(_1118_e2));
        {
          Dafny_Compile._IExpr _1120___mcc_h3 = ((_System.Tuple2<Dafny_Compile._IExpr, Dafny_Compile._IExpr>)_source6)._0;
          Dafny_Compile._IExpr _1121___mcc_h4 = ((_System.Tuple2<Dafny_Compile._IExpr, Dafny_Compile._IExpr>)_source6)._1;
          Dafny_Compile._IExpr _source7 = _1120___mcc_h3;
          if (_source7.is_Const) {
            BigInteger _1122___mcc_h5 = ((Dafny_Compile.Expr_Const)_source7).n;
            if ((_1122___mcc_h5).Sign == 0) {
              Dafny_Compile._IExpr _source8 = _1121___mcc_h4;
              if (_source8.is_Const) {
                BigInteger _1123___mcc_h8 = ((Dafny_Compile.Expr_Const)_source8).n;
                if ((_1123___mcc_h8).Sign == 0) {
                  return Dafny_Compile.Expr.create_Const(BigInteger.Zero);
                } else {
                  Dafny_Compile._IExpr _1124_e2 = _1121___mcc_h4;
                  return _1124_e2;
                }
              } else {
                Dafny_Compile._IExpr _1125___mcc_h11 = ((Dafny_Compile.Expr_Add)_source8).e1;
                Dafny_Compile._IExpr _1126___mcc_h12 = ((Dafny_Compile.Expr_Add)_source8).e2;
                Dafny_Compile._IExpr _1127_e2 = _1121___mcc_h4;
                return _1127_e2;
              }
            } else {
              Dafny_Compile._IExpr _source9 = _1121___mcc_h4;
              if (_source9.is_Const) {
                BigInteger _1128___mcc_h17 = ((Dafny_Compile.Expr_Const)_source9).n;
                if ((_1128___mcc_h17).Sign == 0) {
                  Dafny_Compile._IExpr _1129_e1 = _1120___mcc_h3;
                  return _1129_e1;
                } else {
                  Dafny_Compile._IExpr _1130_e2 = _1121___mcc_h4;
                  Dafny_Compile._IExpr _1131_e1 = _1120___mcc_h3;
                  return Dafny_Compile.Expr.create_Add(_1131_e1, _1130_e2);
                }
              } else {
                Dafny_Compile._IExpr _1132___mcc_h19 = ((Dafny_Compile.Expr_Add)_source9).e1;
                Dafny_Compile._IExpr _1133___mcc_h20 = ((Dafny_Compile.Expr_Add)_source9).e2;
                Dafny_Compile._IExpr _1134_e2 = _1121___mcc_h4;
                Dafny_Compile._IExpr _1135_e1 = _1120___mcc_h3;
                return Dafny_Compile.Expr.create_Add(_1135_e1, _1134_e2);
              }
            }
          } else {
            Dafny_Compile._IExpr _1136___mcc_h23 = ((Dafny_Compile.Expr_Add)_source7).e1;
            Dafny_Compile._IExpr _1137___mcc_h24 = ((Dafny_Compile.Expr_Add)_source7).e2;
            Dafny_Compile._IExpr _source10 = _1121___mcc_h4;
            if (_source10.is_Const) {
              BigInteger _1138___mcc_h29 = ((Dafny_Compile.Expr_Const)_source10).n;
              if ((_1138___mcc_h29).Sign == 0) {
                Dafny_Compile._IExpr _1139_e1 = _1120___mcc_h3;
                return _1139_e1;
              } else {
                Dafny_Compile._IExpr _1140_e2 = _1121___mcc_h4;
                Dafny_Compile._IExpr _1141_e1 = _1120___mcc_h3;
                return Dafny_Compile.Expr.create_Add(_1141_e1, _1140_e2);
              }
            } else {
              Dafny_Compile._IExpr _1142___mcc_h31 = ((Dafny_Compile.Expr_Add)_source10).e1;
              Dafny_Compile._IExpr _1143___mcc_h32 = ((Dafny_Compile.Expr_Add)_source10).e2;
              Dafny_Compile._IExpr _1144_e2 = _1121___mcc_h4;
              Dafny_Compile._IExpr _1145_e1 = _1120___mcc_h3;
              return Dafny_Compile.Expr.create_Add(_1145_e1, _1144_e2);
            }
          }
        }
      }
    }
    public static Dafny_Compile._IStmt simplStmt(Dafny_Compile._IStmt s) {
      Dafny_Compile._IStmt _source11 = s;
      if (_source11.is_Skip) {
        return Dafny_Compile.Stmt.create_Skip();
      } else if (_source11.is_Print) {
        Dafny_Compile._IExpr _1146___mcc_h0 = ((Dafny_Compile.Stmt_Print)_source11).e;
        Dafny_Compile._IExpr _1147_e = _1146___mcc_h0;
        return Dafny_Compile.Stmt.create_Print(Rewriter_Compile.__default.simplExpr(_1147_e));
      } else {
        Dafny_Compile._IStmt _1148___mcc_h1 = ((Dafny_Compile.Stmt_Seq)_source11).s1;
        Dafny_Compile._IStmt _1149___mcc_h2 = ((Dafny_Compile.Stmt_Seq)_source11).s2;
        Dafny_Compile._IStmt _1150_s2 = _1149___mcc_h2;
        Dafny_Compile._IStmt _1151_s1 = _1148___mcc_h1;
        _System._ITuple2<Dafny_Compile._IStmt, Dafny_Compile._IStmt> _source12 = _System.Tuple2<Dafny_Compile._IStmt, Dafny_Compile._IStmt>.create(Rewriter_Compile.__default.simplStmt(_1151_s1), Rewriter_Compile.__default.simplStmt(_1150_s2));
        {
          Dafny_Compile._IStmt _1152___mcc_h3 = ((_System.Tuple2<Dafny_Compile._IStmt, Dafny_Compile._IStmt>)_source12)._0;
          Dafny_Compile._IStmt _1153___mcc_h4 = ((_System.Tuple2<Dafny_Compile._IStmt, Dafny_Compile._IStmt>)_source12)._1;
          Dafny_Compile._IStmt _source13 = _1152___mcc_h3;
          if (_source13.is_Skip) {
            Dafny_Compile._IStmt _source14 = _1153___mcc_h4;
            if (_source14.is_Skip) {
              Dafny_Compile._IStmt _1154_s1 = _1152___mcc_h3;
              return _1154_s1;
            } else if (_source14.is_Print) {
              Dafny_Compile._IExpr _1155___mcc_h5 = ((Dafny_Compile.Stmt_Print)_source14).e;
              Dafny_Compile._IStmt _1156_s2 = _1153___mcc_h4;
              return _1156_s2;
            } else {
              Dafny_Compile._IStmt _1157___mcc_h8 = ((Dafny_Compile.Stmt_Seq)_source14).s1;
              Dafny_Compile._IStmt _1158___mcc_h9 = ((Dafny_Compile.Stmt_Seq)_source14).s2;
              Dafny_Compile._IStmt _1159_s2 = _1153___mcc_h4;
              return _1159_s2;
            }
          } else if (_source13.is_Print) {
            Dafny_Compile._IExpr _1160___mcc_h14 = ((Dafny_Compile.Stmt_Print)_source13).e;
            Dafny_Compile._IStmt _source15 = _1153___mcc_h4;
            if (_source15.is_Skip) {
              Dafny_Compile._IStmt _1161_s1 = _1152___mcc_h3;
              return _1161_s1;
            } else if (_source15.is_Print) {
              Dafny_Compile._IExpr _1162___mcc_h17 = ((Dafny_Compile.Stmt_Print)_source15).e;
              Dafny_Compile._IStmt _1163_s2 = _1153___mcc_h4;
              Dafny_Compile._IStmt _1164_s1 = _1152___mcc_h3;
              return Dafny_Compile.Stmt.create_Seq(_1164_s1, _1163_s2);
            } else {
              Dafny_Compile._IStmt _1165___mcc_h19 = ((Dafny_Compile.Stmt_Seq)_source15).s1;
              Dafny_Compile._IStmt _1166___mcc_h20 = ((Dafny_Compile.Stmt_Seq)_source15).s2;
              Dafny_Compile._IStmt _1167_s2 = _1153___mcc_h4;
              Dafny_Compile._IStmt _1168_s1 = _1152___mcc_h3;
              return Dafny_Compile.Stmt.create_Seq(_1168_s1, _1167_s2);
            }
          } else {
            Dafny_Compile._IStmt _1169___mcc_h23 = ((Dafny_Compile.Stmt_Seq)_source13).s1;
            Dafny_Compile._IStmt _1170___mcc_h24 = ((Dafny_Compile.Stmt_Seq)_source13).s2;
            Dafny_Compile._IStmt _source16 = _1153___mcc_h4;
            if (_source16.is_Skip) {
              Dafny_Compile._IStmt _1171_s1 = _1152___mcc_h3;
              return _1171_s1;
            } else if (_source16.is_Print) {
              Dafny_Compile._IExpr _1172___mcc_h29 = ((Dafny_Compile.Stmt_Print)_source16).e;
              Dafny_Compile._IStmt _1173_s2 = _1153___mcc_h4;
              Dafny_Compile._IStmt _1174_s1 = _1152___mcc_h3;
              return Dafny_Compile.Stmt.create_Seq(_1174_s1, _1173_s2);
            } else {
              Dafny_Compile._IStmt _1175___mcc_h31 = ((Dafny_Compile.Stmt_Seq)_source16).s1;
              Dafny_Compile._IStmt _1176___mcc_h32 = ((Dafny_Compile.Stmt_Seq)_source16).s2;
              Dafny_Compile._IStmt _1177_s2 = _1153___mcc_h4;
              Dafny_Compile._IStmt _1178_s1 = _1152___mcc_h3;
              return Dafny_Compile.Stmt.create_Seq(_1178_s1, _1177_s2);
            }
          }
        }
      }
    }
  }
} // end of namespace Rewriter_Compile
namespace StackMachine_Compile {



  public interface _IOp {
    bool is_PushConst { get; }
    bool is_PopAdd { get; }
    bool is_PopPrint { get; }
    BigInteger dtor_n { get; }
  }
  public abstract class Op : _IOp {
    public Op() { }
    private static readonly _IOp theDefault = create_PushConst(BigInteger.Zero);
    public static _IOp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<StackMachine_Compile._IOp> _TYPE = new Dafny.TypeDescriptor<StackMachine_Compile._IOp>(StackMachine_Compile.Op.Default());
    public static Dafny.TypeDescriptor<StackMachine_Compile._IOp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IOp create_PushConst(BigInteger n) {
      return new Op_PushConst(n);
    }
    public static _IOp create_PopAdd() {
      return new Op_PopAdd();
    }
    public static _IOp create_PopPrint() {
      return new Op_PopPrint();
    }
    public bool is_PushConst { get { return this is Op_PushConst; } }
    public bool is_PopAdd { get { return this is Op_PopAdd; } }
    public bool is_PopPrint { get { return this is Op_PopPrint; } }
    public BigInteger dtor_n {
      get {
        var d = this;
        return ((Op_PushConst)d).n;
      }
    }
  }
  public class Op_PushConst : Op {
    public readonly BigInteger n;
    public Op_PushConst(BigInteger n) {
      this.n = n;
    }
    public override bool Equals(object other) {
      var oth = other as StackMachine_Compile.Op_PushConst;
      return oth != null && this.n == oth.n;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackMachine_Compile.Op.PushConst";
      s += "(";
      s += Dafny.Helpers.ToString(this.n);
      s += ")";
      return s;
    }
  }
  public class Op_PopAdd : Op {
    public Op_PopAdd() {
    }
    public override bool Equals(object other) {
      var oth = other as StackMachine_Compile.Op_PopAdd;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackMachine_Compile.Op.PopAdd";
      return s;
    }
  }
  public class Op_PopPrint : Op {
    public Op_PopPrint() {
    }
    public override bool Equals(object other) {
      var oth = other as StackMachine_Compile.Op_PopPrint;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackMachine_Compile.Op.PopPrint";
      return s;
    }
  }


  public interface _IState {
    bool is_State { get; }
    LinkedList_Compile._IList<BigInteger> dtor_stack { get; }
    Dafny.ISequence<BigInteger> dtor_output { get; }
  }
  public class State : _IState {
    public readonly LinkedList_Compile._IList<BigInteger> stack;
    public readonly Dafny.ISequence<BigInteger> output;
    public State(LinkedList_Compile._IList<BigInteger> stack, Dafny.ISequence<BigInteger> output) {
      this.stack = stack;
      this.output = output;
    }
    public override bool Equals(object other) {
      var oth = other as StackMachine_Compile.State;
      return oth != null && object.Equals(this.stack, oth.stack) && object.Equals(this.output, oth.output);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.stack));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.output));
      return (int) hash;
    }
    public override string ToString() {
      string s = "StackMachine_Compile.State.State";
      s += "(";
      s += Dafny.Helpers.ToString(this.stack);
      s += ", ";
      s += Dafny.Helpers.ToString(this.output);
      s += ")";
      return s;
    }
    private static readonly _IState theDefault = create(LinkedList_Compile.List<BigInteger>.Default(), Dafny.Sequence<BigInteger>.Empty);
    public static _IState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<StackMachine_Compile._IState> _TYPE = new Dafny.TypeDescriptor<StackMachine_Compile._IState>(StackMachine_Compile.State.Default());
    public static Dafny.TypeDescriptor<StackMachine_Compile._IState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IState create(LinkedList_Compile._IList<BigInteger> stack, Dafny.ISequence<BigInteger> output) {
      return new State(stack, output);
    }
    public bool is_State { get { return true; } }
    public LinkedList_Compile._IList<BigInteger> dtor_stack {
      get {
        return this.stack;
      }
    }
    public Dafny.ISequence<BigInteger> dtor_output {
      get {
        return this.output;
      }
    }
  }

  public partial class __default {
    public static StackMachine_Compile._IState interpOp(StackMachine_Compile._IOp op, StackMachine_Compile._IState st)
    {
      _System._ITuple2<StackMachine_Compile._IOp, LinkedList_Compile._IList<BigInteger>> _source17 = _System.Tuple2<StackMachine_Compile._IOp, LinkedList_Compile._IList<BigInteger>>.create(op, (st).dtor_stack);
      {
        StackMachine_Compile._IOp _1179___mcc_h0 = ((_System.Tuple2<StackMachine_Compile._IOp, LinkedList_Compile._IList<BigInteger>>)_source17)._0;
        LinkedList_Compile._IList<BigInteger> _1180___mcc_h1 = ((_System.Tuple2<StackMachine_Compile._IOp, LinkedList_Compile._IList<BigInteger>>)_source17)._1;
        StackMachine_Compile._IOp _source18 = _1179___mcc_h0;
        if (_source18.is_PushConst) {
          BigInteger _1181___mcc_h2 = ((StackMachine_Compile.Op_PushConst)_source18).n;
          LinkedList_Compile._IList<BigInteger> _1182_tl = _1180___mcc_h1;
          BigInteger _1183_n = _1181___mcc_h2;
          return StackMachine_Compile.State.create(LinkedList_Compile.List<BigInteger>.create_Cons(_1183_n, _1182_tl), (st).dtor_output);
        } else if (_source18.is_PopAdd) {
          LinkedList_Compile._IList<BigInteger> _source19 = _1180___mcc_h1;
          if (_source19.is_Cons) {
            BigInteger _1184___mcc_h3 = ((LinkedList_Compile.List_Cons<BigInteger>)_source19).hd;
            LinkedList_Compile._IList<BigInteger> _1185___mcc_h4 = ((LinkedList_Compile.List_Cons<BigInteger>)_source19).tl;
            LinkedList_Compile._IList<BigInteger> _source20 = _1185___mcc_h4;
            if (_source20.is_Cons) {
              BigInteger _1186___mcc_h7 = ((LinkedList_Compile.List_Cons<BigInteger>)_source20).hd;
              LinkedList_Compile._IList<BigInteger> _1187___mcc_h8 = ((LinkedList_Compile.List_Cons<BigInteger>)_source20).tl;
              LinkedList_Compile._IList<BigInteger> _1188_tl = _1187___mcc_h8;
              BigInteger _1189_n1 = _1186___mcc_h7;
              BigInteger _1190_n2 = _1184___mcc_h3;
              return StackMachine_Compile.State.create(LinkedList_Compile.List<BigInteger>.create_Cons((_1189_n1) + (_1190_n2), _1188_tl), (st).dtor_output);
            } else {
              return st;
            }
          } else {
            return st;
          }
        } else {
          LinkedList_Compile._IList<BigInteger> _source21 = _1180___mcc_h1;
          if (_source21.is_Cons) {
            BigInteger _1191___mcc_h11 = ((LinkedList_Compile.List_Cons<BigInteger>)_source21).hd;
            LinkedList_Compile._IList<BigInteger> _1192___mcc_h12 = ((LinkedList_Compile.List_Cons<BigInteger>)_source21).tl;
            LinkedList_Compile._IList<BigInteger> _1193_tl = _1192___mcc_h12;
            BigInteger _1194_n = _1191___mcc_h11;
            return StackMachine_Compile.State.create(_1193_tl, Dafny.Sequence<BigInteger>.Concat((st).dtor_output, Dafny.Sequence<BigInteger>.FromElements(_1194_n)));
          } else {
            return st;
          }
        }
      }
    }
    public static StackMachine_Compile._IState interpProg_k(LinkedList_Compile._IList<StackMachine_Compile._IOp> p, StackMachine_Compile._IState st)
    {
      LinkedList_Compile._IList<StackMachine_Compile._IOp> _source22 = p;
      if (_source22.is_Cons) {
        StackMachine_Compile._IOp _1195___mcc_h0 = ((LinkedList_Compile.List_Cons<StackMachine_Compile._IOp>)_source22).hd;
        LinkedList_Compile._IList<StackMachine_Compile._IOp> _1196___mcc_h1 = ((LinkedList_Compile.List_Cons<StackMachine_Compile._IOp>)_source22).tl;
        LinkedList_Compile._IList<StackMachine_Compile._IOp> _1197_p = _1196___mcc_h1;
        StackMachine_Compile._IOp _1198_op = _1195___mcc_h0;
        return StackMachine_Compile.__default.interpOp(_1198_op, StackMachine_Compile.__default.interpProg_k(_1197_p, st));
      } else {
        return st;
      }
    }
    public static Dafny.ISequence<BigInteger> interpProg(LinkedList_Compile._IList<StackMachine_Compile._IOp> p) {
      return (StackMachine_Compile.__default.interpProg_k(p, StackMachine_Compile.__default.EmptyState)).dtor_output;
    }
    public static Dafny.ISequence<char> prettyPrintDigit(BigInteger n) {
      if ((n).Sign == 0) {
        return Dafny.Sequence<char>.FromString("0");
      } else if ((n) == (BigInteger.One)) {
        return Dafny.Sequence<char>.FromString("1");
      } else if ((n) == (new BigInteger(2))) {
        return Dafny.Sequence<char>.FromString("2");
      } else if ((n) == (new BigInteger(3))) {
        return Dafny.Sequence<char>.FromString("3");
      } else if ((n) == (new BigInteger(4))) {
        return Dafny.Sequence<char>.FromString("4");
      } else if ((n) == (new BigInteger(5))) {
        return Dafny.Sequence<char>.FromString("5");
      } else if ((n) == (new BigInteger(6))) {
        return Dafny.Sequence<char>.FromString("6");
      } else if ((n) == (new BigInteger(7))) {
        return Dafny.Sequence<char>.FromString("7");
      } else if ((n) == (new BigInteger(8))) {
        return Dafny.Sequence<char>.FromString("8");
      } else {
        return Dafny.Sequence<char>.FromString("9");
      }
    }
    public static Dafny.ISequence<char> prettyPrintNum(BigInteger n, Dafny.ISequence<char> zero)
    {
      if ((n).Sign == 0) {
        return zero;
      } else if ((n).Sign == -1) {
        return StackMachine_Compile.__default.prettyPrintNum((BigInteger.Zero) - (n), zero);
      } else if ((n) < (new BigInteger(10))) {
        return StackMachine_Compile.__default.prettyPrintDigit(n);
      } else if ((n) >= (new BigInteger(10))) {
        return Dafny.Sequence<char>.Concat(StackMachine_Compile.__default.prettyPrintNum(Dafny.Helpers.EuclideanDivision(n, new BigInteger(10)), Dafny.Sequence<char>.FromString("")), StackMachine_Compile.__default.prettyPrintNum(Dafny.Helpers.EuclideanModulus(n, new BigInteger(10)), Dafny.Sequence<char>.FromString("0")));
      } else {
        return Global_Compile.__default.unreachable<Dafny.ISequence<char>>();
      }
    }
    public static Dafny.ISequence<char> prettyPrintOp(StackMachine_Compile._IOp op) {
      StackMachine_Compile._IOp _source23 = op;
      if (_source23.is_PushConst) {
        BigInteger _1199___mcc_h0 = ((StackMachine_Compile.Op_PushConst)_source23).n;
        BigInteger _1200_n = _1199___mcc_h0;
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("PushConst("), StackMachine_Compile.__default.prettyPrintNum(_1200_n, Dafny.Sequence<char>.FromString("0"))), Dafny.Sequence<char>.FromString(")"));
      } else if (_source23.is_PopAdd) {
        return Dafny.Sequence<char>.FromString("PopAdd");
      } else {
        StackMachine_Compile._IOp _1201_Print = op;
        return Dafny.Sequence<char>.FromString("Print");
      }
    }
    public static LinkedList_Compile._IList<Dafny.ISequence<char>> prettyPrint(LinkedList_Compile._IList<StackMachine_Compile._IOp> p) {
      LinkedList_Compile._IList<StackMachine_Compile._IOp> _source24 = p;
      if (_source24.is_Cons) {
        StackMachine_Compile._IOp _1202___mcc_h0 = ((LinkedList_Compile.List_Cons<StackMachine_Compile._IOp>)_source24).hd;
        LinkedList_Compile._IList<StackMachine_Compile._IOp> _1203___mcc_h1 = ((LinkedList_Compile.List_Cons<StackMachine_Compile._IOp>)_source24).tl;
        LinkedList_Compile._IList<StackMachine_Compile._IOp> _1204_p = _1203___mcc_h1;
        StackMachine_Compile._IOp _1205_op = _1202___mcc_h0;
        return LinkedList_Compile.List<Dafny.ISequence<char>>.create_Cons(StackMachine_Compile.__default.prettyPrintOp(_1205_op), StackMachine_Compile.__default.prettyPrint(_1204_p));
      } else {
        return LinkedList_Compile.List<Dafny.ISequence<char>>.create_Nil();
      }
    }
    public static StackMachine_Compile._IState EmptyState { get {
      return StackMachine_Compile.State.create(LinkedList_Compile.List<BigInteger>.create_Nil(), Dafny.Sequence<BigInteger>.FromElements());
    } }
  }
} // end of namespace StackMachine_Compile
namespace Compiler_Compile {




  public partial class __default {
    public static LinkedList_Compile._IList<StackMachine_Compile._IOp> compileExpr(Dafny_Compile._IExpr e) {
      Dafny_Compile._IExpr _source25 = e;
      if (_source25.is_Const) {
        BigInteger _1206___mcc_h0 = ((Dafny_Compile.Expr_Const)_source25).n;
        BigInteger _1207_n = _1206___mcc_h0;
        return LinkedList_Compile.__default.Singleton<StackMachine_Compile._IOp>(StackMachine_Compile.Op.create_PushConst(_1207_n));
      } else {
        Dafny_Compile._IExpr _1208___mcc_h1 = ((Dafny_Compile.Expr_Add)_source25).e1;
        Dafny_Compile._IExpr _1209___mcc_h2 = ((Dafny_Compile.Expr_Add)_source25).e2;
        Dafny_Compile._IExpr _1210_e2 = _1209___mcc_h2;
        Dafny_Compile._IExpr _1211_e1 = _1208___mcc_h1;
        return LinkedList_Compile.List<StackMachine_Compile._IOp>.create_Cons(StackMachine_Compile.Op.create_PopAdd(), LinkedList_Compile.__default.Concat<StackMachine_Compile._IOp>(Compiler_Compile.__default.compileExpr(_1210_e2), Compiler_Compile.__default.compileExpr(_1211_e1)));
      }
    }
    public static LinkedList_Compile._IList<StackMachine_Compile._IOp> compileStmt(Dafny_Compile._IStmt s) {
      Dafny_Compile._IStmt _source26 = s;
      if (_source26.is_Skip) {
        return LinkedList_Compile.List<StackMachine_Compile._IOp>.create_Nil();
      } else if (_source26.is_Print) {
        Dafny_Compile._IExpr _1212___mcc_h0 = ((Dafny_Compile.Stmt_Print)_source26).e;
        Dafny_Compile._IExpr _1213_e = _1212___mcc_h0;
        return LinkedList_Compile.List<StackMachine_Compile._IOp>.create_Cons(StackMachine_Compile.Op.create_PopPrint(), Compiler_Compile.__default.compileExpr(_1213_e));
      } else {
        Dafny_Compile._IStmt _1214___mcc_h1 = ((Dafny_Compile.Stmt_Seq)_source26).s1;
        Dafny_Compile._IStmt _1215___mcc_h2 = ((Dafny_Compile.Stmt_Seq)_source26).s2;
        Dafny_Compile._IStmt _1216_s2 = _1215___mcc_h2;
        Dafny_Compile._IStmt _1217_s1 = _1214___mcc_h1;
        return LinkedList_Compile.__default.Concat<StackMachine_Compile._IOp>(Compiler_Compile.__default.compileStmt(_1216_s2), Compiler_Compile.__default.compileStmt(_1217_s1));
      }
    }
  }
} // end of namespace Compiler_Compile
namespace SelfHosting {










  public partial class DafnyCompiler {
    public DafnyCompiler() {
    }
    public static System.Collections.Generic.List<Dafny.ISequence<char>> CompileAndExport(SelfHosting.CSharp.Prog cAST)
    {
      System.Collections.Generic.List<Dafny.ISequence<char>> output = default(System.Collections.Generic.List<Dafny.ISequence<char>>);
      Dafny_Compile._IStmt _1218_translated;
      _1218_translated = Translator_Compile.__default.translateProg(cAST);
      Dafny_Compile._IStmt _1219_optimized;
      _1219_optimized = Rewriter_Compile.__default.simplStmt(_1218_translated);
      LinkedList_Compile._IList<StackMachine_Compile._IOp> _1220_compiled;
      _1220_compiled = Compiler_Compile.__default.compileStmt(_1218_translated);
      LinkedList_Compile._IList<Dafny.ISequence<char>> _1221_prettyPrinted;
      _1221_prettyPrinted = StackMachine_Compile.__default.prettyPrint(_1220_compiled);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("translated = \n  "));
      Dafny.Helpers.Print(_1218_translated);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("optimized = \n  "));
      Dafny.Helpers.Print(_1219_optimized);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("compiled = \n  "));
      Dafny.Helpers.Print(_1220_compiled);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString(""));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("interp(translated) = \n  "));
      Dafny.Helpers.Print(Dafny_Compile.__default.interpStmt(_1218_translated));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("interp(optimized) = \n  "));
      Dafny.Helpers.Print(Dafny_Compile.__default.interpStmt(_1219_optimized));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("interp(compiled) = \n  "));
      Dafny.Helpers.Print((StackMachine_Compile.__default.interpProg_k(_1220_compiled, StackMachine_Compile.__default.EmptyState)).dtor_output);
      Dafny.Helpers.Print(Dafny.Sequence<char>.FromString("\n"));
      System.Collections.Generic.List<Dafny.ISequence<char>> _out0;
      _out0 = SelfHosting.CSharpUtils.ListUtils.Mk<Dafny.ISequence<char>>();
      output = _out0;
      SelfHosting.CSharpUtils.ListUtils.AppendSeq<Dafny.ISequence<char>>(output, LinkedList_Compile.__default.ToSeq<Dafny.ISequence<char>>(_1221_prettyPrinted));
      return output;
    }
  }

} // end of namespace SelfHosting
namespace _module {












} // end of namespace _module
