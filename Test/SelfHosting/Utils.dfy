module LinkedList {
  datatype List<T> =
    | Cons(hd: T, tl: List<T>)
    | Nil

  function method Singleton<T>(t: T) : List<T> {
    Cons(t, Nil)
  }

  function method Concat<T>(l1: List<T>, l2: List<T>) : List<T> {
    match l1 {
      case Nil => l2
      case Cons(h, t) => Cons(h, Concat<T>(t, l2))
    }
  }

  function method ToSeq<T>(l: List<T>) : seq<T> {
    match l {
      case Nil => []
      case Cons(h, t) => [h] + ToSeq(t)
    }
  }
}

module Global {
  function method unreachable<T>() : T
    requires false
  { match () {} }
}
