module {:extern "ExtClasses"} Classes {
  class {:extern "ExtCLS"} CLS {
    method Foo() {}
    method {:extern "ExtBar"} Bar()
  }
}

module {:extern "ExtTraits"} Traits {
  trait {:extern "ExtTrait"} {:compile false} TRT {
    method Foo() {}
    method {:extern "ExtBar"} Bar()
  }
}

method {:extern "ExtBaz"} baz()
