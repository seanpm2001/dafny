module {:extern "Test"} Test {
  trait {:extern "Test", "Base"} Base {}

  trait {:extern "Test", "Derived"} Derived extends Base {
    var v: int
  }
}

method test(b: Test.Base) {
  if (b is Test.Derived) {
    print((b as Test.Derived).v);
  }
}
