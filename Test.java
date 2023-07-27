class Test {
  public static int x = 99;
  public static final Foo foo = new Foo(3);

  public static void main(String[] args) {
    System.out.println(Test.foo);
  }

  int plus(int a, int b) {
    return a + b;
  }
}
