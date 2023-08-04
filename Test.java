
class Test {
  public static void main(String[] args) {
    byte b =3;
    kotlin.io.ConsoleKt.println(b);

    DemoKt.fibonacci(10);
    DemoKt.fibonacci_10();
    DemoKt.fibonacci_10_long();
    DemoKt.byte_short();
  }

  public static int square_primitive(int x) {
    return x*x;
  }

  public static Integer square_boxed(Integer x) {
    return x % 2 == 0 ? x*x : null;
  }

  public static void foo(int x) {
    
  }

}
