import java.net.http.HttpClient;

class Test {
  public static void main(String[] args) {

   HttpClient client = HttpClient.newBuilder()
        .build();
    // System.out.println(foo.bar.Baz.math(11, 10));

    // DemoKt.fibonacci(10);
    // DemoKt.fibonacci_10();
    // DemoKt.fibonacci_10_long();
    // int a = TestKt.square(5);
    // Integer b = TestKt.square(6);
  }

  public static int square_primitive(int x) {
    return x*x;
  }

  public static Integer square_boxed(Integer x) {
    return x % 2 == 0 ? x*x : null;
  }
}
