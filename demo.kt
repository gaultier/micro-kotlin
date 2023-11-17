// This is a demo of what is currently supported by the compiler.
// It also acts as a end-to-end test suite.

fun log_multiply_ints(a: Int, b: Int) {
  println(a*b)
}

fun return_multiply_ints(a: Int, b: Int) : Int {
  return a*b
}

fun fibonacci_rec(n: Int) : Int {
  if (n == 1) {
    return 1
  } 
  return n + fibonacci_rec(n-1)
}

fun main() { /* The entrypoint */
  println("Hello, world!")
  log_multiply_ints(3, 4)
  println(return_multiply_ints(8,9))
  println(return_multiply_ints(return_multiply_ints(8,9), 2))
  println(fibonacci_rec(10))

  print_arguments(1, 2)
  println(plus(127L, 128L))

  fibonacci_10()
  fibonacci_10_long()
  byte_short()
}

fun print_arguments(a: Int, b: Int){
  println("print_arguments")
  println(a)
  println(b)
}

fun empty_body(){}

fun plus(a: Long, b: Long) : Long { return a+b }


fun fibonacci(n: Int) {
  println("fibonacci")

  var a : Int = 0
  var b : Int = 1

  var i : Int = 1
  while (i < n) {
      b = b + a
      a = b - a
      i = i + 1

      println(b)
  }
}

fun fibonacci_10() {
  println("fibonacci_10")

  var a : Int = 0
  var b : Int = 1

  var i : Int = 1
  while (i < 10) {
      b = b + a
      a = b - a
      i = i + 1

      println(b)
  }
}

fun fibonacci_10_long() {
  println("fibonacci_10_long")

  var a : Long = 0L
  var b : Long = 1L

  var i : Long = 1L
  while (i < 10L) {
      b = b + a
      a = b - a
      i = i + 1L

      println(b)
  }
}

fun byte_short(){
  println("byte_short")

  var x: Byte = - 1
  println(x)

  var y: Short = 128
  println(y)
}
