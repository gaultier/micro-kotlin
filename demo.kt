fun main() {
  println("Hello, world!")
}

fun print_arguments(a: Int, b: Int){
  println(a)
  println(b)
}

fun empty_body(){}

fun plus(a: Long, b: Long) : Long { return a+b }


fun fibonacci(n: Int) {
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
