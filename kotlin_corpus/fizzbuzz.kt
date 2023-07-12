fun main() {
  var i : Int = 0
  while (i<=30) {
    if (i % 3 == 0) {
      println("Fizz")
    } else if (i % 5 == 0) {
      println("Buzz")
    } else if (i % 3 == 0 && i % 5 == 0) {
      println("Fizzbuzz")
    }  else {
      println(i)
    }
    i = i + 1
  }
}
