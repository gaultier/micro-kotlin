fun main() {
  var i : Int = 1
  while (i<=30) {
    println(i)

    if (i % 3 == 0 && i % 5 == 0) {
      println("Fizzbuzz")
    } else  if (i % 3 == 0) {
      println("Fizz")
    } else if (i % 5 == 0) {
      println("Buzz")
    } 
    i = i + 1
  }
}
