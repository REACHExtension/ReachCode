sig Element {}

one sig Array {
  // Maps indexes to elements of Element.
  i2e: Int -> Element,
  // Represents the length of the array.
  length: Int
}

// Assume all objects are in the array.
fact Reachable {
  Element = Array.i2e[Int]
}

// Part (a)
fact InBound {
  // All indexes should be greater than or equal to 0 and less than
  // the array length.
  all idx: Array.i2e.Element | idx >= 0 && idx < Array.length
  // Array length should be greater than or equal to 0.
  Array.length >= 0
}

// Part (b)
pred NoConflict() {
  // Each index maps to at most one element.
  all idx: Array.i2e.Element | lone Array.i2e[idx]
}

run {NoConflict and #Element = 0 and #Array = 0} for 0

run {NoConflict} for 1 but exactly 1 Element
run {NoConflict and #Element != 1} for 1 but exactly 1 Array

run NoConflict for 2 but exactly 2 Element
run {NoConflict and #Array = 2 and #Element != 2} for 2 

run NoConflict for 3 but exactly 3 Element
run {NoConflict and #Array = 3 and #Element != 3} for 3 

