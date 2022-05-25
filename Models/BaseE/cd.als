sig Class {
  ext: lone Class
}

one sig Object extends Class {}

pred ObjectNoExt() {
  // Object does not extend any class.
  no Object.ext
}

pred Acyclic() {
  // No class is a sub-class of itself (transitively).
  all c: Class | c !in c.^ext
}

pred AllExtObject() {
  // Each class other than Object is a sub-class of Object.
  all c: Class - Object | c in Object.^~ext
}

pred ClassHierarchy() {
  ObjectNoExt
  Acyclic
  AllExtObject
}


run {ClassHierarchy and #Class = 0 and #Object = 0} for 0

run {ClassHierarchy} for 1 but exactly 1 Class
run {ClassHierarchy and #Class != 1} for 1 but exactly 1 Object

run ClassHierarchy for 2 but exactly 2 Class

run ClassHierarchy for 3 but exactly 3 Class

run ClassHierarchy for 4 but exactly 4 Class

run ClassHierarchy for 5 but exactly 5 Class

run ClassHierarchy for 6 but exactly 6 Class

run ClassHierarchy for 7 but exactly 7 Class

