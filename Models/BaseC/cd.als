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

run {ClassHierarchy and #Class = 1} for 1 
run {ClassHierarchy and #Class < 1 and #Object = 1} for 1 

run {ClassHierarchy and #Class = 2} for 2 
run {ClassHierarchy and #Class < 2 and #Object = 2} for 2 

run {ClassHierarchy and #Class = 3} for 3 
run {ClassHierarchy and #Class < 3 and #Object = 3} for 3 

run {ClassHierarchy and #Class = 4} for 4 
run {ClassHierarchy and #Class < 4 and #Object = 4} for 4 

run {ClassHierarchy and #Class = 5} for 5 
run {ClassHierarchy and #Class < 5 and #Object = 5} for 5 

run {ClassHierarchy and #Class = 6} for 6 
run {ClassHierarchy and #Class < 7 and #Object = 6} for 6 

run {ClassHierarchy and #Class = 7} for 7 
run {ClassHierarchy and #Class < 7 and #Object = 7} for 7 
