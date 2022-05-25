sig List { header: lone Node }
sig Node { link: lone Node }

pred Acyclic{
  all l : List | all n : l.header.*link | n !in n.^link
}


run {Acyclic and #List = 0 and #Node = 0} for 0

run {Acyclic} for 1 but exactly 1 List
run {Acyclic and #List != 1} for 1 but exactly 1 Node

run {Acyclic} for 2 but exactly 2 List
run {Acyclic and #List != 2} for 2 but exactly 2 Node

run {Acyclic} for 3 but exactly 3 List
run {Acyclic and #List != 3} for 3 but exactly 3 Node
