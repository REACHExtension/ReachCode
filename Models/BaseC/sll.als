sig List { header: lone Node }
sig Node { link: lone Node }

pred Acyclic{
  all l : List | all n : l.header.*link | n !in n.^link
}


run {Acyclic and #List = 0 and #Node = 0} for 0

run {Acyclic and #List = 1} for 1 
run {Acyclic and #List < 1 and #Node = 1} for 1 

run {Acyclic and #List = 2} for 2
run {Acyclic and #List < 2 and #Node = 2} for 2 

run {Acyclic and #List = 3} for 3
run {Acyclic and #List < 3 and #Node = 3} for 3 
