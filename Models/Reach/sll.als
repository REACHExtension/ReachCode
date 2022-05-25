sig List { header: lone Node }
sig Node { link: lone Node }

pred Acyclic{
  all l : List | all n : l.header.*link | n !in n.^link
}

run Acyclic for 3
