// empty.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class YourClass { }

const secAttack: Sec := Low // Change as needed
const lattice: Lattice := map[Low := {Low, High}, High := {High}]

method CAS<T(==)>(x: T, e1: T, e2: T)
    returns (b: bool, x2: T)
  ensures x == e1 ==> x2 == e2
  ensures x != e1 ==> x2 == x
{
  if x == e1 {
    x2 := e2;
    b := false;
  } else {
    x2 := x;
    b := true;
  }
}

predicate order(l: Lattice, a: Sec, b: Sec)
  requires a in l
  requires b in l
{
  b in l[a]
}
