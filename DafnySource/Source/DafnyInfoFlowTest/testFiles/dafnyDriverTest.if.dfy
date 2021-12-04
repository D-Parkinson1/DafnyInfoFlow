// dafnyDriverTest.if.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class YourClass {
  function method L_x(): Sec
  {
    Low
  }

  ghost var Gamma_x: Sec
  var x: int

  function method L_z(): Sec
  {
    Low
  }

  ghost var Gamma_z: Sec
  var z: int

  method Relytest()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())
    ensures Gamma_z in lattice
    ensures L_z() in lattice
    ensures old(z) == z ==> old(Gamma_z) == Gamma_z
    ensures order(lattice, Gamma_z, L_z())

  twostate predicate Guaranteetest()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z())
  }

  method test()
    modifies this
  {
    x := 5;
    if true {
      x := 7;
    }
    while x > 3
      decreases x
    {
      x := x - 1;
    }
    x := 3;
  }
}

const secAttack: Sec := High // Change as needed
const lattice: Lattice := map[Low := {Low, High}, High := {High}]

predicate order(l: Lattice, a: Sec, b: Sec)
  requires a in l
  requires b in l
{
  b in l[a]
}

method CAS<T(==)>(x: T, e1: T, e2: T)
    returns (b: bool, x2: T)
  ensures x == e1 ==> x2 == e2 && b
  ensures x != e1 ==> x2 == x && !b
{
  if x == e1 {
    x2 := e2;
    b := true;
  } else {
    x2 := x;
    b := false;
  }
}
