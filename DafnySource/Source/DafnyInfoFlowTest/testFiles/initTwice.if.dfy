// initTwice.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class TestInit {
  function method L_a(): Sec
  {
    FILL_THIS_IN
  }

  ghost var Gamma_a: Sec
  var a: int

  function method L_b(): Sec
  {
    FILL_THIS_IN
  }

  ghost var Gamma_b: Sec
  var b: string

  function method L_c(): Sec
  {
    FILL_THIS_IN
  }

  ghost var Gamma_c: Sec
  var c: bool

  predicate method Guaranteetest1()
    reads this
  {
    false
  }

  method Relytest1()
    modifies this
    ensures Gamma_a in lattice
    ensures L_a() in lattice
    ensures old(a) == a ==> old(Gamma_a) == Gamma_a
    ensures order(lattice, Gamma_a, L_a())
    ensures Gamma_b in lattice
    ensures L_b() in lattice
    ensures old(b) == b ==> old(Gamma_b) == Gamma_b
    ensures order(lattice, Gamma_b, L_b())
    ensures Gamma_c in lattice
    ensures L_c() in lattice
    ensures old(c) == c ==> old(Gamma_c) == Gamma_c
    ensures order(lattice, Gamma_c, L_c())

  method test1()
  {
  }
}

const secAttack: Sec := High // Change as needed
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
