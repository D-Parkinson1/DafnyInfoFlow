// dafnyDriverTest.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class YourClass {
  function method L_x(): Sec
  {
    Low
  }

  ghost var Gamma_x: Sec
  var x: int

  method Relytest()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())

  twostate predicate Guaranteetest()
    requires Gamma_x in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x())
  }

  method test()
    modifies this
    decreases *
  {
    Relytest();
    assert order(lattice, Low, L_x());
    label 0:
    x, Gamma_x := 5, Low;
    assert Guaranteetest@0();
    Relytest();
    assert order(lattice, Low, secAttack);
    label 2:
    if true {
      Relytest();
      assert order(lattice, Low, L_x());
      label 1:
      x, Gamma_x := 7, Low;
      assert Guaranteetest@1();
    }
    assert Guaranteetest@2();
    Relytest();
    assert true ==> order(lattice, meet[(Gamma_x, L_x())], secAttack);
    label 4:
    while x > 3
      decreases *
    {
      Relytest();
      assert order(lattice, meet[(Gamma_x, L_x())], L_x());
      label 3:
      x, Gamma_x := x - 1, meet[(Gamma_x, L_x())];
      assert Guaranteetest@3();
    }
    assert Guaranteetest@4();
    Relytest();
    assert order(lattice, Low, L_x());
    label 5:
    x, Gamma_x := 3, Low;
    assert Guaranteetest@5();
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

const join: map<(Sec, Sec), Sec> := map[(Low, Low) := Low, (Low, High) := High, (High, Low) := High, (High, High) := High]
const meet: map<(Sec, Sec), Sec> := map[(Low, Low) := Low, (Low, High) := Low, (High, Low) := Low, (High, High) := High]
