// dafnyDriverTest.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class Test {
  ghost var testReturn_return_x: int
  ghost var Gamma_testReturn_return_x: Sec

  function method L_x(): Sec
  {
    if y then  High else Low
  }

  ghost var Gamma_x: Sec
  var x: int

  function method L_y(): Sec
  {
    High
  }

  ghost var Gamma_y: Sec
  var y: bool

  function method L_z(): Sec
  {
    Low
  }

  ghost var Gamma_z: Sec
  var z: string

  method testReturn() returns (x: int)
  {
    x, Gamma_x := 7, High;
    return x;
  }

  method start()
    modifies this
  {
    x, Gamma_x := 0, High;
    x, Gamma_x := 7, Low;
    z, Gamma_z := "TEST", Low;
    y, Gamma_y := true, High;
    x, Gamma_x := 0, Low;
  }
}

method commonSupremum(l: Lattice, a: Sec, b: Sec)
    returns (r: Sec)
  requires a in l
  requires b in l
  requires l[a] <= l.Keys
  requires l[b] <= l.Keys
  ensures r in l.Keys
  ensures r in l[b] && r in l[a]
{
  var intersection := l[a] * l[b];
  assert intersection <= l.Keys;
  var min: int := 100;
  while intersection != {}
    invariant intersection <= l.Keys
    decreases |intersection|
  {
    var sec: Sec :| sec in intersection;
    if |l[sec]| < min {
      r := sec;
    }
    intersection := intersection - {sec};
  }
  assume r in l[a] && r in l[b];
  return r;
}

method join(l: Lattice, a: Sec, b: Sec)
    returns (s: Sec)
  requires a in l
  requires b in l
  requires l[a] <= l.Keys
  requires l[b] <= l.Keys
  ensures a in l[b] ==> s == a
  ensures a !in l[b] && b in l[a] ==> s == b
  ensures a !in l[b] && b !in l[a] ==> s in l[a] && s in l[b] && s != a && s != b
  ensures s in l
{
  if a in l[b] {
    s := a;
  } else if b in l[a] {
    s := b;
  } else {
    s := commonSupremum(l, a, b);
  }
}

const lattice: Lattice := map[Low := {Low, High}, High:={High}]

predicate order(l: Lattice, a: Sec, b: Sec)
  requires a in l
  requires b in l
{
  b in l[a]
}

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
