// dafnyDriverTest.dfy

// datatype Sec = Low | High

// type Lattice = map<Sec, set<Sec>>

class YourClass {
  // function method L_x(): Sec
  // {
  //   Low
  // }

  var x: int
  var z: int
  
  method test()
    modifies this
  {
    x := 5;

    if (true) {
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

// const secAttack: Sec := High // Change as needed
// const lattice: Lattice := map[Low := {Low, High}, High := {High}]

// method CAS<T(==)>(x: T, e1: T, e2: T)
//     returns (b: bool, x2: T)
//   ensures x == e1 ==> x2 == e2
//   ensures x != e1 ==> x2 == x
// {
//   if x == e1 {
//     x2 := e2;
//     b := false;
//   } else {
//     x2 := x;
//     b := true;
//   }
// }

// predicate order(l: Lattice, a: Sec, b: Sec)
//   requires a in l
//   requires b in l
// {
//   b in l[a]
// }
