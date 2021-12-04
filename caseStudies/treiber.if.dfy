// treiber.dfy

datatype Sec = Low | High

datatype Node = Node(next: Node, value: int, level: Sec) | Nil

type Lattice = map<Sec, set<Sec>>

class Treiber {
  var pop_return_v: int
  var Gamma_pop_return_v: Sec

  function method L_pop_return_v(): Sec
  {
    Low
  }

  var put_In_level: Sec
  var Gamma_put_In_level: Sec

  function method L_put_In_level(): Sec
  {
    Low
  }

  var put_In_v: int
  var Gamma_put_In_v: Sec

  function method L_put_In_v(): Sec
  reads this
  {
    put_In_level
  }

  function method L_head(): Sec
  {
    Low
  }

  var Gamma_head: Sec
  var head: Node

  twostate predicate Guaranteeput()
    requires Gamma_head in lattice
    reads this
  {
    order(lattice, Gamma_head, L_head())
  }

  method Relyput()
    modifies this
    ensures Gamma_head in lattice
    ensures L_head() in lattice
    ensures old(head) == head ==> old(Gamma_head) == Gamma_head
    ensures order(lattice, Gamma_head, L_head())
    ensures Gamma_put_In_v in lattice
    ensures L_put_In_v() in lattice
    ensures old(put_In_v) == put_In_v ==> old(Gamma_put_In_v) == Gamma_put_In_v
    ensures order(lattice, Gamma_put_In_v, L_put_In_v())
    ensures Gamma_put_In_level in lattice
    ensures L_put_In_level() in lattice
    ensures old(put_In_level) == put_In_level ==> old(Gamma_put_In_level) == Gamma_put_In_level
    ensures order(lattice, Gamma_put_In_level, L_put_In_level())

  method put(v: int, level: Sec)
    modifies this
    decreases *
  {
    assume head.Node?;
    var n := Node(Nil, v, level);
    var ss: Node;
    ss := head;
    n := n.(next := ss);
    var b;
    b, head := CAS<Node>(head, ss, n);
    while !b
      decreases *
    {
      ss := head;
      n := n.(next := ss);
    }
  }

  twostate predicate Guaranteepop()
    requires Gamma_head in lattice
    reads this
  {
    order(lattice, Gamma_head, L_head())
  }

  method Relypop()
    modifies this
    ensures Gamma_head in lattice
    ensures L_head() in lattice
    ensures old(head) == head ==> old(Gamma_head) == Gamma_head
    ensures order(lattice, Gamma_head, L_head())
    ensures Gamma_put_In_v in lattice
    ensures L_put_In_v() in lattice
    ensures old(put_In_v) == put_In_v ==> old(Gamma_put_In_v) == Gamma_put_In_v
    ensures order(lattice, Gamma_put_In_v, L_put_In_v())
    ensures Gamma_put_In_level in lattice
    ensures L_put_In_level() in lattice
    ensures old(put_In_level) == put_In_level ==> old(Gamma_put_In_level) == Gamma_put_In_level
    ensures order(lattice, Gamma_put_In_level, L_put_In_level())
    ensures Gamma_pop_return_v in lattice
    ensures L_pop_return_v() in lattice
    ensures old(pop_return_v) == pop_return_v ==> old(Gamma_pop_return_v) == Gamma_pop_return_v
    ensures order(lattice, Gamma_pop_return_v, L_pop_return_v())

  method pop() returns (v: int)
    modifies this
    decreases *
  {
    assume head.Node?;
    var level: Sec;
    var exit := 0;
    var ss, ssn, n: Node;
    ss := head;
    if !ss.Nil? {
      level := ss.level;
      if level.Low? {
        ssn := ss.next;
        v := ss.value;
        var b;
        b, head := CAS<Node>(head, ss, ssn);
        if b {
          exit := 1;
        }
      }
    }
    while exit == 0
      decreases *
    {
      ss := head;
      if !ss.Nil? {
        level := ss.level;
        if level == Low {
          ssn := ss.next;
          v := ss.value;
          var b;
          b, head := CAS<Node>(head, ss, ssn);
          if b {
            exit := 1;
          }
        }
      }
    }
  }
}

const secAttack: Sec := Low // Change as needed

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

const lattice: Lattice := map[Low := {Low, High}, High := {High}]

predicate order(l: Lattice, a: Sec, b: Sec)
{
  assume a in l && b in l;
  b in l[a]
}
