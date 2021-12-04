// treiber.if.dfy

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

  function method L_put_In_v(put_In_level_in: Sec := put_In_level): Sec
    reads this
  {
    put_In_level_in
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
    Gamma_put_In_level := High;
    Gamma_put_In_v := High;
    Relyput();
    label 0:
    assume head.Node?;
    assert Guaranteeput@0();
    Relyput();
    assert true;
    var Gamma_n: Sec;
    label 1:
    var n := Node(Nil, v, level);
    assert Guaranteeput@1();
    Relyput();
    var Gamma_ss: Sec;
    label 2:
    var ss: Node;
    assert Guaranteeput@2();
    Relyput();
    assert true;
    label 3:
    ss, Gamma_ss := head, meet(Gamma_head, L_head());
    assert Guaranteeput@3();
    Relyput();
    assert true;
    label 4:
    n, Gamma_n := n.(next := ss), Low;
    assert Guaranteeput@4();
    Relyput();
    var Gamma_b: Sec;
    label 5:
    var b;
    assert Guaranteeput@5();
    Relyput();
    assert head == ss ==> order(lattice, join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), secAttack);
    label 6:
    b, head := CAS<Node>(head, ss, n);
    assert Guaranteeput@6();
    Gamma_b, Gamma_head := join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), if head == ss then meet(Gamma_ss, High) else Gamma_head;
    Relyput();
    assert true ==> order(lattice, meet(Gamma_b, High), secAttack);
    label 9:
    while !b
      invariant Gamma_head in lattice
      // invariant b ==> head == n
      invariant Guaranteeput@9()
      decreases *
    {
      Relyput();
      assert true;
      label 7:
      ss, Gamma_ss := head, meet(Gamma_head, L_head());
      assert Guaranteeput@7();
      Relyput();
      assert true;
      label 8:
      assume n.Node?;
      n, Gamma_n := n.(next := ss), Low;
      assert Guaranteeput@8();
    }
    assert Guaranteeput@9();
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
    Gamma_pop_return_v := High;
    Relypop();
    label 0:
    assume head.Node?;
    assert Guaranteepop@0();
    Relypop();
    var Gamma_level: Sec;
    label 1:
    var level: Sec;
    assert Guaranteepop@1();
    Relypop();
    assert true;
    var Gamma_exit: Sec := Low;
    label 2:
    var exit := 0;
    assert Guaranteepop@2();
    Relypop();
    var Gamma_n: Sec;
    var Gamma_ssn: Sec;
    var Gamma_ss: Sec;
    label 3:
    var ss, ssn, n: Node;
    assert Guaranteepop@3();
    Relypop();
    assert true;
    label 4:
    ss, Gamma_ss := head, meet(Gamma_head, L_head());
    assert Guaranteepop@4();
    Relypop();
    assert order(lattice, Low, secAttack);
    label 13:
    if !ss.Nil? {
      Relypop();
      assert true;
      label 5:
      level, Gamma_level := ss.level, Low;
      assert Guaranteepop@5();
      Relypop();
      assert order(lattice, Low, secAttack);
      label 12:
      if level.Low? {
        Relypop();
        assert true;
        label 6:
        ssn, Gamma_ssn := ss.next, Low;
        assert Guaranteepop@6();
        Relypop();
        assert order(lattice, Low, L_pop_return_v());
        label 7:
        v, Gamma_pop_return_v := ss.value, Low;
        assert Guaranteepop@7();
        Relypop();
        var Gamma_b: Sec;
        label 8:
        var b;
        assert Guaranteepop@8();
        Relypop();
        assert head == ss ==> order(lattice, join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), secAttack);
        label 9:
        b, head := CAS<Node>(head, ss, ssn);
        assert Guaranteepop@9();
        Gamma_b, Gamma_head := join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), if head == ss then meet(Gamma_ss, High) else Gamma_head;
        Relypop();
        assert order(lattice, meet(Gamma_b, High), secAttack);
        label 11:
        if b {
          Relypop();
          assert true;
          label 10:
          exit, Gamma_exit := 1, Low;
          assert Guaranteepop@10();
        }
        assert Guaranteepop@11();
      }
      assert Guaranteepop@12();
    }
    assert Guaranteepop@13();
    Relypop();
    assert true ==> order(lattice, meet(Gamma_exit, High), secAttack);
    label 24:
    while exit == 0
      invariant Gamma_head in lattice
      invariant Guaranteepop@24()
      decreases *
    {
      Relypop();
      assert true;
      label 14:
      ss, Gamma_ss := head, meet(Gamma_head, L_head());
      assert Guaranteepop@14();
      Relypop();
      assert order(lattice, Low, secAttack);
      label 23:
      if !ss.Nil? {
        Relypop();
        assert true;
        label 15:
        level, Gamma_level := ss.level, Low;
        assert Guaranteepop@15();
        Relypop();
        assert order(lattice, join(Low, meet(Gamma_level, High)), secAttack);
        label 22:
        if level == Low {
          Relypop();
          assert true;
          label 16:
          ssn, Gamma_ssn := ss.next, Low;
          assert Guaranteepop@16();
          Relypop();
          assert order(lattice, Low, L_pop_return_v());
          label 17:
          v, Gamma_pop_return_v := ss.value, Low;
          assert Guaranteepop@17();
          Relypop();
          var Gamma_b: Sec;
          label 18:
          var b;
          assert Guaranteepop@18();
          Relypop();
          assert head == ss ==> order(lattice, join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), secAttack);
          label 19:
          b, head := CAS<Node>(head, ss, ssn);
          assert Guaranteepop@19();
          Gamma_b, Gamma_head := join(meet(Gamma_ss, High), meet(Gamma_head, L_head())), if head == ss then meet(Gamma_ss, High) else Gamma_head;
          Relypop();
          assert order(lattice, meet(Gamma_b, High), secAttack);
          label 21:
          if b {
            Relypop();
            assert true;
            label 20:
            exit, Gamma_exit := 1, Low;
            assert Guaranteepop@20();
          }
          assert Guaranteepop@21();
        }
        assert Guaranteepop@22();
      }
      assert Guaranteepop@23();
    }
    assert Guaranteepop@24();
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

const joinMap: map<(Sec, Sec), Sec> := map[(Low, Low) := Low, (Low, High) := High, (High, Low) := High, (High, High) := High]

function method join(a: Sec, b: Sec): Sec
{
  assume a in lattice && b in lattice;
  joinMap[(a, b)]
}

const meetMap: map<(Sec, Sec), Sec> := map[(Low, Low) := Low, (Low, High) := Low, (High, Low) := Low, (High, High) := High]

function method meet(a: Sec, b: Sec): Sec
{
  assume a in lattice && b in lattice;
  meetMap[(a, b)]
}
