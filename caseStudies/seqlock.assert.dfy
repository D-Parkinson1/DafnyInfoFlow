// seqLock.if.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class SeqLock {
  var Read_return_r: int
  var Gamma_Read_return_r: Sec

  function method L_Read_return_r(): Sec
  {
    Low
  }

  var Write_In_data: int
  var Gamma_Write_In_data: Sec

  function method L_Write_In_data(): Sec
  {
    Low
  }

  var SyncRead_return_r: int
  var Gamma_SyncRead_return_r: Sec

  function method L_SyncRead_return_r(): Sec
  {
    High
  }

  var SyncWrite_In_secret: int
  var Gamma_SyncWrite_In_secret: Sec

  function method L_SyncWrite_In_secret(): Sec
  {
    High
  }

  function method L_x(z_in: int := z): Sec
    reads this
  {
    if z_in % 2 == 0 then
      Low
    else
      High
  }

  var Gamma_x: Sec
  var x: int

  function method L_z(): Sec
  {
    Low
  }

  var Gamma_z: Sec
  var z: int

  twostate predicate GuaranteeSyncWrite()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) <= z
  }

  method RelySyncWrite()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())
    ensures Gamma_z in lattice
    ensures L_z() in lattice
    ensures old(z) == z ==> old(Gamma_z) == Gamma_z
    ensures order(lattice, Gamma_z, L_z())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures old(z) == z && order(lattice, old(Gamma_x), Gamma_x)

  method SyncWrite(secret: int)
    requires z % 2 == 0
    modifies this
  {
    Gamma_SyncWrite_In_secret := High;
    RelySyncWrite();
    assert order(lattice, meet(Gamma_z, L_z()), L_z()) && order(lattice, meet(Gamma_x, L_x()), L_x(z + 1));
    label 0:
    z, Gamma_z := z + 1, meet(Gamma_z, L_z());
    assert GuaranteeSyncWrite@0();
    RelySyncWrite();
    assert order(lattice, meet(Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret()), L_x());
    label 1:
    x, Gamma_x := secret, meet(Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret());
    assert GuaranteeSyncWrite@1();
    RelySyncWrite();
    assert order(lattice, Low, L_x());
    label 2:
    x, Gamma_x := 0, Low;
    assert GuaranteeSyncWrite@2();
    RelySyncWrite();
    assert order(lattice, meet(Gamma_z, L_z()), L_z()) && order(lattice, meet(Gamma_x, L_x()), L_x(z + 1));
    label 3:
    z, Gamma_z := z + 1, meet(Gamma_z, L_z());
    assert GuaranteeSyncWrite@3();
  }

  twostate predicate GuaranteeSyncRead()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z &&
    order(lattice, old(Gamma_x), Gamma_x)
  }

  method RelySyncRead()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())
    ensures Gamma_z in lattice
    ensures L_z() in lattice
    ensures old(z) == z ==> old(Gamma_z) == Gamma_z
    ensures order(lattice, Gamma_z, L_z())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures Gamma_SyncRead_return_r in lattice
    ensures L_SyncRead_return_r() in lattice
    ensures old(SyncRead_return_r) == SyncRead_return_r ==> old(Gamma_SyncRead_return_r) == Gamma_SyncRead_return_r
    ensures order(lattice, Gamma_SyncRead_return_r, L_SyncRead_return_r())

  method SyncRead() returns (r: int)
    modifies this
  {
    Gamma_SyncRead_return_r := High;
    RelySyncRead();
    assert order(lattice, meet(Gamma_x, L_x()), L_SyncRead_return_r());
    label 0:
    return x;
    assert GuaranteeSyncRead@0();
  }

  twostate predicate GuaranteeWrite()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z &&
    order(lattice, old(Gamma_x), Gamma_x)
  }

  method RelyWrite()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())
    ensures Gamma_z in lattice
    ensures L_z() in lattice
    ensures old(z) == z ==> old(Gamma_z) == Gamma_z
    ensures order(lattice, Gamma_z, L_z())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures Gamma_SyncRead_return_r in lattice
    ensures L_SyncRead_return_r() in lattice
    ensures old(SyncRead_return_r) == SyncRead_return_r ==> old(Gamma_SyncRead_return_r) == Gamma_SyncRead_return_r
    ensures order(lattice, Gamma_SyncRead_return_r, L_SyncRead_return_r())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())

  method Write(data: int)
    modifies this
  {
    Gamma_Write_In_data := High;
    RelyWrite();
    assert order(lattice, meet(Gamma_Write_In_data, L_Write_In_data()), L_x());
    label 0:
    x, Gamma_x := data, meet(Gamma_Write_In_data, L_Write_In_data());
    assert GuaranteeWrite@0();
  }

  twostate predicate GuaranteeRead()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z &&
    order(lattice, old(Gamma_x), Gamma_x)
  }

  method RelyRead()
    modifies this
    ensures Gamma_x in lattice
    ensures L_x() in lattice
    ensures old(x) == x ==> old(Gamma_x) == Gamma_x
    ensures order(lattice, Gamma_x, L_x())
    ensures Gamma_z in lattice
    ensures L_z() in lattice
    ensures old(z) == z ==> old(Gamma_z) == Gamma_z
    ensures order(lattice, Gamma_z, L_z())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures Gamma_SyncRead_return_r in lattice
    ensures L_SyncRead_return_r() in lattice
    ensures old(SyncRead_return_r) == SyncRead_return_r ==> old(Gamma_SyncRead_return_r) == Gamma_SyncRead_return_r
    ensures order(lattice, Gamma_SyncRead_return_r, L_SyncRead_return_r())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())
    ensures Gamma_Read_return_r in lattice
    ensures L_Read_return_r() in lattice
    ensures old(Read_return_r) == Read_return_r ==> old(Gamma_Read_return_r) == Gamma_Read_return_r
    ensures order(lattice, Gamma_Read_return_r, L_Read_return_r())
    ensures z >= old(z)

  method Read() returns (r: int)
    modifies this
    decreases *
  {
    Gamma_Read_return_r := High;
    RelyRead();
    label 0:
    var r1: int, Gamma_r1: Sec;
    assert GuaranteeRead@0();
    RelyRead();
    label 1:
    var r2: int, Gamma_r2: Sec;
    assert GuaranteeRead@1();
    RelyRead();
    assert true;
    label 2:
    r1, Gamma_r1 := z, meet(Gamma_z, L_z());
    assert GuaranteeRead@2();
    RelyRead();
    assert true ==> order(lattice, meet(Gamma_r1, High), secAttack);
    label 4:
    while r1 % 2 != 0
      invariant Gamma_z in lattice
      invariant Gamma_x in lattice
      invariant GuaranteeRead@4()
      decreases *
    {
      RelyRead();
      assert true;
      label 3:
      r1, Gamma_r1 := z, meet(Gamma_z, L_z());
      assert GuaranteeRead@3();
    }
    assert GuaranteeRead@4();
    RelyRead();
    assert true;
    label 5:
    r2, Gamma_r2 := x, meet(Gamma_x, L_x());
    assert GuaranteeRead@5();
    RelyRead();
    assert true ==> order(lattice, join(meet(Gamma_r1, High), meet(Gamma_z, L_z())), secAttack);
    label 10:
    while z != r1
      invariant Gamma_z in lattice
      invariant Gamma_x in lattice
      invariant GuaranteeRead@10()
      decreases *
    {
      RelyRead();
      assert true;
      label 6:
      r1, Gamma_r1 := z, meet(Gamma_z, L_z());
      assert GuaranteeRead@6();
      RelyRead();
      assert true ==> order(lattice, meet(Gamma_r1, High), secAttack);
      label 8:
      while r1 % 2 != 0
        invariant Gamma_z in lattice
        invariant Gamma_x in lattice
        invariant GuaranteeRead@8()
        decreases *
      {
        RelyRead();
        assert true;
        label 7:
        r1, Gamma_r1 := z, meet(Gamma_z, L_z());
        assert GuaranteeRead@7();
      }
      assert GuaranteeRead@8();
      RelyRead();
      assert true;
      label 9:
      r2, Gamma_r2 := x, meet(Gamma_x, L_x());
      assert GuaranteeRead@9();
    }
    assert GuaranteeRead@10();
    RelyRead();
    assert order(lattice, meet(Gamma_r2, High), L_Read_return_r());
    label 11:
    return r2;
    assert GuaranteeRead@11();
  }
}

const secAttack: Sec := Low // Change as needed
const lattice: Lattice := map[Low := {Low, High}, High := {High}]

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
