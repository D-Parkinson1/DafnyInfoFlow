// syncLock.if.dfy

datatype Sec = Low | High

type Lattice = map<Sec, set<Sec>>

class SyncLock {
  var SyncRead_return_y: int
  var Gamma_SyncRead_return_y: Sec

  function method L_SyncRead_return_y(): Sec
  {
    Low
  }

  var Read_return_y: int
  var Gamma_Read_return_y: Sec

  function method L_Read_return_y(): Sec
  {
    High
  }

  var SyncWrite_In_secret: int
  var Gamma_SyncWrite_In_secret: Sec

  function method L_SyncWrite_In_secret(): Sec
  {
    High
  }

  var Write_In_data: int
  var Gamma_Write_In_data: Sec

  function method L_Write_In_data(): Sec
  {
    Low
  }

  function method L_X(Z_in: int := Z): Sec
    reads this
  {
    if Z_in != 1 then
      Low
    else
      High
  }

  var Gamma_X: Sec
  var X: int

  function method L_Z(): Sec
  {
    Low
  }

  var Gamma_Z: Sec
  var Z: int

  twostate predicate GuaranteeWrite()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    requires old(Gamma_X) in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    old(Z) == Z &&
    order(lattice, Gamma_X, old(Gamma_X))
  }

  method RelyWrite()
    modifies this
    ensures Gamma_X in lattice
    ensures L_X() in lattice
    ensures old(X) == X ==> old(Gamma_X) == Gamma_X
    ensures order(lattice, Gamma_X, L_X())
    ensures Gamma_Z in lattice
    ensures L_Z() in lattice
    ensures old(Z) == Z ==> old(Gamma_Z) == Gamma_Z
    ensures order(lattice, Gamma_Z, L_Z())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())
    ensures old(Gamma_X) in lattice

  method Write(data: int)
    modifies this
  {
    Gamma_Write_In_data := High;
    RelyWrite();
    assert order(lattice, meet(Gamma_Write_In_data, L_Write_In_data()), L_X());
    label 0:
    X, Gamma_X := data, meet(Gamma_Write_In_data, L_Write_In_data());
    assert GuaranteeWrite@0();
  }

  twostate predicate GuaranteeSyncWrite()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    (old(Z) == 2 ==>
      old(Z) == Z &&
      old(X) == X)
  }

  method RelySyncWrite()
    modifies this
    ensures Gamma_X in lattice
    ensures L_X() in lattice
    ensures old(X) == X ==> old(Gamma_X) == Gamma_X
    ensures order(lattice, Gamma_X, L_X())
    ensures Gamma_Z in lattice
    ensures L_Z() in lattice
    ensures old(Z) == Z ==> old(Gamma_Z) == Gamma_Z
    ensures order(lattice, Gamma_Z, L_Z())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures old(Gamma_X) in lattice
    ensures order(lattice, Gamma_X, old(Gamma_X)) && (old(Z) == 1 ==> old(Z) == Z)

  method SyncWrite(secret: int)
    modifies this
    decreases *
  {
    Gamma_SyncWrite_In_secret := High;
    RelySyncWrite();
    label 0:
    var b, Gamma_b: Sec;
    assert GuaranteeSyncWrite@0();
    RelySyncWrite();
    assert Z == 0 ==> order(lattice, meet(Gamma_Z, L_Z()), secAttack);
    label 1:
    b, Z := CAS(Z, 0, 1);
    assert GuaranteeSyncWrite@1();
    Gamma_b, Gamma_Z := meet(Gamma_Z, L_Z()), if Z == 0 then Low else Gamma_Z;
    RelySyncWrite();
    assert true ==> order(lattice, meet(Gamma_b, High), secAttack);
    label 4:
    while !b
      invariant Gamma_Z in lattice
      invariant Gamma_X in lattice
      invariant b ==> Z == 1
      invariant GuaranteeSyncWrite@4()
      decreases *
    {
      RelySyncWrite();
      assert true ==> order(lattice, meet(Gamma_Z, L_Z()), secAttack);
      label 2:
      while Z != 0
        invariant Gamma_Z in lattice
        invariant Gamma_X in lattice
        invariant GuaranteeSyncWrite@2()
        decreases *
      {
      }
      assert GuaranteeSyncWrite@2();
      RelySyncWrite();
      assert Z == 0 ==> order(lattice, meet(Gamma_Z, L_Z()), secAttack);
      label 3:
      b, Z := CAS(Z, 0, 1);
      assert GuaranteeSyncWrite@3();
      Gamma_b, Gamma_Z := meet(Gamma_Z, L_Z()), if Z == 0 then Low else Gamma_Z;
    }
    assert GuaranteeSyncWrite@4();
    RelySyncWrite();
    assert order(lattice, meet(Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret()), L_X());
    label 5:
    X, Gamma_X := secret, meet(Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret());
    assert GuaranteeSyncWrite@5();
    RelySyncWrite();
    assert order(lattice, Low, L_X());
    label 6:
    X, Gamma_X := 0, Low;
    assert GuaranteeSyncWrite@6();
    RelySyncWrite();
    assert order(lattice, Low, L_Z()) && order(lattice, meet(Gamma_X, L_X()), L_X(0));
    label 7:
    Z, Gamma_Z := 0, Low;
    assert GuaranteeSyncWrite@7();
  }

  twostate predicate GuaranteeRead()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    old(Z) == Z &&
    old(X) == X
  }

  method RelyRead()
    modifies this
    ensures Gamma_X in lattice
    ensures L_X() in lattice
    ensures old(X) == X ==> old(Gamma_X) == Gamma_X
    ensures order(lattice, Gamma_X, L_X())
    ensures Gamma_Z in lattice
    ensures L_Z() in lattice
    ensures old(Z) == Z ==> old(Gamma_Z) == Gamma_Z
    ensures order(lattice, Gamma_Z, L_Z())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures Gamma_Read_return_y in lattice
    ensures L_Read_return_y() in lattice
    ensures old(Read_return_y) == Read_return_y ==> old(Gamma_Read_return_y) == Gamma_Read_return_y
    ensures order(lattice, Gamma_Read_return_y, L_Read_return_y())

  method Read() returns (y: int)
    modifies this
  {
    Gamma_Read_return_y := High;
    RelyRead();
    assert order(lattice, meet(Gamma_X, L_X()), L_Read_return_y());
    label 0:
    return X;
    assert GuaranteeRead@0();
  }

  twostate predicate GuaranteeSyncRead()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    old(X) == X &&
    (old(Z) == 1 ==>
      old(Z) == Z)
  }

  method RelySyncRead()
    modifies this
    ensures Gamma_X in lattice
    ensures L_X() in lattice
    ensures old(X) == X ==> old(Gamma_X) == Gamma_X
    ensures order(lattice, Gamma_X, L_X())
    ensures Gamma_Z in lattice
    ensures L_Z() in lattice
    ensures old(Z) == Z ==> old(Gamma_Z) == Gamma_Z
    ensures order(lattice, Gamma_Z, L_Z())
    ensures Gamma_Write_In_data in lattice
    ensures L_Write_In_data() in lattice
    ensures old(Write_In_data) == Write_In_data ==> old(Gamma_Write_In_data) == Gamma_Write_In_data
    ensures order(lattice, Gamma_Write_In_data, L_Write_In_data())
    ensures Gamma_SyncWrite_In_secret in lattice
    ensures L_SyncWrite_In_secret() in lattice
    ensures old(SyncWrite_In_secret) == SyncWrite_In_secret ==> old(Gamma_SyncWrite_In_secret) == Gamma_SyncWrite_In_secret
    ensures order(lattice, Gamma_SyncWrite_In_secret, L_SyncWrite_In_secret())
    ensures Gamma_Read_return_y in lattice
    ensures L_Read_return_y() in lattice
    ensures old(Read_return_y) == Read_return_y ==> old(Gamma_Read_return_y) == Gamma_Read_return_y
    ensures order(lattice, Gamma_Read_return_y, L_Read_return_y())
    ensures Gamma_SyncRead_return_y in lattice
    ensures L_SyncRead_return_y() in lattice
    ensures old(SyncRead_return_y) == SyncRead_return_y ==> old(Gamma_SyncRead_return_y) == Gamma_SyncRead_return_y
    ensures order(lattice, Gamma_SyncRead_return_y, L_SyncRead_return_y())
    ensures old(Gamma_X) in lattice
    ensures old(Z) == 2 ==> old(Z) == Z && order(lattice, Gamma_X, old(Gamma_X))

  method SyncRead() returns (y: int)
    modifies this
  {
    Gamma_SyncRead_return_y := High;
    RelySyncRead();
    label 0:
    var b, Gamma_b: Sec;
    assert GuaranteeSyncRead@0();
    RelySyncRead();
    assert Z == 0 ==> order(lattice, meet(Gamma_Z, L_Z()), secAttack);
    label 1:
    b, Z := CAS(Z, 0, 2);
    assert GuaranteeSyncRead@1();
    Gamma_b, Gamma_Z := meet(Gamma_Z, L_Z()), if Z == 0 then Low else Gamma_Z;
    RelySyncRead();
    assert order(lattice, meet(Gamma_b, High), secAttack);
    label 5:
    if b {
      RelySyncRead();
      assert order(lattice, meet(Gamma_X, L_X()), L_SyncRead_return_y());
      label 2:
      y, Gamma_SyncRead_return_y := X, meet(Gamma_X, L_X());
      assert GuaranteeSyncRead@2();
      RelySyncRead();
      assert order(lattice, Low, L_Z()) && order(lattice, meet(Gamma_X, L_X()), L_X(0));
      label 3:
      Z, Gamma_Z := 0, Low;
      assert GuaranteeSyncRead@3();
      RelySyncRead();
      assert order(lattice, meet(Gamma_SyncRead_return_y, L_SyncRead_return_y()), L_SyncRead_return_y());
      label 4:
      return y;
      assert GuaranteeSyncRead@4();
    }
    assert GuaranteeSyncRead@5();
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
