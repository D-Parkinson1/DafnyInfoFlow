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

  function method L_X(): Sec
    reads this
  {
    if Z % 2 == 0 then
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
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    (old(Z) == Z) && order(lattice, Gamma_X, old(Gamma_X))
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
    X := data;
  }

  twostate predicate GuaranteeSyncWrite()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    ((old(Z) == 2) ==> (old(Z) == Z && old(X) == X))
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
    ensures order(lattice, Gamma_X, old(Gamma_X)) && (old(Z) == 1 ==> old(Z) == Z)

  method SyncWrite(secret: int)
    modifies this
    decreases *
  {
    var b;
    b, Z := CAS(Z, 0, 1);
    while !b
      decreases *
    {
      while Z != 0
        decreases *
      {
      }
      b, Z := CAS(Z, 0, 1);
    }
    X := secret;
    X := 0;
    Z := 0;
  }

  twostate predicate GuaranteeRead()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    (old(Z) == Z && (old(X) == X))
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
  {
    return X;
  }

  twostate predicate GuaranteeSyncRead()
    requires Gamma_X in lattice
    requires Gamma_Z in lattice
    reads this
  {
    order(lattice, Gamma_X, L_X()) &&
    order(lattice, Gamma_Z, L_Z()) &&
    (old(X) == X && (old(Z) == 1 ==> (old(Z) == Z)))
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
    ensures (old(Z) == 2 ==> old(Z) == Z && order(lattice, Gamma_X, old(Gamma_X)))

  method SyncRead() returns (y: int)
    modifies this
  {
    var b;
    b, Z := CAS(Z, 0, 2);
    if b {
      y := X;
      Z := 0;
      return y;
    }
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
