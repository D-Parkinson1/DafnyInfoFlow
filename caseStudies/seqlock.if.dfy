// seqLock.dfy

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

  function method L_x(): Sec
    reads this
  {
    if (z % 2 == 0) then Low else High
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
    z := z + 1;
    x := secret;
    x := 0;
    z := z + 1;
  }

  twostate predicate GuaranteeSyncRead()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z && order(lattice, old(Gamma_x), Gamma_x)
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
  {
    return x;
  }

  twostate predicate GuaranteeWrite()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z && order(lattice, old(Gamma_x), Gamma_x)
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
    x := data;
  }

  twostate predicate GuaranteeRead()
    requires Gamma_x in lattice
    requires Gamma_z in lattice
    reads this
  {
    order(lattice, Gamma_x, L_x()) &&
    order(lattice, Gamma_z, L_z()) &&
    old(z) == z && order(lattice, old(Gamma_x), Gamma_x)
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
    decreases *
  {
    var r1: int;
    var r2: int;
    r1 := z;
    while r1 % 2 != 0
      decreases *
    {
      r1 := z;
    }
    r2 := x;
    while z != r1
      decreases *
    {
      r1 := z;
      while r1 % 2 != 0
        decreases *
      {
        r1 := z;
      }
      r2 := x;
    }
    return r2;
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
