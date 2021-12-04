class SeqLock {

  var x: int
  var z: int

  method SyncWrite(secret: int)
    requires z % 2 == 0
    modifies this
  {
    z := z + 1;
    x := secret;
    // wait until x is read
    x := 0;
    z := z + 1;
  }

  method SyncRead() returns (r: int)
  {
    return x;
  }

  method Write(data: int)
    modifies this
  {
    x := data;
  }


  method Read() returns (r: int)
    decreases *
  {
    var r1: int;
    var r2: int;
    //do
      //do
      r1 := z;
      //while
      while r1 % 2 != 0
        decreases *
      {
        r1 := z;
      }
      r2 := x;
    //while
    while z != r1
      decreases *
    {
      //do
      r1 := z;
      //while
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
