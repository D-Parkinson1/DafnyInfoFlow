class SyncLock {

    var X: int; 
    var Z:int;

    method Write(data: int) 
        modifies this;
    { 
        X := data;
    }

    method SyncWrite(secret: int)
        modifies this
        decreases *;
    {
        // CAS is part of while loop for reasoning purposes
        var b;
        b, Z := CAS(Z, 0, 1);
        while (!b) 
            decreases *
        {
            while (Z != 0) 
                decreases * 
            {}
            b, Z := CAS(Z, 0, 1);
        }
       
        X := secret;
        
        X := 0;
        
        Z := 0;
    }

    method Read() returns (y: int) 
    {
        return X;
    }

    method SyncRead() returns (y: int) 
        modifies this;
    {
        var b;
        b, Z := CAS(Z, 0, 2);
        if (b) {
            y := X;
            Z := 0; 
            return y;
        }
    }
}

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









