class Test {
    var x: int;
    
    method labelInClass() 
        modifies this
    {
        var y:= 3;
        x := x + y;
    }

    method label2InClass() returns (y: int) 
        modifies this
    {
        y := 3;
        x := x + y;
        y := x + 1;
        return y;
    }
    
}