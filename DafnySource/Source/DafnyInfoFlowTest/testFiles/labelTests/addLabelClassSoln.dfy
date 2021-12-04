// addLabelClassTest.dfy

class Test {
    var x: int;
    
    method labelInClass() 
        modifies this
    {
        label labelInClass_1:
        var y:= 3;
        label labelInClass_2:
        x := x + y;
    }

    method label2InClass() returns (y: int) 
        modifies this
    {
        label label2InClass_1:
        y := 3;
        label label2InClass_2:
        x := x + y;
        label label2InClass_3:
        y := x + 1;
        return y;
    }
}