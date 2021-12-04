method multiLabelSimultaneousAssign(x: int) {
    var a := 3;
    var r := a + x;
    a := 2;
    r, a := a + r, r;
}