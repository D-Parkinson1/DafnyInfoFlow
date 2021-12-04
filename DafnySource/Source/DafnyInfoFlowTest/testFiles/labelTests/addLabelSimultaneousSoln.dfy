// addLabelSimultaneousTest.dfy

method multiLabelSimultaneousAssign(x: int) {
    label multiLabelSimultaneousAssign_1:
    var a := 3;
    label multiLabelSimultaneousAssign_2:
    var r := a + x;
    label multiLabelSimultaneousAssign_3:
    a := 2;
    label multiLabelSimultaneousAssign_4:
    r, a := a + r, r;
}