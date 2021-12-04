// addManyLabelTest.dfy

method multiLabel(x: int) {
    label multiLabel_1:
    var a := 3;
    label multiLabel_2:
    var r := a + x;
    label multiLabel_3:
    a := 2;
}