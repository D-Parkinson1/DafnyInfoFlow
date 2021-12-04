// addLabelWhileTest.dfy

method labelWhile() {
    label labelWhile_1:
    var b := 7;
    label labelWhile_2:
    while (b > 1) 
        decreases b
    {
        label labelWhile_3:
        b := b - 1;
    }
}