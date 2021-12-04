// addLabelIfSoln.dfy

method labelIf(a: bool) returns (y:nat) {
    label labelIf_1:
    if (a) {
        label labelIf_2:
        y := 32;
    } else {
        label labelIf_3:
        y := 3;
    }
}