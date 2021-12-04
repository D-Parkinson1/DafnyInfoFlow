method labelWhile() {
    var b := 7;
    while (b > 1) 
        decreases b
    {
        b := b - 1;
    }
}