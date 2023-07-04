method div_ent_rec(a: int, b: int) returns (c: int, r: int)

// Algoritmo recursivo de la división de enteros
// que calcula su cociente y resto

    requires a >= 0 && b > 0
    ensures  a == b*c + r && 0 <= r < b
    decreases a
{
    if (a < b) { c := 0; r := a ;}
    else { c, r := div_ent_rec(a - b, b); c := c + 1 ;}
}

method Main()
{
    var c, r := div_ent_rec(9, 2) ;
    print "Cociente: ", c, ", Resto: ", r ;
}