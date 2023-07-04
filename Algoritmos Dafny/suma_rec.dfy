function suma_vector(V : array<int>, n : nat) : int

// x = V[n] + V[n + 1] + ... + V[N - 1]
// Funcion auxiliar para la suma de
// las componentes de un vector

    requires  0 <= n <= V.Length
    decreases n
    reads V
{
    if n == 0 then 0
    else suma_vector(V, n - 1) + V[n - 1]
}

method suma_rec(V : array<int>) returns (x : int)

// Algoritmo recursivo que calcula la
// suma de las componentes de un vector

    ensures  x == suma_vector(V, V.Length)
{
    x := gsuma_rec(V, V.Length) ;
}

method gsuma_rec(V : array<int>, n : nat) returns (x : int)
    requires  0 <= n <= V.Length
    ensures   x == suma_vector(V, n)
    decreases n
{
    if n == 0 { x := 0 ;}
    else {
        var y : int ;
        y := gsuma_rec(V, n - 1) ;
        x := y + V[n - 1] ;
    }
}

method Main()
{
    var v := new int[] [-1, 2, 5, -5, 8] ;
    var w := new int[] [ 1, 0, 5,  5, 8] ;
    var s1 := suma_rec(v) ;
    var s2 := suma_rec(w) ;

    print "La suma del vector v es: ", s1, "\n" ;
    print "La suma del vector w es: ", s2 ;
}