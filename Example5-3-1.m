
R<x> := PolynomialRing(Integers());
g := x^2 - x;
h := x^3 + 7*x^2 - 9*x + 7; //psi is given by [h, g]
f := g * (h^3 - h*g^2 + g^3);
E := EllipticCurve(x^3 - x + 1);
C := HyperellipticCurve(f);
J := Jacobian(C);
disc := Discriminant(f);

assert RankBound(J) eq 1; //takes some time

assert Integers()!(#Jacobian(ChangeRing(C,GF(5)))/#ChangeRing(E, GF(5))) eq 2^3*3*29;
assert Integers()!(#Jacobian(ChangeRing(C,GF(13)))/#ChangeRing(E, GF(13))) eq 2^2*17*311;
