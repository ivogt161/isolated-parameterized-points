
R<x> := PolynomialRing(RationalField());
g := x^4 + 8*x^3 + 22*x^2 + 25*x + 10;
f := Evaluate(g, x^2);
E := HyperellipticCurve(g);
JE := EllipticCurve(E);
C := HyperellipticCurve(f);
JC := Jacobian(C);

assert #MordellWeilGroup(JE) eq 6;
assert [-3/2, 1/4] in E;
assert RankBound(JC) eq 0;