PolyRing := PolynomialRing(Rationals());
//Compare to LMFDB code on https://www.lmfdb.org/EllipticCurve/2.0.3.1/283.1/a/1
K<a> := NumberField(PolyRing![1, -1, 1]);
abar := Trace(a) - a;
d := -3;
junk, isqrt3 := IsSquare(K!d);
assert junk eq true;

//Compare to LMFDB code on https://www.lmfdb.org/EllipticCurve/2.0.3.1/283.1/a/1
Em := EllipticCurve([K![1,0],K![0,1],K![1,1],K![-1,0],K![0,-1]]); //minimal model
Pm := Em![0,-a,1]; //generator for MW group according to 
E, phi := SimplifiedModel(Em);

A := K!(-3/16);
B := -1/32 - isqrt3/9;

assert aInvariants(E) eq [0,0,0,A,B];

Abar := Trace(A) - A;
Bbar := Trace(B) - B;

R<w0,w1,w2,w3,w4> := PolynomialRing(Rationals(), 5);
RK := ChangeRing(R, K);

//claim 1 and 3 given by properties of restriction of scalars, claim 2 verified below

//ideal defining surface in P^4 birational to restriction of scalars.
Sideal := ideal<R  |
            1/2*w0^3 + 3*w0^2*w3 + w0*w1^2 - 3*w0*w2^2 - 16*w3^3 + 144*w3*w4^2, 
            8/9*w0^3 + 3/2*w0^2*w4 + w0*w1*w2 - 24*w3^2*w4 + 24*w4^3>;

SidealK := ideal<RK | [RK!g : g in Generators(Sideal)]>;

//defining map from base change of S to E x Ebar
X := 4*RK!w3 + 4*isqrt3*RK!w4;
Y := RK!w1 + isqrt3*RK!w2;
Z := 4*RK!w0;
Eeqn := Y^2*Z - (X^3 + A*X*Z^2 + B*Z^3);
assert Eeqn in SidealK; //image lands in E x P^2

Xbar := 4*RK!w3 - 4*isqrt3*RK!w4;
Ybar := RK!w1 - isqrt3*RK!w2;
Zbar := 4*RK!w0;
Ebareqn := Ybar^2*Zbar - (Xbar^3 + Abar*Xbar*Zbar^2 + Bbar*Zbar^3);
assert Ebareqn in SidealK; //and image lands in P^2 x Ebar, so map lands

P := [phi(Pm)[1], phi(Pm)[2], phi(Pm)[3]]; //generator of MW group on E
assert P eq [1/4 + 1/6*(isqrt3), 1/4 - 1/4*isqrt3, 1]; //P as given in paper
Pbar :=     [1/4 - 1/6*(isqrt3), 1/4 + 1/4*isqrt3, 1]; //Pbar on Ebar
assert P[2]^2*P[3] - (P[1]^3 + A*P[1]*P[3]^2 + B*P[3]^3) eq 0; //checking that P lies on E
assert Pbar[2]^2*Pbar[3] - (Pbar[1]^3 + Abar*Pbar[1]*Pbar[3]^2 + Bbar*Pbar[3]^3) eq 0; //and that Pbar lands on Ebar

PMat := Matrix([
    [X,Y,Z],P
]);
Pideal := ideal<RK | Minors(PMat, 2)>;
PbarMat := Matrix([
    [Xbar,Ybar,Zbar],Pbar
]);
Pbarideal := ideal<RK | Minors(PbarMat, 2)>;

//check that map is generically 1-to-1.
preimageideal := Pideal + Pbarideal + SidealK;
preimage := Proj(quo<RK | preimageideal>);
assert Dimension(preimage) eq 0;
assert Degree(preimage) eq 1;

/**********************************/
//Now checking claims about curve
//ideal defining curve
Cideal := ideal<R | w4 - w3, 18*w1*w2 + 27*w4*w0 + 16*w0^2> + Sideal;
            //    2*w1^2*w0 + 256*w4^3 + 6*w4*w0^2 - 6*w2^2*w0 + w0^3>;
//curve lies on surfaces
assert Sideal subset Cideal;

C := Curve(Proj(quo<R | Cideal>));
//C is smooth of genus 4
assert IsNonsingular(C);
assert Genus(C) eq 4;

//Z pullsback to a P^1-isolated degree 4 point on C
pullback := Cideal + ideal<R | [R!g : g in GroebnerBasis(Pideal*Pbarideal)]>;

x := Proj(quo<R | pullback>);
assert Dimension(x) eq 0;
assert Degree(x) eq 4;
assert #PrimaryComponents(x) eq 1; //is irreducible
assert IsReduced(x);//is reduced

xdiv := Divisor(C, Scheme(C, pullback));
assert Dimension(RiemannRochSpace(xdiv)) eq 1; //x is P^1-isolated.
