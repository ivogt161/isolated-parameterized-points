R<eps,a,m> := PolynomialRing(Integers(), 3);


//m = Min(d2/d3,d1/d3) - 2
//a = |d2/d3 - d1/d3|
min := m + 2;// m is at least 0
max := m + a + 2; //a is at least 0
//the pair {min,max} equals the pair {d1/d3, d2/d3}
//min*max = d1*d2/d3^3
//min + max = d1/d3 + d2/d3

//bound = (sqrt{g} + 1)/d3 > max
bound := max + eps;

f := min*max*(bound - 1)^2 - min*max*(min*max - min - max + 1) - max*(bound-min)^2 - min*(bound-max)^2;

assert f eq eps^2*(a*m + a + m^2 + 2*m) + 2*eps*(m+1)*(a+m+2)^2 + (m+1)*a*(a+m+2)^2;