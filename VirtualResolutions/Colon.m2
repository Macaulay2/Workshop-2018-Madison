newPackage(
        "Colon",
        Version => "0.1", 
        Date => "",
        Authors => {{Name => "", 
                  Email => "", 
                  HomePage => ""}},
        Headline => "saturation and ideal and submodule colon/quotient routines",
        DebuggingMode => true
        )

export {
    "eliminationInfo",
    "saturateByElimination",
    "intersectionByElimination"
    }

-- quotient methods:
-- 1. syzygyies
-- 2. use eliination methods? I forget how?
-- 3. case: x is a variable, I is homogeneous
--    case: x is a polynomial
--    case: x is an ideal
----------------
-- saturation --
----------------

-- Bayer trick
-- eliminate(t,(I, tf-1))
--   a. use MGB
--   b. use gb
-- iterated quotient

eliminationInfo = method()
eliminationInfo Ring := (cacheValue symbol eliminationInfo)(R -> (
     n := numgens R;
     k := coefficientRing R;
     X := local X;
     M := monoid [X_0 .. X_n,MonomialOrder=>Eliminate 1,MonomialSize=>16];
     R1 := k M;
     fto := map(R1,R,drop(generators R1, 1));
     fback := map(R,R1,matrix{{0_R}}|vars R);
     (R1, fto, fback)
    ))

-- Computing (I : f^\infty) = saturate(I,f)
-- version #1: elimination
saturateByElimination = method()
saturateByElimination(Ideal, RingElement) := (I, f) -> (
     R := ring I;
     (R1,fto,fback) := eliminationInfo R;
     f1 := fto f;
     I1 := fto I;
     J := ideal(f1*R1_0-1) + I1;
     --g := groebnerBasis(J, Strategy=>"MGB");
     --g := gens gb J;
     g := groebnerBasis(J, Strategy=>"F4");
     p1 := selectInSubring(1, g);
     ideal fback p1
     )

intersectionByElimination = method()
intersectionByElimination(Ideal, Ideal) := (I,J) -> (
     R := ring I;
     (R1,fto,fback) := eliminationInfo R;
     I1 := R1_0 * fto I;
     J1 := (1-R1_0) * fto J;
     L := I1 + J1;
     --g := groebnerBasis(J, Strategy=>"MGB");
     --g := gens gb J;
     g := groebnerBasis(L, Strategy=>"F4");
     p1 := selectInSubring(1, g);
     ideal fback p1
    )

intersectionByElimination List := (L) -> fold(intersectionByElimination, L)

saturateByElimination(Ideal, Ideal) := (I, J) -> (
    L := for g in J_* list saturateByElimination(I, g);
    intersectionByElimination L
    )

beginDocumentation()

end--
doc ///
Key
  Colon
Headline
  saturation and ideal and submodule colon/quotient routines
Description
  Text
  Example
Caveat
SeeAlso
///

end--

doc ///
Key
Headline
Usage
Inputs
Outputs
Consequences
Description
  Text
  Example
  Code
  Pre
Caveat
SeeAlso
///

TEST ///
-- test code and assertions here
-- may have as many TEST sections as needed
///

end--

restart
needsPackage "Colon"

kk = ZZ/32003
R = kk(monoid[x_0, x_1, x_2, x_3, x_4, Degrees => {2:{1, 0}, 3:{0, 1}}, Heft => {1,1}])
B0 = ideal(x_0,x_1)
B1 = ideal(x_2,x_3,x_4)

I = ideal(x_0^2*x_2^2*x_3^2+44*x_0*x_1*x_2^2*x_3^2+2005*x_1^2*x_2^2*x_3^2+12870
     *x_0^2*x_2*x_3^3-725*x_0*x_1*x_2*x_3^3-15972*x_1^2*x_2*x_3^3-7768*x_0^2*x_2
     ^2*x_3*x_4-13037*x_0*x_1*x_2^2*x_3*x_4-14864*x_1^2*x_2^2*x_3*x_4+194*x_0^2*
     x_2*x_3^2*x_4-2631*x_0*x_1*x_2*x_3^2*x_4-2013*x_1^2*x_2*x_3^2*x_4-15080*x_0
     ^2*x_3^3*x_4-9498*x_0*x_1*x_3^3*x_4+5151*x_1^2*x_3^3*x_4-12401*x_0^2*x_2^2*
     x_4^2+4297*x_0*x_1*x_2^2*x_4^2-13818*x_1^2*x_2^2*x_4^2+7330*x_0^2*x_2*x_3*x
     _4^2-13947*x_0*x_1*x_2*x_3*x_4^2-12602*x_1^2*x_2*x_3*x_4^2-14401*x_0^2*x_3^
     2*x_4^2+8101*x_0*x_1*x_3^2*x_4^2-1534*x_1^2*x_3^2*x_4^2+8981*x_0^2*x_2*x_4^
     3-11590*x_0*x_1*x_2*x_4^3+1584*x_1^2*x_2*x_4^3-13638*x_0^2*x_3*x_4^3-5075*x
     _0*x_1*x_3*x_4^3-14991*x_1^2*x_3*x_4^3,x_0^7*x_2-6571*x_0^6*x_1*x_2+13908*x
     _0^5*x_1^2*x_2+11851*x_0^4*x_1^3*x_2+14671*x_0^3*x_1^4*x_2-14158*x_0^2*x_1^
     5*x_2-15190*x_0*x_1^6*x_2+6020*x_1^7*x_2+5432*x_0^7*x_3-8660*x_0^6*x_1*x_3-
     3681*x_0^5*x_1^2*x_3+11630*x_0^4*x_1^3*x_3-4218*x_0^3*x_1^4*x_3+6881*x_0^2*
     x_1^5*x_3-6685*x_0*x_1^6*x_3+12813*x_1^7*x_3-11966*x_0^7*x_4+7648*x_0^6*x_1
     *x_4-10513*x_0^5*x_1^2*x_4+3537*x_0^4*x_1^3*x_4+2286*x_0^3*x_1^4*x_4+733*x_
     0^2*x_1^5*x_4+11541*x_0*x_1^6*x_4+660*x_1^7*x_4)

ans1 = elapsedTime saturateByElimination(saturateByElimination(I, B0), B1);
ans2 = elapsedTime saturateByElimination(saturateByElimination(I, B1), B0);

elapsedTime J1 = saturateByElimination(I, x_0);
elapsedTime J2 = saturateByElimination(I, x_1);
elapsedTime J = intersectionByElimination(J1,J2);
elapsedTime J' = intersectionByElimination(J2,J1);
elapsedTime J'' = intersect(J1,J2);
elapsedTime J''' = intersect(J2,J1);
J == J'
J == J''

time gens gb I;
J2 = elapsedTime saturateByElimination(I, x_0);
assert isHomogeneous J2
J2' = elapsedTime saturateByElimination(I, x_1);

J2 = elapsedTime saturateByElimination(I, ideal(x_0,x_1));
J2' = elapsedTime saturateByElimination(J2, ideal(x_2,x_3,x_4));

J1 = elapsedTime saturate(I, x_0);
J1' = elapsedTime saturate(I, x_1);
J1 == J2
J1' == J2'

betti J2
betti J1

restart
needsPackage "Colon"
load "badsaturations.m2"

J = paramRatCurve({2,2},{3,3},{4,2});
elapsedTime genSat(J,2) -- 200 sec
elapsedTime genSat2(J,2) -- 50 sec
elapsedTime genSat3(J,2) -- 35 sec

J = paramRatCurve({2,2},{3,3},{5,2});
elapsedTime genSat(J,2) -- 691 sec
elapsedTime genSat2(J,2) -- 104 sec
elapsedTime genSat3(J,2) -- 71 sec

J = paramRatCurve({2,2},{3,4},{4,3});
elapsedTime genSat(J,2) --  sec
elapsedTime genSat2(J,2) --  sec
elapsedTime genSat3(J,2) -- 75 sec
