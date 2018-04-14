--
--
-- Curve from Example 1.4
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
hilbertPolynomial(X,J')
r' = res J'
betti' r'
--  This is the resolution in line (1.4.1)
hilbertPolynomial(X,J')
--curve of bidegree (2,8)
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J'))
--(2,1) and (1,5) are both in regularity.

q1 = winnowProducts(X,r',{2,1})
assert(saturate(image q1.dd_1,irr) == J')
betti' q1
--  This is the virtual resolution in (1.4.2)
phi = q1.dd_2
--  Matrix from (1.4.3)


q2 = winnowProducts(X,r',{1,5})
assert(saturate(image q1.dd_1,irr) == J')
betti' q2
phi' = q2.dd_2




--
--
--  Example 2.2
--
--
--  We redefine the ideal of the curve from Example 1.4
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
OC = sheaf(X,S^1/J');
T00 = OO_X^1;
T01 = (sheaf kernel matrix{{x_2,x_3,x_4}})**OO_X(0,1);
T11 = cotangentSheaf(X);
T10 = OO_X(-1,0);
T02 = OO_X(0,-1);
T12 = OO_X(-1,-1);
T = {T00,T01,T11,T10,T02,T12};
-- this doesn't terminate.  i computed it another way.
apply(T,t->HH^0(X,OC(2,2)**t))

--
--
--  Example 2.6
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(2)**projectiveSpace(2)
S = ring X;
irr = ideal X;
I = intersect(ideal(x_0,x_1),ideal(x_3,x_4))
betti' res I

--
-- 
-- Example 4.5 and Example 5.7
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(2);
S = ring X;
irr = ideal X;
I1 = intersect apply(6,i-> ideal(random({1,0,0},S),random({0,1,0},S), random({0,0,1},S),random({0,0,1},S)));
I = saturate(I1,irr);
r = res I

--Computing the regularity
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,0},I))
--  We see that (5,0,0) and (2,1,0) and (1,2,0) and (0,5,0) are all
-- minimal elements of the regularity
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,1},I))
--  We see that (1,0,1) and (0,1,1) are minimal elements of the regularity
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,2},I))
--  Finally, (0,0,2) is a minimal elements of the regularity


q0 = winnowProducts(X,r,{5,0,0})
q1 = winnowProducts(X,r,{2,1,0})
q2 = winnowProducts(X,r,{1,0,1})
q3 = winnowProducts(X,r,{0,0,2})
numTwists = r ->(
    #unique flatten apply(length r+1, i-> unique degrees r_i)
    )
assert(numTwists(q0) == 18)
assert(numTwists(q1) == 22)
assert(numTwists(q2) == 15)
assert(numTwists(q3) == 13)
assert(HH_1(q0) != 0)
assert(HH_1(q1) != 0)
assert(HH_1(q2) != 0)
assert(HH_1(q3) != 0)
assert(HH_2(q0) != 0)
assert(HH_2(q1) != 0)
assert(HH_2(q2) != 0)
assert(HH_2(q3) == 0)
unique degrees q0_1
unique degrees q1_1
unique degrees q2_1
unique degrees q3_1

B0 = ideal(x_0,x_1);
B1 = ideal(x_2,x_3);
J = intersect(I,B0^2,B1);
K = intersect(I,B0^3,B1^3);

res J
res K
numTwists(res J)
numTwists(res K)

betti' res K
betti' res J 
betti' q0
betti' q1
betti' q2
betti' q3


--
--
--  Example 5.9
--
--
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = smoothFanoToricVariety(2,3);
S = ring X
degrees S
B = ideal X;
--  We start by defining the ideal of 3 points
pointToIdealX = v->(  
    ideal(v_2*v_3*x_0 - v_0*x_2*x_3, v_4*x_1*x_2 - v_1*v_2*x_4)
    )
point1 = {1,1,1,1,1};
point2 = {2,1,3,1,5};
point3 = {7,1,11,1,13};
I1 = pointToIdealX(point1);
I2 = pointToIdealX(point2);
I3 = pointToIdealX(point3);
IZ = saturate(intersect(I1,I2,I3),B);
assert(hilbertPolynomial(X,IZ) == 3)
betti' res IZ
IZ
--  IZ is the saturated ideal of the 3 points

--  There's a blowdown map to P^2 obtained by blowing down
--  the toric divisors V(x_1) and V(x_3).
--  The corresponding map of rings is the map psi below.
A = QQ[t_0,t_1,t_2]
--  the image of the points in PP^2 are {1,1,1}, {2,3,5},{7,11,13}
psi = map(S,A,{x_0*x_1,x_1*x_2*x_3,x_3*x_4})
pointToIdealP2 = v->(  
    ideal(v_1*t_0-v_0*t_1, v_2*t_0-v_0*t_2)
    )
pointToIdealP2({1,1,1})
J = intersect(pointToIdealP2({1,1,1}),pointToIdealP2({2,3,5}),pointToIdealP2({7,11,13}));
--  J is the ideal of the image of the points
--  the pullback of the resolution of A/J is the desired
--  virtual resolution
K = psi J;
betti' res K

--
--
--  Remark 5.3
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = hirzebruchSurface(2)
S = ring X;
B = ideal X;
J = ideal(x_0^5*x_1^2 + x_2*x_3^2, x_0*x_3 + x_1*x_2^3);
I = saturate(J,B);
betti' res I;
B0 = ideal(x_0,x_2)
B1 = ideal(x_1,x_3)
res intersect(I,B0^3)
res intersect(I,B0^4)
res intersect(I,B0^5)
res intersect(I,B0^11)



--
--
--  Example 6.4
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
K = ideal(J'_0,J'_1);
betti' res K
assert(saturate(K,irr) == J')

--
--
--  Example 6.9
--
--
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(3)
S = ring X
irr = ideal X;
I = ideal((x_0^2)*(x_3^2)+x_1^2*x_2*x_5+x_0*x_1*x_4^2, x_0*(x_2*x_4)+x_1*(x_3*x_5)+x_1*x_3^2)
J = saturate(I,irr);
--  To get coordinates consistent with paper,
--  we can do this change of coordinates
--  A = QQ[x_(1,0),x_(1,1),x_(2,0),x_(2,1),x_(2,2),x_(2,3)]
--  phi = map(A,S,gens A)
--  phi(J)

--  Computing genus of a random fiber of map
L = J + ideal(random({1,0},S));
B2 = ideal(x_2,x_3,x_4,x_5);
assert(saturate(L,B2) == L)
hilbertPolynomial(X,L)
--  General fiber is a genus 1 curve

--  Checking that (1,1) is in regularity
hilbertPolynomial(X,J)
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))








decompose J
r = res J
betti' r
w = winnowProducts(X,r,{1,1})
betti' w
K = ann HH_0 w;
saturate(K,irr) == J


f = hilbertPolynomial(X,I)
sub(f, {(ring f)_0 => 1, (ring f)_1 => 2})
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))























-- Elliptic curve in P2 x P2
-- Moved out of paper
restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(2)**projectiveSpace(2);
S = ring X;
irr = ideal X;
IE = ideal(random({1,1},S),random({1,1},S),random({1,1},S));
hilbertPolynomial(X,IE)
J = saturate(IE,irr);
betti' res J
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))
r = res J
q = winnowProducts(X,r,{1,0})
betti' q





----
X = projectiveSpace(2)**projectiveSpace(2)
S = ring X
irr = ideal X
phi1 = random(S^{2:{-1,0}},S^{2:{-1,-1}})
psi1 = phi1 - transpose(phi1);
phi2 = random(S^{5:{0,0}},S^{5:{-1,-1}})
psi2 = phi2 - transpose(phi2);
psi = psi1 ++ psi2
J = pfaffians(4,psi2);
codim J
betti' res J
codim J
I = intersect(ideal(x_0,x_1),ideal(x_3,x_4));
J = saturate(I,irr);
betti' res J
P = hilbertPolynomial(X,ideal(0_S))
P11 = sub(P,{A_0 => A_0-1, A_1 => A_1-1})
P22 = sub(P,{A_0 => A_0-2, A_1 => A_1-2})
P33 = sub(P,{A_0 => A_0-3, A_1 => A_1-3})
P44 = sub(P,{A_0 => A_0-4, A_1 => A_1-4})
P55 = sub(P,{A_0 => A_0-5, A_1 => A_1-5})
P - 5*P22 + 5*P33 - P55
delta = minors(2, matrix{{x_0,x_1,x_2},{x_3,x_4,x_5}});
I = ideal(x_0^2,x_3^2)+delta;
betti' res I
codim I
A = ring P
sub(P,{A_0 => A_0+1})


I = saturate(J,irr);


restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"

X = projectiveSpace(1)**projectiveSpace(1)
S = ring X
irr = ideal X
I = intersect(ideal(x_0,x_2),ideal(x_1,x_3))
r = res I
Q = ideal(x_0,x_1)
J = intersect(I,Q)
r' = res J
K = intersect(J,minors(2,r'.dd_2))
res K
peek res K
peek r'

matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},I))




restart
needsPackage "SplendidComplexes"
load "CapeCod.m2"

X = projectiveSpace(1)**projectiveSpace(1)
S = ring X
irr = ideal X

I = intersect apply(5,i-> ideal(random({1,0},S),random({0,1},S)));
J = saturate(I,irr);
r = res J
betti' r
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))
--(2,1) is in regularity

q1 = winnowProducts(X,r,{2,1})
saturate(image q1.dd_1,irr) == J
--  confirming that we really got a splendid resolution
betti' q1
K = ideal image q1.dd_1;

B0 = ideal(x_0,x_1);
L = intersect(J,B0^4);
M = intersect(J,B0^9);
betti res M
hilbertFunction({0,0},Hom(K,S^1/K))
hilbertFunction({0,0},Hom(I,S^1/I))
hilbertFunction({0,0},Hom(L,S^1/L))
hilbertFunction({0,0},Hom(M,S^1/M))

--Deformations are the same regardless of the model. 
-- The curve is a smooth point on its
--  Hilbert scheme, which is a 28-dimensional Hilbert scheme.
--  And you can compute the deformation thoery via
--  any of these models.

--  By contrast if you work with the saturated model,
--  then the deformations are obstructed:
hilbertFunction({0,0},Hom(J,S^1/J))








--  New Curve
I = ideal(random({1,1},S),random({1,1},S));
J = saturate(I,irr);
r = res J
betti' r
--rational curve of bidegree (1,2)
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))
--(2,2) is in regularity

K = J+ideal random({2,2},S);
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},K))
betti' res saturate(K,irr)
K = ideal(random({1,0},S),random({0,2},S),random({0,6},S));
K = intersect apply(6,i-> ideal(random({1,0},S),random({0,1},S)));
K = saturate(K,irr);
betti' res K
q1 = winnowProducts(X,r,{2,2})
saturate(image q1.dd_1,irr) == J
--  confirming that we really got a splendid resolution
betti' q1
I = ideal image q1.dd_1;



Ext^2(I,I) == 0
deg Ext^1(J,J) == 0
deg Hom(J,S^1/pJ)
--HH_(>2) q = 0
decompose annihilator HH_1 q
r
q
(rank q / rank r)_RR
betti' q
(betti q, betti r, betti r - betti q)

--Another choice:
-- {1,1,1,0} is in reg(S/J):
hilbertFunction({1,1,1,0},J)
q' = winnowProducts(X,r,{1,1,1,0})
saturate(image q'.dd_1,irr) == J
--HH_(>2) q' = 0
decompose annihilator HH_1 q'
r
q --previous example
q' --current example
(rank q' / rank r)_RR
betti' q'




--Del Pezzo Exaxmple for Section 6



hilbertPolynomial(X,J)


r = res IZ
phi = submatrix(r.dd_2,{1,2,3},{2,3})
J = minors(2,phi);
betti' res J
saturate(J,B) == IZ
betti' res J
degrees S
rays X

-- not generic enough????
kernel
F = basis({1,1,1},S)
f = F_(0,0)+F_(0,3)
g = F_(0,4)+F_(0,7)
J = ideal(f,g);
I = saturate(J,B);
r = res I
betti' r
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,0},J))
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,1},J))
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,2},J))
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i,3},J))
w = winnowProducts(X,r,{1,2,1})
betti' w




---------------
--  (PP1)^6:
X' = projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)
S' = ring X'
irr' = ideal X';
-- 4 points on X':
I' = intersect apply(4,i->(
	ideal(random({1,0,0,0,0,0},S'),random({0,1,0,0,0,0},S'),random({0,0,1,0,0,0},S'),random({0,0,0,1,0,0},S'),random({0,0,0,0,1,0},S'),random({0,0,0,0,0,1},S')))
    );
J' = saturate(I',irr');
r' = res J'
betti r'
betti' r'
-- {1,1,0,0,0,0} is in reg(S/J):
hilbertFunction({1,1,0,0,0,0},J')
--w = winnowProducts(X',r',{1,1,0,0,0,0})
w
betti w
saturate(image w.dd_1,irr') == J'
--prune HH w
--decompose annihilator HH_1 w
r'
w
(rank w / rank r')_RR
betti' w

---------------------------
restart
--  Example 6.12 surface in P1 x P3
needsPackage "SplendidComplexes"
load "CapeCod.m2"

X = projectiveSpace(1)**projectiveSpace(3)
S = ring X
irr = ideal X;
-- Surface
--I = ideal(random({2,2},S),random({1,2},S));
I = ideal((x_0^2)*(x_3^2)+x_1^2*x_2*x_5+x_0*x_1*x_4^2, x_0*(x_2*x_4)+x_1*(x_3*x_5)+x_1*x_3^2)
--I = ideal(x_0*x_2*x_3+x_1*x_4*x_5,x_0^2*x_4^2)
J = saturate(I,irr);
A = QQ[x_(1,0),x_(1,1),x_(2,0),x_(2,1),x_(2,2),x_(2,3)]
phi = map(A,S,gens A)
tex phi(J)
isHomogeneous J
isPrime J
--random fiber of map
L = J + ideal(random({1,0},S));
B2 = ideal(x_2,x_3,x_4,x_5);
saturate(L,B2) == L
hilbertPolynomial(X,L)

decompose J
r = res J
betti' r
w = winnowProducts(X,r,{1,1})
betti' w
K = ann HH_0 w;
saturate(K,irr) == J


f = hilbertPolynomial(X,I)
sub(f, {(ring f)_0 => 1, (ring f)_1 => 2})
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))

regRegion = I ->(
    f = hilbertPolynomial(X,I);
    matrix table(11,11,(a,b) -> hilbertFunction({b,10-a},I) - sub(f, {(ring f)_0 => b, (ring f)_1 => 10-a}))
    )

I = intersect(ideal(random({2,2},S),random({1,2},S)),ideal(random({3,1},S),random({1,2},S)));
I = intersect(
   ideal((x_0^2)*(x_3^2)+x_1^2*x_2*x_5+x_0*x_1*x_4^2, 
       x_0*(x_2*x_4)+x_1*(x_3*x_5)+x_1*x_3^2),
   ideal(x_0^3*x_2+x_0*x_1^2*x_5+x_1^3*x_3,
       x_1^2*x_2^2+x_0*x_1*x_4*x_5)
   );
I = ideal(random({3,2},S),random({1,2},S));
J = saturate(I,irr);
regRegion J



--  Example 6.12 curve in P2 x P2
needsPackage "SplendidComplexes"
load "CapeCod.m2"

X = projectiveSpace(2)**projectiveSpace(2)
S = ring X
irr = ideal X;
-- Surface
--I = ideal(random({2,2},S),random({1,2},S));
I = ideal((x_0^2)*(x_3^2)+x_1^2*x_2*x_5+x_0*x_1*x_4^2, x_0*(x_2*x_4)+x_1*(x_3*x_5)+x_1*x_3^2)
--I = ideal(x_0*x_2*x_3+x_1*x_4*x_5,x_0^2*x_4^2)
J = saturate(I,irr);
A = QQ[x_(1,0),x_(1,1),x_(2,0),x_(2,1),x_(2,2),x_(2,3)]
phi = map(A,S,gens A)
tex phi(J)
isHomogeneous J
isPrime J
--random fiber of map
L = J + ideal(random({1,0},S));
B2 = ideal(x_2,x_3,x_4,x_5);
saturate(L,B2) == L
hilbertPolynomial(X,L)

decompose J
r = res J
betti' r
w = winnowProducts(X,r,{1,1})
betti' w
K = ann HH_0 w;
saturate(K,irr) == J


f = hilbertPolynomial(X,I)
sub(f, {(ring f)_0 => 1, (ring f)_1 => 2})
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))

regRegion = I ->(
    f = hilbertPolynomial(X,I);
    matrix table(11,11,(a,b) -> hilbertFunction({b,10-a},I) - sub(f, {(ring f)_0 => b, (ring f)_1 => 10-a}))
    )


M = random(S^2,S^{{-1,-1},{-1,-1},{0,-2}});
I = minors(2,M);
J = saturate(I,irr);
betti' res J
I = ideal(random({2,2},S),random({2,2},S));
J = saturate(I,irr);
regRegion(J)

-----
needsPackage "SplendidComplexes"
load "CapeCod.m2"

X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X;
-- Surface
I = intersect(ideal(x_2,x_3),ideal(x_0,x_4));
J = saturate(I,irr);
r = res J
betti' r
w = winnowProducts(X,r,{0,1})
betti' w
K = ann HH_0 w;
saturate(K,irr) == J

hilbertPolynomial(X,I)
matrix table(7,7,(i,j) -> hilbertFunction({j,6-i},J))
