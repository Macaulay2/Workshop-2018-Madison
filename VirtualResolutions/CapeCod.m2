needsPackage "SplendidComplexes"
needsPackage "FourierMotzkin"



--  CAVEAT:  Does not guarantee that point is actually in regularity.
--  N = starting degree, which subsumes the pi^* O(m) for m>>0.
regCheck = (J,N) ->(
    X := variety ring J;
    d := hilbertPolynomial(X,J);
    nefX := transpose nefGenerators X;
    c := numcols nefX;
    testDeg := N;
    while hilbertFunction(testDeg,J) != d do(
	testDeg = testDeg + entries (nefX_(random(0,c-1))));
    testDeg
    );

--  input:  an ideal and a module
--  output: depth of the ideal on the module.
--  probably not most efficient algorithm.
hackyDepth = method();
hackyDepth (Ideal,Module) := (P,M) ->(
     K := (koszul gens P)**M;
     i := 0;
     while HH_(length K - i)(K) == 0 do i = i+1;
     i
     	  )
      
--  input:  an ideal and a complex
--  output: depth of the ideal on the module.
--  probably not most efficient algorithm.
hackyDepth (Ideal,ChainComplex) := (P,r) ->(
     K := (koszul gens P)**r;
     i := 0;
     while HH_(length K - i)(K) == 0 do i = i+1;
     i
     	  )



trimReg = J->(
    r := regCheck(J);
    ideal apply(numgens J,j-> if (degree J_j)_1 < r + 2 then J_j else 0)
    );

irrHomology = method();
--  Input: toric variety X and a chain complex F
-- Output:  true or false, depending on whether the complex of line bundles
--          associated to F is acyclic.
irrHomology (NormalToricVariety, ChainComplex) := (X,F) ->(
    irr := ideal X;
    for i from 1 to i + 1 do( 
	if saturate(ann prune HH_i F,irr) == 0 then break false);
    saturate(ann HH_0 F,irr) == saturate (ann HH_0 G,irr)
    );

splendidEquivalent = method();
--  Input:  two complexes F,G where we know F has irrelevant homology except in position 0
--          and we want to test if G represents the same sheaf.
--          so far we're only testing the HH_0 and we're assuming the module is cyclic
-- Output:  true or false
splendidEquivalent (NormalToricVariety, ChainComplex, ChainComplex) := (X,F,G) ->(
    irr := ideal X;
    saturate(ann HH_0 F,irr) == saturate (ann HH_0 G,irr)
    );

splendidEquivalent (NormalToricVariety, Ideal, Ideal) := (X,I,J) ->(
    irr := ideal X;
    saturate(I,irr) == saturate(J,irr)
    );

winnow = method();
--  Input: F a free chain complex on Cox(X).  L a functional on Pic(X). a in ZZ.
--  Output: the subcomplex of summands whose dot product with L is at most a.
--  CAVEAT:  No check that the output is quasisomorphic to the input.
winnow (NormalToricVariety, ChainComplex, List, ZZ) := (X,F,L,a) ->(
    --irr := ideal X;
    if #L != #degree (ring X)_0 then error "Functional has wrong length";
    lowDegreeSpots := for j to length F list(
	for i to rank F_j - 1 list(
	    if (sum apply(#L,k-> L_k*((degree F_j_i)_k))) <= a then i else continue
	    ));
    chainComplex apply(length F, i ->(
	     submatrix(F.dd_(i+1),lowDegreeSpots_i,lowDegreeSpots_(i+1))))
     );

winnow (NormalToricVariety, ChainComplex, RingElement, ZZ) := (X,F,f,a) ->(
    d := degree f;
    (A,B) := fourierMotzkin transpose matrix degrees ring X;
    C := first entries (matrix{degree f}*A);
    D := select(#C, i-> C#i === 0);
    if #D === 0 then error "No orthogonal functional found for f.";
    if #D > 1 then <<"Multiple orthogonal functionals found!!!!?!??!"<< endl;
    winnow(X,F,-entries (A_(D#0)),a)
    );



--  Input: two degrees
--  Output:  true if d <= e in the termwise partial order
termwiseLeq = (d,e) -> (
    if #d != #e then error "degrees have difference lengths";
    OUT = true;
    scan(#d,i-> if d_i > e_i then OUT = false);
    OUT
    )

--  Input: F a free chain complex on Cox(X).  alpha a degree in Pic(X)
--  Output: the subcomplex of summands generated in degree <= alpha.
--  Caveat:  only really meaningful for a product of projective spaces
--  CAVEAT:  No check that the output is quasisomorphic to the input.
winnow (NormalToricVariety, ChainComplex, List) := (X,F,alpha) ->(
    if #alpha != #degree (ring X)_0 then error "degree has wrong length";
    lowDegreeSpots := for j to length F list(
	for i to rank F_j - 1 list(
	    if termwiseLeq(degree F_j_i , alpha) then i else continue
	    ));
    chainComplex apply(length F, i ->(
	     submatrix(F.dd_(i+1),lowDegreeSpots_i,lowDegreeSpots_(i+1))))
     );
 
 
--  Same as above code, but Beilinson window is taken into account
--  so that alpha itself is in the regularity.
--  Primarily used for Christine's Eau Claire presentation.
winnowProducts = method();
winnowProducts (NormalToricVariety, ChainComplex, List) := (X,F,beta) ->(
    n := sum degrees ring F;
    m := n - apply(#n, i -> 1);
    alpha := beta + m;
    if #alpha != #degree (ring X)_0 then error "degree has wrong length";
    lowDegreeSpots := for j to length F list(
	for i to rank F_j - 1 list(
	    if termwiseLeq(degree F_j_i , alpha) then i else continue
	    ));
    chainComplex apply(length F, i ->(
	     submatrix(F.dd_(i+1),lowDegreeSpots_i,lowDegreeSpots_(i+1))))
     );

rank (ChainComplex) := F ->(
    sum apply(toList(min F .. max F), i -> rank F_i)
    );

--dotProduct of two lists:
dotProduct = (L,L') ->(sum apply(length L,i->( L#i*L'#i )));


--
--

--Input: ideal J, regularity bound d, alpha = vector for effective cone functional
--shavedIdeal = (J,d,alpha) ->(
--     ideal( for j to numgens J - 1 list(
--	if dotProduct(degree (J_j),alpha) <= d then J_j else continue
--	))
--    );


--  Input: two ideals, P and J
--  Output:  the depth(P,S^1/J).
--  You could move this higher in the file if you like.
koszulDepth = (P,J)->(
    KP := (koszul gens P)**(S^1/J);
    L := select(4,i-> HH_i KP != 0);
    numgens P - max L
    );

end;
--------
--------

restart
load "CapeCod.m2"
rho = {{1,0},{1,1},{0,1},{-1,0},{0,-1}} 
    -- Not a product of projective spaces
    -- Our winnow theorem fails below! 
sigma = apply(#rho,i-> {i,(i+1)%(#rho)})
X = normalToricVariety(rho,sigma)
S = ring X
irr = ideal X
netList decompose irr
netList degrees ring X
variety ring X
I = intersect apply(2,i-> ideal(random({1,2,1},S),random({1,2,1},S)));
I = intersect(I,ideal(random({2,0,2},S),random({0,1,0},S)));
J = saturate(I,irr);
hilbertPolynomial(X,J)
codim J
F = res J
B = betti' res J
res J
E1 = prune Ext^1(S^1/irr^[1],S^1/J);
L1 = associatedPrimes ann E1;
netList L1
E2 = prune Ext^2(S^1/irr^[1],S^1/J);
L2 = associatedPrimes ann E2;
netList L2
E3 = prune Ext^3(S^1/irr^[1],S^1/J);
L3 = associatedPrimes ann E3;
netList L3
--irr components: 02, 14, 24, 03, 13

--Make splendid in two steps:
K = winnow(X,res J,x_0,4) --Multiple orthogonal functionals found!
betti' K 
saturate(image K.dd_1,irr) == J
--prune HH K --K is acyclic
E'1 = prune Ext^1(S^1/irr^[1],S^1/image(K.dd_1));
L'1 = associatedPrimes ann E'1;
netList L'1
E'2 = prune Ext^2(S^1/irr^[1],S^1/image(K.dd_1));
L'2 = associatedPrimes ann E'2;
netList L'2
E'3 = prune Ext^3(S^1/irr^[1],S^1/image(K.dd_1));
L'3 = associatedPrimes ann E'3;
netList L'3



K' = winnow(X,K,x_1,4) --Multiple orthogonal functionals found!
betti' K' --SPLENDID!
saturate(image K'.dd_1,irr) == J
M = prune (HH_1 K') --free module?! BAD!!! We do not have the qis we want!

--Another way:
G = winnow(X,res J,x_1,2) --Multiple orthogonal functionals found!
betti' G
saturate(image G.dd_1,irr) == J --true
--prune HH G --G acyclic

G' = winnow(X,G,x_0,7) --Multiple orthogonal functionals found!
betti' G' --SPLENDID!
saturate(image G'.dd_1,irr) == J
ann (prune HH_1 G') --free module?! BAD!!! We do not have the qis we want!

--Interesting, here we chop off the tail! 
G' = winnow(X,G,x_0,6) --Multiple orthogonal functionals found!
betti' G' --Too short!
saturate(image G'.dd_1,irr) == J --true
HH_1 G' == 0 --false

G = winnow(X,res J,{1,0,1},4)
betti' G
saturate(image G.dd_1,irr) == J
prune HH_2 G 



--  the zero below is the minimal a+c in the regularity
matrix table(5,5,(i,j) -> hilbertFunction({j,5,4-i},J))
--  regularity choices include (0,5,3), (1,5,2) or (2,5,1) or (3,5,0)
--  Let D := (0,0,3).
--  Which degrees could yield an R^0? (after twisting by D and the cushion)?
--

needsPackage "FourierMotzkin"
M = transpose matrix degrees ring X
(A,B) = fourierMotzkin M
(degrees module OO(X_0))

K = shavedIdeal(J,4);
betti' res K
saturate(K,irr) == J

matrix table(25,25,(i,j) -> hilbertFunction({j,24-i,5},K))
hilbertFunction({4,5,0},K)
K' = shavedIdeal'(K,4);
betti' res K'
saturate(K',irr) == J

whichHaveNoR0 = B -> new MultigradedBettiTally from for k in keys B list (
	if k#2#0+k#2#2 > 4 then (k,B#k))

    
(B - whichHaveNoR0 B)
shavedIdeal = (J,d) ->(
     ideal( for j to numgens J - 1 list(
	if (degree (J_j))#0+(degree (J_j))#2 <= d then J_j else continue
	))
    )



------------
-- Double blowup
------------
restart
load "CapeCod.m2"
rho = {{1,0},{2,1},{1,1},{0,1},{-1,0},{0,-1}}
sigma = apply(#rho,i-> {i,(i+1)%(#rho)})
X = normalToricVariety(rho,sigma)
S = ring X
irr = ideal X
decompose irr
netList degrees ring X
I = intersect apply(2,i-> ideal(random({1,2,1,1},S),random({1,2,1,1},S)));
I = intersect(I,ideal(random({2,0,2,1},S),random({0,1,0,0},S)));
J = saturate(I,irr);
hilbertPolynomial(X,J)
codim J
B = betti' res J

G = winnow(X,res J,x_1,2) 
betti' G
saturate(image G.dd_1,irr) == J --true
prune HH G --acyclic
--WOW!!!

G' = winnow(X,G,x_0,4) 
betti' G'
saturate(image G'.dd_1,irr) == J --true
prune HH_1 G' --free module - BAD!!

H = winnow(X,res J,x_0,4) 
betti' H
saturate(image H.dd_1,irr) == J --true
prune HH H --acyclic

------------------------
--PP^2 x PP^2
------------------------
restart
load "CapeCod.m2"
--needsPackage "TateOnProducts"
needsPackage "SplendidComplexes"
--needsPackage "NormalToricVarieties"
X = projectiveSpace(2)**projectiveSpace(2)
S = ring X
irr = ideal X
I = ideal(random({2,1},S), random({1,1},S),random({1,1},S));
J = saturate(I,irr);
r = res J;
betti' r
codim J

E1 = prune Ext^1(S^1/irr^[1],S^1/J);
L1 = associatedPrimes ann E1;
netList L1
E2 = prune Ext^2(S^1/irr^[1],S^1/J);
L2 = associatedPrimes ann E2;
netList L2
E3 = prune Ext^3(S^1/irr^[1],S^1/J);
L3 = associatedPrimes ann E3;
netList L3
E4 = prune Ext^4(S^1/irr^[1],S^1/J);
L4 = associatedPrimes ann E4;
netList L4
E5 = prune Ext^5(S^1/irr^[1],S^1/J);
L5 = associatedPrimes ann E5;
netList L5


hilbertPolynomial(X,J)
matrix table(15,15,(i,j) -> hilbertFunction({j,14-i},J)) 
--  (1,1) and (2,0) in regularity so winnow by (3,3)??

q = winnow(X,r,{3,3})
betti' q
-- {3,3} unique appears as unique minimum element in last column.
prune HH q --acyclic
K = ideal flatten entries q.dd_1;
matrix table(15,15,(i,j) -> hilbertFunction({j,14-i},K)) 
-- (1,1) now the unique generator of the regularity

Eq0 = prune Ext^0(S^1/irr^[1],S^1/K);
Lq0 = associatedPrimes ann Eq0;
netList Lq0
Eq1 = prune Ext^1(S^1/irr^[1],S^1/K);
Lq1 = associatedPrimes ann Eq1;
netList Lq1
Eq2 = prune Ext^2(S^1/irr^[1],S^1/K);
Lq2 = associatedPrimes ann Eq2;
netList Lq2
Eq3 = prune Ext^3(S^1/irr^[1],S^1/K);
Lq3 = associatedPrimes ann Eq3;
netList Lq3
Eq4 = prune Ext^4(S^1/irr^[1],S^1/K);
Lq4 = associatedPrimes ann Eq4;
netList Lq4
Eq5 = prune Ext^5(S^1/irr^[1],S^1/K);
Lq5 = associatedPrimes ann Eq5;
netList Lq5

netList L1
netList Lq1
netList L2
netList Lq2
netList L3
netList Lq3
netList L4
netList Lq4
netList L5
netList Lq5

s = winnow(X,r,{4,2})
betti' s
prune HH s --acyclic
K' = ideal flatten entries s.dd_1;
-- {4,2} unique appears as unique minimum element in last column.
matrix table(15,15,(i,j) -> hilbertFunction({j,14-i},K')) 
-- (2,0) now the unique generator of the regularity

Es1 = prune Ext^1(S^1/irr^[1],S^1/K');
Ls1 = associatedPrimes ann Es1;
netList Ls1
Es2 = prune Ext^2(S^1/irr^[1],S^1/K');
Ls2 = associatedPrimes ann Es2;
netList Ls2
Es3 = prune Ext^3(S^1/irr^[1],S^1/K');
Ls3 = associatedPrimes ann Es3;
netList Ls3
Es4 = prune Ext^4(S^1/irr^[1],S^1/K');
Ls4 = associatedPrimes ann Es4;
netList Ls4
Es5 = prune Ext^5(S^1/irr^[1],S^1/K');
Ls5 = associatedPrimes ann Es5;
netList Ls5

netList L1
netList Ls1
netList L2
netList Ls2
netList L3
netList Ls3
netList L4
netList Ls4
netList L5
netList Ls5


---
---Another example with regularity having 3 generators
--
I = intersect apply(7, i->(
	ideal(random({1,0},S),random({1,0},S),random({0,1},S),random({0,1},S))
	    ));
J = saturate(I,irr);
r = res J;
betti' r

E1 = prune Ext^1(S^1/irr^[1],S^1/J);
L1 = associatedPrimes ann E1;
netList L1
E2 = prune Ext^2(S^1/irr^[1],S^1/J);
L2 = associatedPrimes ann E2;
netList L2
E3 = prune Ext^3(S^1/irr^[1],S^1/J);
L3 = associatedPrimes ann E3;
netList L3
E4 = prune Ext^4(S^1/irr^[1],S^1/J);
L4 = associatedPrimes ann E4;
netList L4
E5 = prune Ext^5(S^1/irr^[1],S^1/J);
L5 = associatedPrimes ann E5;
netList L5

hilbertPolynomial(X,J)
matrix table(15,15,(i,j) -> hilbertFunction({j,14-i},J)) 
--reg is (3,0),(1,1), and (0,3)

q1 = winnow(X,r,{5,2})
q2 = winnow(X,r,{3,3})
q3 = winnow(X,r,{2,5})
betti' q1
betti' q2
betti' q3
--  in each case, the winnowing degree appears as the unique maximum element
--  in the last column.  the nontrivial fact is that it actually shows up!
K1 = ideal flatten entries q1.dd_1;
K2 = ideal flatten entries q2.dd_1;
K3 = ideal flatten entries q3.dd_1;
prune HH q1   -- has HH_1
prune HH q2   -- has HH_1
prune HH q3   -- has HH_1

--Not really the Ext groups we want to compute here:
Eq11 = prune Ext^1(S^1/irr^[1],S^1/K1);
Lq11 = associatedPrimes ann Eq11;
Eq12 = prune Ext^2(S^1/irr^[1],S^1/K1);
Lq12 = associatedPrimes ann Eq12;
Eq13 = prune Ext^3(S^1/irr^[1],S^1/K1);
Lq13 = associatedPrimes ann Eq13;
Eq14 = prune Ext^4(S^1/irr^[1],S^1/K1);
Lq14 = associatedPrimes ann Eq14;
Eq15 = prune Ext^5(S^1/irr^[1],S^1/K1);
Lq15 = associatedPrimes ann Eq15;

Eq21 = prune Ext^1(S^1/irr^[1],S^1/K2);
Lq21 = associatedPrimes ann Eq21;
Eq22 = prune Ext^2(S^1/irr^[1],S^1/K2);
Lq22 = associatedPrimes ann Eq22;
Eq23 = prune Ext^3(S^1/irr^[1],S^1/K2);
Lq23 = associatedPrimes ann Eq23;
Eq24 = prune Ext^4(S^1/irr^[1],S^1/K2);
Lq24 = associatedPrimes ann Eq24;
Eq25 = prune Ext^5(S^1/irr^[1],S^1/K2);
Lq25 = associatedPrimes ann Eq25;

Eq31 = prune Ext^1(S^1/irr^[1],S^1/K3);
Lq31 = associatedPrimes ann Eq31;
Eq32 = prune Ext^2(S^1/irr^[1],S^1/K3);
Lq32 = associatedPrimes ann Eq32;
Eq33 = prune Ext^3(S^1/irr^[1],S^1/K3);
Lq33 = associatedPrimes ann Eq33;
Eq34 = prune Ext^4(S^1/irr^[1],S^1/K3);
Lq34 = associatedPrimes ann Eq34;
Eq35 = prune Ext^5(S^1/irr^[1],S^1/K3);
Lq35 = associatedPrimes ann Eq35;


netList L1
netList Lq11
netList Lq21
netList Lq31
netList L2
netList Lq12
netList Lq22
netList Lq32
netList L3
netList Lq13
netList Lq23
netList Lq33
netList L4
netList Lq14
netList Lq24
netList Lq34
netList L5
netList Lq15
netList Lq25
netList Lq35


--  When we choose a corner of regularity, that corresponds to an obstruction
--  to H^i_B vanishing in an appropriate degree, and that provides
--  an obstruction to F_i being generated in certain degrees.
--  For an ideal of points, the only possible obstruction is that H^top_B F_{dim X}
--  provides the obstruction in exactly the degree we expect, 
--  so this might explain the appearance of that degree in these examples.
hilbertFunction (List,ChainComplex,ZZ) := (L,r,d) -> (
    sum apply(d, i-> (-1)^i*hilbertFunction(L,HH_i r))
    )

matrix table(4,4,(i,j) -> hilbertFunction({j,3-i},q1,2)) 
hilbertFunction({4,0},q2,2)
--  so {3,0} no longer in regularity of q2 and neither is {0,3}.


--  Crazy conjecture 1 for products of projective spaces:
--  If we start with a cyclic module and winnow w/r/t to a corner of the regularity,
--  then the regularity of the new complex r is generated entirely in that degree,
--  and the resulting complex is splendid.
--  Conjecture 2:  Does winnowing at a corner product a splendid
--  complex for a cyclic module?  (We need the cyclic condition because winnowing 
--  doesn't play well with direct sums.)


------------
--PP^1 x PP^1 x PP^2
-----------

restart
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(2)
X = normalToricVariety(rays X,max X)
S = ring X
irr = ideal X

I = intersect apply(3,i->ideal(random({2,0,0},S),random({0,2,0},S),random({0,0,1},S),random({0,0,1},S)));
J = saturate(I,irr);
hilbertPolynomial(X,J)
r = res J
needsPackage "SplendidComplexes"
betti' r

--  (1,1,1) in the regularity; so is (1,5,0) and (2,3,0)
matrix table(15,15,(i,j) -> hilbertFunction({2,j,14-i},J)) 

--so we would winnow by (1,1,1) w/ cushion (1,1,2), and thus
--drop anything that isn't \leq (2,2,3).  this kills of column 5 entirely.
 q = winnow(X,r,{2,2,3})
 betti' q
saturate(ideal flatten entries q.dd_1,irr) == J
betti' r - betti' q


-- winnowing from (1,5,0) w cushion (1,1,2):
betti' winnow(X,r,{2,6,2})

E = apply({5,6},i-> Ext^i(S^1/irr^[5],S^1/J));
saturate(ann E_0,B_1)
saturate(ann E_1,B_1)

--
I = intersect apply(6,i->ideal(random({1,0,0},S),random({0,1,0},S),random({0,0,1},S),random({0,0,1},S)));
J = saturate(I,irr);
hilbertPolynomial(X,J)
r = res J
-- (1,2,0), (1,0,1), (0,0,2) all in the regularity. don't forget cushion (1,1,2);
r
#unique flatten apply(length r + 1, i-> apply(rank r_i, j-> degree r_i_j))
betti' r
q1 = winnow(X,r,{2,3,2})
#unique flatten apply(length q1 + 1, i-> apply(rank q1_i, j-> degree q1_i_j))
betti' q1
q2 = winnow(X,r,{2,1,3})
#unique flatten apply(length q2 + 1, i-> apply(rank q2_i, j-> degree q2_i_j))
betti' q2
q3 = winnow(X,r,{1,1,4})
#unique flatten apply(length q3 + 1, i-> apply(rank q3_i, j-> degree q3_i_j))
betti' q3

matrix table(15,15,(i,j) -> hilbertFunction({1,j,14-i},J)) 
hilbertFunction({1,2,0},J)

--
--
--Let's try a curve on PP^1 x PP^2
--
--
restart
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
X = normalToricVariety(rays X,max X)
S = ring X
irr = ideal X

--Let's try a curve.
I = intersect apply(2,i->ideal(random({1,1},S),random({1,1},S))
    );
J = saturate(I,irr);
dim X - codim J

r = res J;
betti' r
HP = hilbertPolynomial(X,J)
matrix table(10,10,(i,j) -> hilbertFunction({j,9-i},J) - sub(HP, {(ring HP)_0 => j, (ring HP)_1 => 9-i}))
--(1,2) and (3,1) are in regularity?
--(2,1) is in the socle of H^1_{irr} and seems to create the obstacle
--to having a shorter resolution.


q1 = winnow(X,r,{2,4})
K1 = ideal flatten entries q1.dd_1;
hilbertPolynomial(X,K1) == hilbertPolynomial(X,J)
betti' q1
matrix table(10,10,(i,j) -> hilbertFunction({j,9-i},K1) - sub(HP, {(ring HP)_0 => j, (ring HP)_1 => 9-i}))


OC = sheaf (S^1/J);
matrix table(10,10,(i,j) -> hilbertFunction({j,9-i},J) - sub(HP, {(ring HP)_0 => j, (ring HP)_1 => 9-i}))

viewHelp normalToricVariety
q2 = winnow(X,r,{4,3})
K2 = ideal flatten entries q2.dd_1;
hilbertPolynomial(X,K2) == hilbertPolynomial(X,J)
betti' q2

--something changes

--  The {2,2,4} was arrived at by trial and error.
--  I wasn't able to compute/estimate the regularity directly.
q1 = winnow(X,r,{2,2,4})
K1 = ideal flatten entries q1.dd_1;
hilbertPolynomial(X,K1) == hilbertPolynomial(X,J)
betti' q1
E = Ext^4(S^1/irr^[3],S^1/J);





X = projectiveSpace(1)**projectiveSpace(2)
X = normalToricVariety(rays X,{{0,2,3},{0,2,4},{0,3,4},{1,2,3},{1,2,4},{1,3,4}})
isWellDefined X
S = ring X
irr = ideal X
I = intersect apply(2, i-> ideal(random({1,1},S), random({1,1},S)));
J = saturate(I,irr);
betti' res J
betti res J
Ihope = ideal for j to numgens J - 1 list(
    if (degree J_j)_0 <= 8 and (degree J_j)_1 <= 2 then J_j else continue);
betti res Ihope
hackyDepth(Q,S^1/Ihope)
hackyDepth(P,S^1/Ihope)
hackyDepth(P+Q,S^1/Ihope)
betti res Ihope
hackyDepth(Q,S^1/J)
hackyDepth(P,S^1/(J+Q))


tally apply(50,i->(
	reg = regCheck(J,{0,0,0});
	sum apply(#L,l-> reg#l*L#l
	)
    ))	    
(P,Q) = toSequence decompose irr 
hackyDepth(P,S^1/J)
hackyDepth(Q,S^1/(J+P))
codim J
res intersect(J,Q^3)
betti res J
netList sort keys betti res J
betti res Ihope
hackyDepth(P,S^1/Ihope)
hackyDepth(Q,S^1/(Ihope))
hackyDepth(Q,S^1/(Ihope+P))



degree F_1_3


G = winnow(X,F,x_3,4)
betti' G

H = winnow(X,G,x_4,4)
betti' H

B = betti' F
min apply(keys B, k -> k#2#0 + k#2#2 - k#0 + 1)
min apply(keys B, k -> k#2#1 - k#0 + 1)
B = betti' res ideal gens S
B = betti' res ideal(x_0*x_1,x_3)


splendidEquivalent(X,J,ann HH_0 H)

for j to numgens J - 1 list(
	if (degree (J_j))#0+(degree (J_j))#2 <= d then J_j else continue

--  PP1 x PP1
restart
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)
X = normalToricVariety(rays X,max X)
S = ring X
irr = ideal X
I = intersect apply(2,i->ideal(random({1,0},S),random({0,1},S)));
J = saturate(I,irr);
r = res J
betti' r
q = winnow(X,r,{2,1})
betti' q


--  PP1 x PP1 x PP1 x PP1
-- for Christine at Eau Claire
restart
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)**projectiveSpace(1)
X = normalToricVariety(rays X,max X)
S = ring X
irr = ideal X
I = intersect apply(5,i->(
	ideal(random({1,0,0,0},S),random({0,1,0,0},S),random({0,0,1,0},S),random({0,0,0,1},S)))
    );
J = saturate(I,irr);
r = res J
betti r
betti' r
hilbertFunction({2,1,0,0},J)
q = winnowProducts(X,r,{2,1,0,0})
saturate(image q.dd_1,irr) == J

(rank q / rank r)_RR
betti' q
(betti q, betti r, betti r - betti q)


hilbertFunction({1,1,1,0},J)
q = winnowProducts(X,r,{1,1,1,0})
saturate(image q.dd_1,irr) == J
(rank q / rank r)_RR

betti' q
(betti q, betti r, betti r - betti q)



--  PP2 x PP1
--  Hilbert--Burch resolutions
restart
load "CapeCod.m2"

X = projectiveSpace(2)**projectiveSpace(1)
X = normalToricVariety(rays X,max X)
(S,irr) = (ring X,ideal X)
P = ideal(S_0,S_1,S_2);

-- Example 1:  A curve that has a Hilbert-Burch resolution
I = ideal(random({2,2},S),random({3,1},S));
J = saturate(I,irr);
r = res J
betti' r
--  The commented out line "computes" that
--  the regularity of the generated is generaetd in degree (3,1)
--matrix reverse apply(10,i-> apply(10,j-> hilbertFunction({j,i},J)))
q = winnowProducts(X,r,{3,1})
betti' q

JQ = ideal gens image q.dd_1;
betti' res JQ == betti' q

HJ = matrix reverse apply(10,i-> apply(10,j-> hilbertFunction({j,i},J)))
HJQ = matrix reverse apply(10,i-> apply(10,j-> hilbertFunction({j,i},JQ)))
HJ - HJQ
-- so we H^0_irr in degree 8,1 or something.

--  I2 is a vertical fiber which will screw up the
-- depth condition from Prop 2.6.
I1 = ideal(random({2,2},S),random({3,1},S));
I2 = ideal(random({1,0},S),random({1,0},S));
J = saturate(intersect(I1,I2),irr);
r = res J
betti' r
HJ = matrix reverse apply(10,i-> apply(10,j-> hilbertFunction({j,i},J)))
-- so (3,2) is in the regularity.
q = winnowProducts(X,r,{3,2})
betti' q

JQ = ideal gens image q.dd_1;
betti' res JQ == betti' q
hilbPoly = (s,t) ->(8*s+6*t-11)
HJQ = matrix reverse apply(15,i-> apply(15,j-> hilbertFunction({j,i},JQ)))
HP = matrix reverse apply(15,i-> apply(15,j-> hilbPoly(j,i)))
HJ-HP
HJQ-HP
HJ - HJQ
--  I think JQ only adds H^0.

-- let's confirm that depth is too low.
koszulDepth(P,J)
--  Thus, condition (1) of Prop 2.6 is not satisfied,
--  so there is no Hilbert-Burch resolux3tion.
