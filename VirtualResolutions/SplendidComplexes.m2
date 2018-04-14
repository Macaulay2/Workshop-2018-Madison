-- -*- coding: utf-8 -*-
------------------------------------------------------------------------------
-- Copyright 2014  Gregory G. Smith
--
-- This program is free software: you can redistribute it and/or modify it
-- under the terms of the GNU General Public License as published by the Free
-- Software Foundation, either version 3 of the License, or (at your option)
-- any later version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
-- FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
-- more details.
--
-- You should have received a copy of the GNU General Public License along
-- with this program.  If not, see <http://www.gnu.org/licenses/>.
------------------------------------------------------------------------------

newPackage(
  "SplendidComplexes2",
  AuxiliaryFiles => false,
  Version => "0.2",
  Date => "30 June 2014",
  Authors => {{
      Name => "Gregory G. Smith", 
      Email => "ggsmith@mast.queensu.ca", 
      HomePage => "http://www.mast.queensu.ca/~ggsmith"}},
  Headline => "splendid complexes",
  PackageExports => {"NormalToricVarieties"},
  PackageImports => {},
  DebuggingMode => false
  )

export { 
  "MultigradedBettiTally",
  "betti'",
  "minimize",
  "pointsIdeal"
  }

------------------------------------------------------------------------------
-- CODE THAT BELONGS SOMEWHERE ELSE
------------------------------------------------------------------------------

NormalToricVariety ** NormalToricVariety := NormalToricVariety => (X,Y) -> (
  V1 := transpose matrix rays X;
  V2 := transpose matrix rays Y;
  V := entries transpose (V1 ++ V2);
  F1 := max X;
  F2 := max Y;
  n := #rays X;
  F2 = apply(F2, s -> apply(s, i -> i+n));
  F := flatten table(F1,F2, (s,t) -> s|t);
  W1 := fromWDivToCl X;
  W2 := fromWDivToCl Y;
  XY := normalToricVariety(V,F, WeilToClass => W1 ++ W2);
  return XY)


NormalToricVariety ^** ZZ := NormalToricVariety => (X,n) -> (
  if n <= 0 then error "expected a positive integer";
  if n == 1 then return X;
  X ** (X ^** (n-1)))

------------------------------------------------------------------------------
-- CODE
------------------------------------------------------------------------------
MultigradedBettiTally = new Type of VirtualTally
MultigradedBettiTally.synonym = "multigraded Betti tally" 
MultigradedBettiTally == MultigradedBettiTally := (B,C) -> B === C
MultigradedBettiTally ++ MultigradedBettiTally := (B,C) -> merge(B,C,plus)
MultigradedBettiTally ** MultigradedBettiTally := (B,C) -> (
  combine(B,C, (k,j) -> apply(j,k, plus), times, plus))
ZZ * MultigradedBettiTally := (n,B) -> applyValues(B, v -> n*v)
QQ * MultigradedBettiTally := (n,B) -> applyValues(B, v -> n*v)
pdim MultigradedBettiTally := B -> max apply(keys B, i -> i#0)
MultigradedBettiTally List := (B,l) -> applyKeys(B, (i,h,d) -> (i,h,d-l))
MultigradedBettiTally Array := (B,A) -> (
  if #A =!= 1 then error "expected array of length 1";
  n := A#0;
  applyKeys(B, (i,h,d) -> (i-n,h,d)))

net MultigradedBettiTally := B -> ( 
  H := new MutableHashTable;
  if keys B == {} then return 0;
  scan(sort keys B, key -> (
      (i,h,d) := key;
      s := toString(B#key) | ":" | toString(d);
      if H#?i then H#i = H#i | {s} else H#i = {s}));
  rows := max apply(values H, v -> #v);
  T := table(toList(0..rows-1), sort keys H, 
    (i,k) -> if i < #H#k then H#k#i else null);
  T = prepend(sort keys H,T);  
  netList(T, 
    Alignment => Left, 
    HorizontalSpace => 1,
    BaseRow => 1,
    Boxes => false))

poincare (NormalToricVariety, MultigradedBettiTally) := (X,B) -> (
  R := degreesRing ring X;
  if #B === 0 then return 0_R;
  sum(keys B, k -> (-1)^(k#0) * B#k * R_(k#2)))


-- local function for selecting and computing the appropriate heft
heftFunction0 := wt -> d -> sum(min(#wt,#d), i -> wt#i * d#i)
heftFunction := (wt1,wt2) -> (
  if wt1 =!= null then heftFunction0 wt1
  else if wt2 =!= null then heftFunction0 wt2
  else d -> 0)

-- our new method for displaying degrees
betti' = method(TypicalValue => MultigradedBettiTally, 
  Options => {Weights => null});
betti' MultigradedBettiTally := opts -> B -> (
  if opts.Weights === null then B 
  else ( 
    heftFn := heftFunction0 opts.Weights;
    applyKeys(B, (i,h,d) -> (i, heftFn d, d))))
betti' Matrix := opts -> f -> betti'(chainComplex f, opts)
betti' GroebnerBasis := opts -> G -> betti'(generators G, opts)
betti' Ideal := opts -> I -> betti'(generators I, opts)
betti' MonomialIdeal := opts -> I ->  betti'(ideal I, opts)
betti' Module := opts -> M -> betti'(presentation M, opts)
betti' GradedModule := opts -> C -> (
  complete C;
  heftFn := heftFunction(opts.Weights, heft C);
  new MultigradedBettiTally from flatten apply(
    select(pairs C, (i,F) -> class i === ZZ),
    (i,F) -> apply(pairs tally degrees F, (d,n) -> (i, heftFn d, d) => n)))



-- local functions for finding the extremal homological degrees of the
-- nonzero modules in a graded module
nonzeroMin = (cacheValue symbol nonzeroMin)(C -> (
    complete C;
    min for i from min C to max C list if C_i == 0 then continue else i))
nonzeroMax = (cacheValue symbol nonzeroMax)(C -> (
    complete C;
    max for i from min C to max C list if C_i == 0 then continue else i))

minimize = method();
minimize ChainComplex := ChainComplex => C -> (
  complete C;
  lower := nonzeroMin C;
  upper := nonzeroMax C;
  if not all(lower..upper, i -> isFreeModule C_i)
  then error "expected a chain complex of free modules";
  rows := new MutableHashTable; -- row indices in each differential to keep  
  D := new MutableHashTable;    -- differentials 
  E := new MutableHashTable;    -- free modules 
  for i from lower to upper do (
    rows#i = set(0.. rank C_i - 1);
    D#i = mutableMatrix C.dd_i;
    E#i = {});
  for i from lower + 1 to upper do (
    k := 0;  -- column index in i-th differential
    while k < rank C_i do (
      j := 0;  -- row index in i-th differential
      for j in toList rows#(i-1) do (
	a := (D#i)_(j,k);
	if isUnit a then (
	  rows#(i-1) = rows#(i-1) - set{j};
	  rows#i = rows#i - set{k};
	  for ell in toList rows#(i-1) do (
	    b := (D#i)_(ell,k);
	    D#i = rowAdd(D#i, ell, -b*a^(-1), j);
	    D#(i-1) = columnAdd(D#(i-1), j, b*a^(-1), ell));
	  break));
      k = k+1));
  for i from lower to upper do rows#i = toList rows#i;
  E#lower = target submatrix(C.dd_(lower+1), rows#lower, rows#(lower+1));
  for i from lower+1 to upper do (
    E#i = source submatrix(C.dd_i, rows#(i-1), rows#i));
  (chainComplex for i from lower + 1 to upper list (
    (-1)^lower * map(E#(i-1), E#i, submatrix(matrix D#i, rows#(i-1), 
	rows#i))))[-lower])



-- to compute the Hilbert polynomial, we simply interpolated the coefficients
-- for a sufficiently large number of points in the nef cone.  Is there a
-- better way?  
hilbertPolynomial NormalToricVariety := RingElement => opts ->
(cacheValue symbol hilbertPolynomial)(X -> (
    if not isSmooth X  
    then error "not (yet?) implemented for singular toric varieties";    
    d := dim X;
    r := rank picardGroup X;
    R := (ZZ/2)(monoid [local T_0.. local T_r]);
    monomialExp := rsort apply(flatten entries basis({d},R), 
      r -> drop(first exponents r,-1));
    m := #monomialExp;
    nefX := transpose nefGenerators X;
    ell := rank source nefX;
    b := ceiling min(binomial(d+r,r), log_ell binomial(d+r,r));
    while true do (
      Sigma := (toList ((set(0..b-1)) ^** ell));
      nefPoints := unique rsort apply(Sigma,
      	s -> first entries transpose (nefX * transpose matrix {toList s}));
      if #nefPoints >= m then (
	A := matrix table(nefPoints, monomialExp, 
      	  (p,e) -> product(r, j -> (1/1) * (p#j) ^ (e#j)));
	if det( transpose(A) * A ) != 0 then break);
      b = b+1);
    A = (transpose(A)*A)^(-1)* transpose(A);  -- pseudoinverse
    B := transpose matrix {apply(nefPoints, p -> hilbertFunction(p, ring X))};
    hilbertCoeffs := first entries transpose (A * B);
    i := symbol i;
    S := QQ(monoid [i_0..i_(r-1)]);
    sum(m, j -> hilbertCoeffs#j*product(r, k -> S_k^(monomialExp#j#k)))))

hilbertPolynomial (NormalToricVariety,Module) := RingElement => opts -> 
(X,M) -> (
  if not isHomogeneous M then error "expected a homogeneous module";
  if ring X =!= ring M then error "expected module over the Cox ring";
  h := hilbertPolynomial X;
  R := ring h;
  r := numgens R;
  f := poincare M;
  p := pairs standardForm f;
  if #p === 0 then 0_R
  else sum(p, (d,c) -> (
      shift := apply(r, j -> if d#?j then R_j - d#j else R_j);
      c * substitute(h,matrix{shift}))))

hilbertPolynomial (NormalToricVariety, Ring) := RingElement => opts ->
(X,S) -> hilbertPolynomial(X, S^1, opts)
hilbertPolynomial (NormalToricVariety, Ideal) := RingElement => opts ->
(X,I) -> hilbertPolynomial(X, (ring I)^1/I, opts)
hilbertPolynomial (NormalToricVariety, CoherentSheaf) := RingElement => 
opts -> (X,F) -> hilbertPolynomial(X, F.module, opts)

hilbertPolynomial (NormalToricVariety,MultigradedBettiTally) := RingElement =>
opts -> (X,B) -> (
  h := hilbertPolynomial X;
  R := ring h;
  r := numgens R;
  f := poincare(X,B);
  p := pairs standardForm f;
  if #p === 0 then 0_R
  else sum(p, (d,c) -> (
      shift := apply(r, j -> if d#?j then R_j - d#j else R_j);
      c * substitute(h,matrix{shift}))))



pointsIdeal = method()
pointsIdeal (NormalToricVariety, ZZ) := Ideal => (X,m) -> (
  S := ring X;
  d := dim X;
  G := entries nefGenerators X;
  if m < 1 then error "expected a positive integer";
  I := ideal(1_S);
  for j to m-1 do (
    -- construct the complete intersection of random forms whose degrees are 
    -- primitive generators of the nef cone
    while true do (
      J := ideal random(S^1, S^(apply(d, i -> - G#(random(#G)))));
      if codim J == d then break);
    I = intersect(I,J));
  return I)

------------------------------------------------------------------------------
-- DOCUMENTATION
------------------------------------------------------------------------------
beginDocumentation()

document {
  Key => SplendidComplexes2,
  Headline => "a package for working with splendid complexes",
  "A splendid complex is a short chain complex with irrelevant homology.",
  PARA{},
  "This ", EM "Macaulay2", " package is designed to create, manipulate, and
  investigate splendid complexes."
}

document {
  Key => {MultigradedBettiTally,
    (symbol **, MultigradedBettiTally,MultigradedBettiTally),
    (symbol ++, MultigradedBettiTally,MultigradedBettiTally),    
    (symbol ==, MultigradedBettiTally,MultigradedBettiTally),
    (symbol SPACE, MultigradedBettiTally, Array),
    (symbol SPACE, MultigradedBettiTally, List),
    (net, MultigradedBettiTally),
    (pdim, MultigradedBettiTally),
    (symbol *, QQ, MultigradedBettiTally),
    (symbol *, ZZ, MultigradedBettiTally),
    (hilbertPolynomial, NormalToricVariety, MultigradedBettiTally),
    (poincare, NormalToricVariety, MultigradedBettiTally)},
  Headline => "the class of all multigraded Betti tallies",
  "A multigraded Betti tally is a special type of ", TO "Tally", " that is 
  printed as a display of the multigraded Betti numbers.  The class was
  created so that the function ", TO "betti'", " could return something that
  both prints nicely and from which information could be extracted.  The keys
  are triples ", TT "(i,h,d)", " where ", TT "i", " is the homological 
  degree, ", TT "d", " is a list of integers giving a multidegree, and ", 
  TT "h", " is the result of applying a weight covector to ", TT "d", ".",
  PARA{},
  "The data is display as a table.  Each column corresponds a given 
  homological degree appearing as the top entry.  The other entries in a 
  column correspond to a fixed multidegree, ordered by the ", TT "h", 
  ".  The number of summand correspond to a given multidegree appears to 
  the left of the multidegree.",
  EXAMPLE lines ///
    B = new MultigradedBettiTally from {(0,0,{0,0}) => 1, (1,2,{-2,1}) => 2, (1,5,{1,1}) => 2, (2,3,{-1,1}) => 1, (2,6,{-2,2}) => 2, (2,6,{2,1}) => 1, (3,7,{ -1,2}) => 1}
    peek B
    X = hirzebruchSurface 3;
    S = ring X;
    C = res ideal X
    B == betti' C
    peek betti' C
    ///,
  "For convenience, the operations of direct sum (", TO "++", "), tensor 
  product (", TO "**", "), ", TO "pdim", " and degree shifting (numbers in
  brackets or lists in parentheses) have been implemented for multigraded
  Betti tables.  These operations mimic the corresponding operations on
  chain complexes.",
  EXAMPLE lines ///
    B({1,1})
    B[1]
    B[1] ++ B
    B ** B      
    pdim B
    hilbertPolynomial(X,B)
    poincare(X,B)
    ///,
  "A multigraded Betti tally also can multiplied by an integer or by a
  rational number.",
  EXAMPLE lines ///
    3 * B	 
    (1/2) * B
    ///,
  SeeAlso => {
    (hilbertPolynomial,NormalToricVariety),    
    BettiTally,
    poincare}
  }

document {
  Key => {betti',
    (betti',GradedModule)},
  Headline => "display of multigraded degrees in a graded module",
  Usage => "betti' C",
  Inputs => {"C" => GradedModule,
    Weights => {"a ", TO2(List,"list"), " of integers whose dot product with
      the multidegree of a basis element is used to order the elements in each
      column of the display.  The default value uses the ", 
      TO2("heft vectors", "heft vector"), " of the ring." }},
  Outputs => {MultigradedBettiTally => {" a diagram showing the degrees of the
      generators of the modules in ", TT "C"}},
   "The diagram can be used to determine the degrees of the entries in the
   matrices of the differentials in a chain complex (which is a type of 
   graded module) provided they are homogenous maps of degree 0.",
  PARA{},
  "Here is a simple example in which the multidegrees have length 2.",
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    S = ring X;
    C = res ideal X
    B = betti' C
    heft S
    betti'(C, Weights => {1,0})
    betti'(C, Weights => {0,1})    
    ///,     
  "When the degree length is 1, then ", TT "betti'", " provides an 
  alternative display for the graded betti numbers.",
  EXAMPLE lines ///
    S = ring projectiveSpace 3;
    C = res minors(2, matrix table(2,3, (i,j) -> S_(i+j)))
    betti C
    betti' C
    ///,
  SeeAlso => {
    MultigradedBettiTally, 
    (betti, GradedModule), 
    heft}
  }

document {
  Key => {(betti',MultigradedBettiTally)},
  Headline => "view and set the weights of a multigraded Betti tally",
  Usage => "betti' B",
  Inputs => {"B" => MultigradedBettiTally,
    Weights => {"a ", TO2(List,"list"), " of integers whose dot product with
      the multidegree of a basis element is used to order the elements in each
      column of the display.  The default value uses the ", 
      TO2("heft vectors", "heft vector"), " of the ring." }},
  Outputs => {MultigradedBettiTally => {" different from the input only in 
      its ordering of the columns"}},
  "By changing the weights, we can reorder the columns of the diagram.",
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    S = ring X;
    C = res ideal X
    B = betti' C
    toString C.dd_2
    heft S
    betti'(B, Weights => {1,0})
    betti'(B, Weights => {0,1})    
    ///,     
  SeeAlso => {
    MultigradedBettiTally, 
    (betti,BettiTally),
    heft}
  }

document {
  Key => {(betti',Matrix),
    (betti', GroebnerBasis)},
  Headline => "display the multidegrees of a map or Groebner basis",
  Usage => "betti' f",
  Inputs => {"f" => Matrix,
    Weights => {"a ", TO2(List,"list"), " of integers whose dot product with
      the multidegree of a basis element is used to order the elements in each
      column of the display.  The default value uses the ", 
      TO2("heft vectors", "heft vector"), " of the ring." }},
  Outputs => {MultigradedBettiTally => {" a diagram showing the multidegrees 
      of the generators of the source and target modules of ", TT "f"}},
  "Here is a sample diagram.",
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    S = ring X;
    f =  matrix {{x_0*x_1, x_1*x_2, x_0*x_3, x_2*x_3}}
    betti' f
    ///,     
  Caveat => "The diagram ignores the degree of the map itself'.",
  SeeAlso => {
    MultigradedBettiTally, 
    (betti,Matrix),
    (betti,GroebnerBasis)}    
  }

document {
  Key => {(betti', Module),
    (betti', Ideal),
    (betti', MonomialIdeal)},
  Headline => "display the multidegrees of the generators and relations",
  Usage => "betti' M",
  Inputs => {"M" => Module,
    Weights => {"a ", TO2(List,"list"), " of integers whose dot product with
      the multidegree of a basis element is used to order the elements in each
      column of the display.  The default value uses the ", 
      TO2("heft vectors", "heft vector"), " of the ring." }},
  Outputs => {MultigradedBettiTally => {" a diagram showing the multidegrees 
      of the generators and the relations"}},
  "Here is a sample diagram.",      
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    S = ring X;
    M = cokernel matrix {{-x_0*x_3+x_2^2, x_2*x_3, 0, x_3^2}, {-x_0*x_2, -x_0*x_3, -x_0*x_3, -x_1*x_3}, {x_0*x_1,-x_1*x_2, x_2^2, -x_1*x_3}, {0, x_0*x_1, x_0*x_1-x_0*x_2, x_1^2}}
    betti' M
    ///,
  "For an ideal, the output is the multidegrees of the generators and 
  relations fo the quotient of the ambient ring by the ideal.",
  EXAMPLE lines ///    
    I = ideal(x_0*x_1, x_1*x_2, x_0*x_3, x_2*x_3)
    betti' I
    ///,     
  Caveat => "The diagram ignores the degree of the map itself.",
  SeeAlso => {
    MultigradedBettiTally, 
    (betti,Module),
    (betti,Ideal)}
  }

document {
  Key => {minimize,
    (minimize, ChainComplex)},
  Headline => "computes a quasi-isomorphic free complex having minimal ranks",
  Usage => "minimize C",
  Inputs => {"C" => ChainComplex => " consisting of free modules"},
  Outputs => {ChainComplex => {" in which the matrices associated to the 
      differential contain no units"}},
  "Here is a simple example in which the complex ", TT "C", " has a trival
  direct sumannd.",
  EXAMPLE lines ///
    S = QQ[x_0..x_3];
    K = res coker vars S
    C = minimize K;
    C.dd == K.dd
    D = chainComplex id_(S^1)
    C' = K ++ D[-1]
    C'.dd
    C = minimize(K ++ D[-1])
    C.dd == K.dd
    ///,     
  SeeAlso => {chainComplex}
  }

document {
  Key => {(hilbertPolynomial,NormalToricVariety)},
  Headline => "compute the multivariate Hilbert polynomial",
  Usage => "hilbertPolynomial X",
  Inputs => {"X" => NormalToricVariety => " which is nonsingular"},
  Outputs => {RingElement => {" a multivariate polynomial"}},
  "The torus-equivariant Euler characteristic of a smooth normal toric 
  variety is a multivariate polynomial called the Hilbert polynomial. 
  The number of variables equals the rank of the Picard group.  Since a nef 
  line bundle has no higher cohomology on a normal toric variety, the 
  Hilbert polynomial agrees with the dimension of a graded component of 
  the Cox ring at any lattice point in the nef cone. ",
  PARA{},
  "For projective space, we obtain the usual binomial coefficent.",
  EXAMPLE lines ///
    n = 3;
    X = projectiveSpace n;
    h = hilbertPolynomial X    
    R = ring h;    
    h == (1/n!) * product(n, i -> R_0+n-i)
    ///,
  "Here are a couple examples in which the Picard rank is greater than one.",
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    hilbertPolynomial X
    Y = smoothFanoToricVariety(3,11);
    hilbertPolynomial Y
    ///,     
  SeeAlso => {
    (hilbertPolynomial, NormalToricVariety,Module),
    hilbertPolynomial}
  }

document {
  Key => {(hilbertPolynomial,NormalToricVariety,Module),
    (hilbertPolynomial,NormalToricVariety,Ideal),
    (hilbertPolynomial,NormalToricVariety,Ring),
    (hilbertPolynomial,NormalToricVariety,CoherentSheaf)},
  Headline => "compute the multivariate Hilbert polynomial",
  Usage => "hilbertPolynomial(X,M)",
  Inputs => {"X" => NormalToricVariety => " which is nonsingular",
    "M" => Module => {" over the Cox ring of ", TT "X"} },
  Outputs => {RingElement => {" a multivariate polynomial"}},
  "The torus-equivariant Euler characteristic of a smooth normal toric 
  variety is a multivariate polynomial called the Hilbert polynomial. 
  The number of variables equals the rank of the Picard group.  Since a nef 
  line bundle has no higher cohomology on a normal toric variety, the 
  Hilbert polynomial agrees with the dimension of a graded component of 
  the Cox ring at any lattice point in the nef cone. ",
  PARA{},
  "For the twisted cubic curve, we obtain the usual polynomial.",
  EXAMPLE lines ///
    X = projectiveSpace 3;
    S = ring X;
    I = minors(2, matrix table(2,3, (i,j) -> S_(i+j)))
    h = hilbertPolynomial(X,I)    
    ///,
  "Here are a few examples over a toric variety with the Picard rank is 
  greater than one.",
  EXAMPLE lines ///
    X = smoothFanoToricVariety(2,3);
    S = ring X;
    F = OO sum(#rays X, i -> X_i)
    hilbertPolynomial(X,F)
    curve = ideal random(S^1, S^{{ -1,-1,-1}})
    hilbertPolynomial(X,curve)
    points = ideal random(S^1, S^{{ -1,-1,-1},{ -1,0,0}})
    hilbertPolynomial(X,points)
    hilbertPolynomial(X,betti' res points)
    ///,     
  SeeAlso => {hilbertPolynomial,
    (hilbertPolynomial,NormalToricVariety)}
  }

document {
  Key => {pointsIdeal,
    (pointsIdeal,NormalToricVariety,ZZ)},
  Headline => "ideal of a pseudorandom collection of points",
  Usage => "pointsIdeal(X,m)",
  Inputs => {"X" => NormalToricVariety => " which is nonsingular",
    "m" => ZZ => " the number of complete intersection "},
  Outputs => {Ideal => {" in the Cox ring of ", TT "X", " corresponding 
      to a pseudorandom collection of points"}},
  "To create the ideal of a pseudorandom collection of points, 
  we intersect ", TT "m", " complete intersections of ", TT "dim X", "
  homogeneous forms in the Cox ring.  The degree of each individual 
  homogeneous form corresponds to a generator of the nef cone of the 
  underlying toric variety ", TT "X", ".",
  PARA{},
  "On projective space, we obtain the following.",
  EXAMPLE lines ///
    n = 2;
    X = projectiveSpace n;
    I1 = pointsIdeal(X, 1)
    hilbertPolynomial(X,I1)
    I7 = pointsIdeal(X, 7);
    hilbertPolynomial(X,I7)
    ///,
  "Here are a couple examples in which the Picard rank is greater than one.",
  EXAMPLE lines ///
    X = hirzebruchSurface 3;
    I = pointsIdeal(X, 11);
    hilbertPolynomial(X,I)
    Y = smoothFanoToricVariety(3,11);
    J = pointsIdeal(Y, 9);
    hilbertPolynomial(Y,J)
    ///,     
  SeeAlso => {
    random}
  }



------------------------------------------------------------------------------
-- TESTS
------------------------------------------------------------------------------
-- test 0: basic tests for minimize method
TEST ///
S = QQ[x_0..x_3];
K = res coker vars S
C = minimize K;
assert(C.dd^2 == 0)
assert(C.dd == K.dd)
D = chainComplex id_(S^1);
C = minimize(K ++ D[-1]);
assert(C.dd^2 == 0)
assert(C.dd == K.dd)
C = minimize (K ++ D[-1] ++ D[-2] ++ D);
assert(C.dd^2 == 0)
assert(C.dd == K.dd)
C = minimize (K ++ D[-1] ++ D[-2] ++ D[1]);
assert(C.dd^2 == 0)
assert(C.dd == K.dd)
C = minimize (K ++ D[-1] ++ D[-2] ++ D[4]);
assert(C.dd^2 == 0)
assert(C.dd == K.dd)
///
-- test 1: minizing a Taylor resolution
TEST ///
S = QQ[x,y,z];
phi1 = map(S^1,S^{ - 3,-4,-2,-2}, matrix{{x^2*y, x*y^3, x*z, y*z}});
phi2 = map(S^{ -3,-4,-2,-2}, S^{ -5,-4, -4, -5, -5, -3}, 
  matrix{{y^2,z,z,0,0,0},{ -x,0,0,z,z,0}, {0,-x*y, 0,-y^3,0,y},
    {0,0,-x^2,0,-x*y^2,-x}});
phi3 = map(S^{ -5, -4, -4, -5, -5, -3}, S^{ -6,-6,-4,-5},
  matrix{{ -z,-z,0,0},{y^2,0,-1,0},{0,y^2,1,0},{ -x,0,0,-1},
    {0,-x,0,1},{0,0,-x,-y^2}});
phi4 = map(S^{ -6,-6,-4,-5},S^{ -6},
  matrix{{1},{ -1},{y^2},{ -x}});
K = chainComplex(phi1, phi2, phi3, phi4);
assert(K.dd^2 == 0)
C = minimize K;
assert(C.dd^2 == 0)
assert(rank C_0 == 1 and rank C_1 == 4 and rank C_2 == 4 and rank C_3 == 1)
assert(poincare C == poincare K)
///

-- test 2: basic checks on Hilbert polynomials
TEST ///
X = projectiveSpace 3;
h = hilbertPolynomial X;
T = ring h;
assert(h == (1/6)*(T_0+3)*(T_0+2)*(T_0 +1))
ell = 4;
X = hirzebruchSurface ell;
h = hilbertPolynomial X;
T = ring h;
assert(h == T_0*T_1 + (ell/2)*T_1^2 + T_0 +(ell+2)/2*T_1 +1)
///

end
------------------------------------------------------------------------------
-- SCRATCH SPACE
------------------------------------------------------------------------------

restart
uninstallPackage "SplendidComplexes"
installPackage "SplendidComplexes"
check "SplendidComplexes"
needsPackage "SplendidComplexes"


X = projectiveSpace 3;
S = ring X;
I = minors(2,matrix table(2,3, (i,j) -> S_(i+j)));
h = hilbertPolynomial(X,I);
R = ring h;
assert(h == 3*R_0+1)
C = res I;
B = betti' C;
assert(poincare(X,B) == poincare C)
assert(hilbertPolynomial(X,B) == 3*R_0+1)

X = hirzebruchSurface 3;
nefGenerators X


X = smoothFanoToricVariety(3,11);
I = pointsIdeal(X,20);
hilbertPolynomial(X,I)
S = ring X;
res I
vars S
nefGenerators X
picardGroup X

code(nefGenerators, NormalToricVariety)

fourierMotzkin
m = rank target nefGenerators X
r = rank picardGroup X
d = dim X
random(ZZ^1, ZZ^m, Density => 1.0 * d/m, Height => d)
lift(random((ZZ/2)^1, (ZZ/2)^m, Density => 1.0 * d/m),ZZ)
random m

S = ring X;
transpose matrix degrees S
G = entries nefGenerators X
G#0
random (#G)
apply(dim X, i -> -G#(random (#G)))



M = (fourierMotzkin transpose nefGenerators X)#0
N = nefGenerators X
N*M
I = ideal random(S^1, S^{ -{1,0,0,1}, -{0,1,1,0}})
hilbertPolynomial(X,I)

all(flatten entries (matrix{{1,0,0,1}} * M), e -> e <= 0)

isNef 
OO_X(1,0,0,1)

methods(isNef)

ideal(1_S)



X = hirzebruchSurface 3;
I = pointsIdeal(X,7);
hilbertPolynomial(X,I)

restart
uninstallPackage "SplendidComplexes"
installPackage "SplendidComplexes"
check "SplendidComplexes"
needsPackage "SplendidComplexes"


X = projectiveSpace(2)**projectiveSpace(2)
S = ring X
degrees S
I = intersect(apply(2,j-> ideal apply(3,i-> random({1,1},S))));
I = saturate(I,ideal X);
degree I
dim I
betti' res I
F = res I

matrix table(10,10,(i,j) -> hilbertFunction({9-i,j},I))
--(2,1) appears to be in the regularity.



winnowHat = method();

--  Input: two degrees
--  Output:  true if d <= e in the termwise partial order
termwiseLeq = (d,e) -> (
    if #d != #e then error "degrees have difference lengths";
    OUT = true;
    scan(#d,i-> if d_i > e_i then OUT = false);
    OUT
    )

listLeq = (d,L)->(
    OUT = false;
    scan(L,l-> if termwiseLeq(d,l) then OUT = true);
    OUT
    )

linearResDegs = {{{0,0}},{{1,1}},{{2,1},{1,2}},{{2,2}},{{2,2}},{{2,2}}};

--  Input: F a free chain complex on Cox(X).  alpha a degree in Pic(X)
--  Output: the subcomplex of summands generated in degree <= alpha.
--  Caveat:  only really meaningful for a product of projective spaces
--  CAVEAT:  No check that the output is quasisomorphic to the input.
winnowHat (NormalToricVariety, ChainComplex, List) := (X,F,alpha) ->(
    if #alpha != #degree (ring X)_0 then error "degree has wrong length";
    G := F**S^{alpha};
    lowDegreeSpots := for j to length F list(
	for i to rank G_j - 1 list(
	    if listLeq(degree G_j_i , linearResDegs_j) then i else continue
	    ));
    H := chainComplex apply(length G, i ->(
	     submatrix(G.dd_(i+1),lowDegreeSpots_i,lowDegreeSpots_(i+1))));
     H**S^{-alpha}
     );
F' = winnowHat(X,F,{2,1})   
betti' F'
betti' (F**S^{{2,1}})
HS = apply(5,i-> HH_i F');
J = saturate(ann HS_0,ideal X);
J == I
apply({1,2,3,4},i-> saturate(ann HS_i, ideal X))

load "CapeCod.m2"
wF = winnow(X,F,{4,3})
betti' wF
betti' F'
-- winnowHat doesn't work.
F'
wHS = apply(4,i-> HH^i wF);
wJ = saturate(ann wHS_0,ideal X);
wJ == I
apply({1,2,3},i-> saturate(ann wHS_i, ideal X))

lowDegreeSubmatrix = (phi,Ktarget,Ksource) ->(
    lowDegreeSource := for i to rank source phi - 1 list(
	if listLeq(degree (source phi)_i,Ksource) then i else continue);
    lowDegreeTarget := for i to rank target phi - 1 list(
	if listLeq(degree (source phi)_i,Ktarget) then i else continue);
    submatrix(phi,lowDegreeTarget,lowDegreeSource)
    )
resHat = (M,alpha) ->(
    L = apply(linearResDegs, l-> apply(l,ll ->  ll+alpha));
    lowDegreeSpots := for j to length F list(
	for i to rank G_j - 1 list(
	    if listLeq(degree G_j_i , linearResDegs_j) then i else continue
	    ));
    
    phi = {presentation M}
	submatrix(G.dd_(i+1),lowDegreeSpots_i,lowDegreeSpots_(i+1))))
	submatrix(};
    
    H := chainComplex apply(dim S,i->(
	    
	    presentation (S^1/I);
    
    )
M = (S^1/ideal(x_0))
phi = presentation M
