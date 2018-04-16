-*
restart
loadPackage("VirtualResolutions", Reload =>true)
installPackage "VirtualResolutions"
installPackage "CompleteIntersectionResolutions"
installPackage "BGG"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
viewHelp CompleteIntersectionResolutions
check "VirtualResolutions"
*-
---------------------------------------------------------------------------
-- PURPOSE : 
--           
--
-- PROGRAMMERS : 
--               
--
-- UPDATE HISTORY : created 14 April 2018;
---------------------------------------------------------------------------
newPackage ("VirtualResolutions",
    Version => "0.0",
    Date => "April 14, 2018",
    Headline => "Methods for virtual resolutions on products of projective spaces",
    Authors =>{
    	{Name => "Ayah Almousa",       Email => "aka66@cornell.edu"},
    	{Name => "Christine Berkesch", Email => "cberkesc@umn.edu",    HomePage => "http://www-users.math.umn.edu/~cberkesc/"},
        {Name => "David Eisenbud",     Email => "de@msri.org",         HomePage => "http://www.msri.org/~de/"},
        {Name => "Mahrud Sayrafi",     Email => "mahrud@berkeley.edu"}
    	},
    PackageExports => {
	"BGG",
	"TateOnProducts",
	"CompleteIntersectionResolutions"
	},
    DebuggingMode => true,
    AuxiliaryFiles => false
    )

export{
    "multiBetti",
    "HideZeros",
    "DegreeBounds"
    }


monomial = (R, d, n) -> (
    m := 1_R * n;
    apply(pairs d, (i, e) -> m = m * R_i ^ e);
    m
    )

-- TODO: incorporate Minimize and Weights options
multiBetti = method(Options => 
    options betti ++ {
	HideZeros => false,
	DegreeBounds => null,
	})
multiBetti GradedModule := opts -> C -> (
    complete C;
    N := degreeLength ring C;
    R := ZZ[vars(0..N-1)];
    bt := betti(C, Weights => if opts.?Weights then opts.Weights else apply(N, i->1));
    ht := new MutableHashTable;
    (rows, cols) := ({}, {});
    scan(pairs bt,
	(key,n) -> (
	    (i,d,h) := key;
	    key = (h, i);
	    (rows, cols) = (append(rows, h), append(cols, i));
	    m := if opts.DegreeBounds === null or all(N, i->d#i<=opts.DegreeBounds#i)
	        then monomial(R, d, n) else 0;
	    if ht#?key then ht#key = ht#key + m else ht#key = m;
	    ));
    (rows, cols) = if opts.HideZeros === true then (
	sort unique rows, sort unique cols
	) else (
	toList (min rows .. max rows), toList (min cols .. max cols)
	);
    mbt := table(toList (0 .. length rows - 1), toList (0 .. length cols - 1),
	(i,j) -> if ht#?(rows#i,cols#j) then ht#(rows#i,cols#j) else 0);
    -- Making the table
    xAxis := toString \ cols;
    yAxis := (i -> toString i | ":") \ rows;
    mbt = applyTable(mbt, n -> if n === 0 then "." else n);
    mbt = prepend(xAxis, mbt);
    mbt = apply(prepend("", yAxis), mbt, prepend);
    netList(mbt, Alignment => Right, HorizontalSpace => 2, BaseRow => 1, Boxes => false)
    )

--------------------------
-- Begining of the documentation
------------------------
beginDocumentation()



--------------------------
-- Begining of the TESTS
------------------------


end--

restart
installPackage "VirtualResolutions"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
check "VirtualResolutions"

restart
loadPackage("VirtualResolutions", Reload =>true)
R = ZZ/32003[a,b, Degrees => {{1,0}, {0,1}}]
I = ideal"a2,b2,ab"
C = res I
multiBetti C

restart
needsPackage "VirtualResolutions"
needsPackage "SplendidComplexes"
load "CapeCod.m2"
X = projectiveSpace(1)**projectiveSpace(2)
S = ring X
irr = ideal X
I' = ideal(x_0^2*x_2^2+x_1^2*x_3^2+x_0*x_1*x_4^2, x_0^3*x_4+x_1^3*(x_2+x_3))
J' = saturate(I',irr);
hilbertPolynomial(X,J')
r' = res J'
multiBetti r'
multiBetti(r', DegreeBounds => {3, 3})
