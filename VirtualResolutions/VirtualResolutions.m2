-*
restart
loadPackage("VirtualResolutions", Reload =>true)
installPackage "VirtualResolutions"
viewHelp "VirtualResolutions"
viewHelp "TateOnProducts"
check "VirtualResolutions"
*-

newPackage ("VirtualResolutions",
    Version => "0.0",
    Date => "April 14, 2018",
    Headline => "Methods for virtual resolutions on products of projective spaces",
    Authors =>{
    	{Name =>"Ayah Almousa"},
    	{Name =>"Christine Berkesch"},
    	{Name =>"David Eisenbud"},
    	{Name =>"Mahrud Sayrafi"}
    	},
    PackageExports => {"TateOnProducts"},
    DebuggingMode => true
    )

export{
    "multiBetti"
    }

monomial = (R, d, n) -> (
    m := 1_R * n;
    apply(pairs d, (i, e) -> m = m * R_i ^ e);
    m
    )

multiBetti = method()
multiBetti GradedModule := C -> (
    complete C;
    N := degreeLength ring C;
    R := ZZ[vars(0..N-1)];
    heftfn := d -> d//sum;
    v := new HashTable from flatten apply(
	select(pairs C, (i,F) -> class i === ZZ), 
	(i,F) -> apply(pairs tally degrees F, (d,n) -> (i,d,heftfn d) => n));
    v' := new MutableHashTable;
    cols := {};
    rows := {};
    scan(pairs v, (key,n) -> (
	    (i,d,h) := key;
	    m := monomial(R, d, n);
	    key = (h, i);
	    rows = append(rows, h);
	    cols = append(cols, i);
	    if v'#?key then v'#key = v'#key + m else v'#key = m;
	    ));
    cols = sort unique cols;
    rows = sort unique rows;
    v = v';
    v = table(toList (0 .. length rows - 1), toList (0 .. length cols - 1),
	(i,j) -> if v#?(rows#i,cols#j) then v#(rows#i,cols#j) else 0);
    leftside := prepend("", apply(length rows, i -> toString (rows#i) | ":"));
    v = applyTable(v, bt -> if bt === 0 then "." else bt);
    v = prepend(toString \ cols, v);
    v = apply(leftside,v,prepend);
    netList(v, Alignment => Right,
	 HorizontalSpace => 1, BaseRow => 1, Boxes => false)
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
loadPackage "VirtualResolutions"
R = ZZ/32003[a,b, Degrees => {{1,0}, {0,1}}]
I = ideal"a2,b2,ab"
C = res I
multiBetti C
