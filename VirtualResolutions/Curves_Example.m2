loadPackage "SpaceCurves"
installPackage "VirtualResolutions"

R = ZZ/32003[x_0..x_3];
Q = quadricSurface(R); 
X = cubicSurface(R);
Y = quarticSurfaceRational(R);

LQ = smoothDivisors(7,Q);
genus7DivsQ = delete(,apply(LQ, D->(
	if genus curve D == 3 then D
	)))

LX = smoothDivisors(7,X);
genus7DivsX = delete(,apply(LX, D->(
	if genus curve D == 3 then D
	)))

LY = smoothDivisors(7,Y);
genus7DivsY = delete(,apply(LY, D->(
	if genus curve D == 3 then D
	)))

genus7Divs = genus7DivsQ|genus7DivsX|genus7DivsY

D  = genus7Divs#0
divCheck = (D,L)->(
    L1 = apply(L,d->d#Coordinate);
    isSubset({D#Coordinate},L1)
    )
divCheck(D,genus7Divs)

H = new MutableHashTable  
apply(500,i->(
        R := ZZ/32003[t_0..t_3];
	C := curve(7,3,R);
	I1 := ideal C;
	I := curveFromP3toP1P2(I1);
	S := ring I;
	B := intersect(ideal(x_(0,0), x_(0,1)), ideal(x_(1,0), x_(1,1), x_(1,2)));
	J := saturate(I,B);
	divC = divisor C;
	divCordC := (divisor C)#Coordinate;
	mgRegC := multigradedRegularity(S, S^1/J);
	print i;
	if isSubset({divCordC},keys H) == true then H#divCordC = H#divCordC|mgRegC;
	if isSubset({divCordC},keys H) == false then H#divCordC = mgRegC;
	--if divCheck(divC,keys H) == true then H#divC = H#divC|{mgRegC};
	--if  divCheck(divC,keys H) == false then H#divC = mgRegC;
	))
H = new HashTable from H
uniqueResults = applyValues(H, v -> unique v)
