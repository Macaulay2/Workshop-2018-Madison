needsPackage "VirtualResolutions";

case = (n, m) -> (
    --  (PP1)^n:
    X = fold((i,j) -> i ** j, toList (n:toricProjectiveSpace 1));
    S = ring X;
    irr = ideal X;
    -- m points on X:
    I = intersect apply(m, i -> ideal apply(n, j -> random(entries ZZ^n_j, S)));
    J = saturate(I,irr);
    --d = first multigradedRegularity(X, J);
    --elapsedTime print res J
    elapsedTime print virtualOfPair(J, {toList((n-1):0)|{m-1}}) -- 15s
    --elapsedTime print virtualOfPair(r, {{2,1,0,0}}) -- 33s
    )

end--

restart
load "GrowthTest.m2"

for n from 2 to 7 do case(n, 3);
