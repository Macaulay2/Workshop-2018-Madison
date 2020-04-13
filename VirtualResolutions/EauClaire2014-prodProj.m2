restart
needsPackage "VirtualResolutions";

--  (PP1)^4:
X = toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)
S = ring X
irr = ideal X
-- 5 points on X:
I = intersect apply(5,i->(
	ideal(random({1,0,0,0},S),random({0,1,0,0},S),random({0,0,1,0},S),random({0,0,0,1},S)))
    );
J = saturate(I,irr);
M = S^1/J
elapsedTime r = res J 
elapsedTime virtualOfPair(J, {{2,1,0,0}}) -- 15s
elapsedTime virtualOfPair(res J, {{2,1,0,0}}) -- 15s
elapsedTime res M
elapsedTime virtualOfPair(M, {{2,1,0,0}}) -- 15s
elapsedTime virtualOfPair(res M, {{2,1,0,0}}) -- 15s

multigraded betti r
-- {2,1,0,0} is in reg(S/J):
hilbertFunction({2,1,0,0},J)
q = winnowProducts(X,r,{2,1,0,0})
saturate(image q.dd_1,irr) == J
--HH_(>2) q = 0
decompose annihilator HH_1 q
r
q
(rank q / rank r)_RR
multigraded betti q
(multigraded betti q, multigraded betti r, multigraded betti r - multigraded betti q)

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
multigraded betti q'


---------------
--  (PP1)^6:
restart
needsPackage "VirtualResolutions";
X = toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)**toricProjectiveSpace(1)
S = ring X
irr = ideal X;
-- 4 points on X:
I = intersect apply(4,i->(
	ideal(random({1,0,0,0,0,0},S),random({0,1,0,0,0,0},S),random({0,0,1,0,0,0},S),random({0,0,0,1,0,0},S),random({0,0,0,0,1,0},S),random({0,0,0,0,0,1},S )))
    );
J  = saturate(I ,irr );
M = S^1/J
elapsedTime res J 
elapsedTime virtualOfPair(J, {{1,1,0,0,0,0}}) -- 15s
elapsedTime virtualOfPair(res J, {{1,1,0,0,0,0}}) -- 15s
elapsedTime res M
elapsedTime virtualOfPair(M, {{1,1,0,0,0,0}}) -- 15s
elapsedTime virtualOfPair(res M, {{1,1,0,0,0,0}}) -- 15s

multigraded betti r 
multigraded betti  r 
-- {1,1,0,0,0,0} is in reg(S/J):
hilbertFunction({1,1,0,0,0,0},J )
--w = winnowProducts(X ,r ,{1,1,0,0,0,0})
w
multigraded betti w
saturate(image w.dd_1,irr ) == J 
--prune HH w
--decompose annihilator HH_1 w
r 
w
(rank w / rank r )_RR
multigraded betti  w
