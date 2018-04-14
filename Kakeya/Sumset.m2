
+ M2 --no-readline --print-width 213
Macaulay2, version 1.11
with packages: ConwayPolynomials, Elimination, IntegralClosure, InverseSystems, LLLBases, PrimaryDecomposition, ReesAlgebra, TangentCone

i1 : loadPackage "Sumset"
Sumset.m2:14:9:(3):[7]: error: missing semicolon or comma on previous line?
stdio:1:1:(3): --backtrace: parse error--

i2 : loadPackage "Sumset"
Sumset.m2:64:1:(2):[7]: error: missing Key

i3 : loadPackage "Sumset"

o3 = Sumset

o3 : Package

i4 : check "Sumset"
--running test 0 of package Sumset on line 61 in file ./Sumset.m2
--    rerun with: check_0 "Sumset"
--making test results in file /tmp/M2-92-0/0.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/1-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/0.m2" >>"/tmp/M2-92-0/0.tmp" 2>&1
/tmp/M2-92-0/0.tmp:0:1: (output file) error: Macaulay2 exited with status code 1
/tmp/M2-92-0/0.m2:0:1: (input file)
M2: *** Error 1
stdio:4:1:(3): error: 1 error(s) occurred running tests for package Sumset

i5 : k = ZZ/101

o5 = k

o5 : QuotientRing

i6 : R = k[a,b]

o6 = R

o6 : PolynomialRing

i7 : I = idealFromPts({{1,0},{0,1}},R)

               2
o7 = ideal (- b  + b, -a*b, a*b - a - b + 1)

o7 : Ideal of R

i8 : assert(I == ideal(a*b, a+b-1))

i9 : T = k[t_1,t_2]

o9 = T

o9 : PolynomialRing

i10 : J = intersect(ideal(t_1-1,t_2-1),ideal(t_1-2,t_2-1))

                                                 2
o10 = ideal (- t  + 1, - t t  + t  + 2t  - 2, - t  + 3t  - 2)
                2         1 2    1     2         1     1

o10 : Ideal of T

i11 : S = sumset(I, idealFromPt({1,1},R))

                           2
o11 = ideal (t  + t  - 3, t  - 3t  + 2)
              1    2       2     2

o11 : Ideal of k[t , t ]
                  1   2

i12 : assert((map(T,ring S,gens T))(S) == J)
stdio:12:1:(3): error: assertion failed

i13 : check "Sumset"
--running test 0 of package Sumset on line 61 in file ./Sumset.m2
--    rerun with: check_0 "Sumset"
--making test results in file /tmp/M2-92-0/2.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/3-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/2.m2" >>"/tmp/M2-92-0/2.tmp" 2>&1
/tmp/M2-92-0/2.tmp:0:1: (output file) error: Macaulay2 exited with status code 1
/tmp/M2-92-0/2.m2:0:1: (input file)
M2: *** Error 1
stdio:13:1:(3): error: 1 error(s) occurred running tests for package Sumset

i14 : T = k[t_1,t_2]

o14 = T

o14 : PolynomialRing

i15 : J = intersect(ideal(t_1-1,t_2-2),ideal(t_1-2,t_2-1))

              2
o15 = ideal (t  - 3t  + 2, - t t  + t  + t  - 1, t t  - 2t  - 2t  + 4)
              2     2         1 2    1    2       1 2     1     2

o15 : Ideal of T

i16 : S = sumset(I, idealFromPt({1,1},R))

                           2
o16 = ideal (t  + t  - 3, t  - 3t  + 2)
              1    2       2     2

o16 : Ideal of k[t , t ]
                  1   2

i17 : assert((map(T,ring S,gens T))(S) == J)

i18 : loadPackage("Sumset",Reload=>true)

o18 = Sumset

o18 : Package

i19 : check "Sumset"
--running test 0 of package Sumset on line 61 in file ./Sumset.m2
--    rerun with: check_0 "Sumset"
--making test results in file /tmp/M2-92-0/4.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/5-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/4.m2" >>"/tmp/M2-92-0/4.tmp" 2>&1

i20 : R = QQ[x,y]

o20 = R

o20 : PolynomialRing

i21 : I = ideal(x^2,y^2,random(1,R))

              2   2  5
o21 = ideal (x , y , -x + y)
                     4

o21 : Ideal of R

i22 : J = ideal((x-1)^2,y^3)

              2            3
o22 = ideal (x  - 2x + 1, y )

o22 : Ideal of R

i23 : sumset(I,J)

              3     2             4     2 2       3        2     3      2
o23 = ideal (t  - 3t  + 3t  - 1, t , 15t t  + 8t t  - 30t t  - 8t  + 15t )
              1     1     1       2     1 2     1 2      1 2     2      2

o23 : Ideal of QQ[t , t ]
                   1   2

i24 : primaryDecomposition oo

               3     2             4     2 2       3        2     3      2
o24 = {ideal (t  - 3t  + 3t  - 1, t , 15t t  + 8t t  - 30t t  - 8t  + 15t )}
               1     1     1       2     1 2     1 2      1 2     2      2

o24 : List

i25 : minimalPrimes o23

o25 = {ideal (t , t  - 1)}
               2   1

o25 : List

i26 : I = ideal(y^2 - x^3 + x)

               3    2
o26 = ideal(- x  + y  + x)

o26 : Ideal of R

i27 : GF(9)

o27 = GF 9

o27 : GaloisField

i28 : k = GF(9)

o28 = k

o28 : GaloisField

i29 : R = k[x,y]

o29 = R

o29 : PolynomialRing

i30 : I = ideal(y^2 - x^3 + x)

               3    2
o30 = ideal(- x  + y  + x)

o30 : Ideal of R

i31 : k = GF(25)

o31 = k

o31 : GaloisField

i32 : R = k[x,y]

o32 = R

o32 : PolynomialRing

i33 : I1 = ideal(y^2 - x^3 + x, x)

                3    2
o33 = ideal (- x  + y  + x, x)

o33 : Ideal of R

i34 : I2 = ideal(y^2 - x^3 + x, x - 2)

                3    2
o34 = ideal (- x  + y  + x, x - 2)

o34 : Ideal of R

i35 : sumset(I1,I2)

                      4     2
o35 = ideal (t  - 2, t  - 2t  + 1)
              1       2     2

o35 : Ideal of k[t , t ]
                  1   2

i36 : minimalPrimes oo
stdio:36:1:(3): error: expected base field to be QQ or ZZ/p

i37 : minimalPrimes sub(o35, ZZ/5[t_1,t_2])

o37 = {}

o37 : List

i38 : k = ZZ/5

o38 = k

o38 : QuotientRing

i39 : R = k[x,y]

o39 = R

o39 : PolynomialRing

i40 : I1 = ideal(y^2 - x^3 + x, x)

                3    2
o40 = ideal (- x  + y  + x, x)

o40 : Ideal of R

i41 : I2 = ideal(y^2 - x^3 + x, x - 2)

                3    2
o41 = ideal (- x  + y  + x, x - 2)

o41 : Ideal of R

i42 : sumset(I1,I2)

                      4     2
o42 = ideal (t  - 2, t  - 2t  + 1)
              1       2     2

o42 : Ideal of k[t , t ]
                  1   2

i43 : S = sumset(I1,I2)

                      4     2
o43 = ideal (t  - 2, t  - 2t  + 1)
              1       2     2

o43 : Ideal of k[t , t ]
                  1   2

i44 : minimalPrimes S

o44 = {ideal (t  + 1, t  - 2), ideal (t  - 1, t  - 2)}
               2       1               2       1

o44 : List

i45 : loadPackage("Sumset",Reload=>true)
Sumset.m2:30:5:(2):[7]: error: missing semicolon or comma on previous line?
stdio:45:1:(3): --backtrace: parse error--

i46 : loadPackage("Sumset",Reload=>true)

o46 = Sumset

o46 : Package

i47 : check "Sumset"
--running test 0 of package Sumset on line 58 in file ./Sumset.m2
--    rerun with: check_0 "Sumset"
--making test results in file /tmp/M2-92-0/6.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/7-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/6.m2" >>"/tmp/M2-92-0/6.tmp" 2>&1
--running test 1 of package Sumset on line 66 in file ./Sumset.m2
--    rerun with: check_1 "Sumset"
--making test results in file /tmp/M2-92-0/8.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/9-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/8.m2" >>"/tmp/M2-92-0/8.tmp" 2>&1
--running test 2 of package Sumset on line 75 in file ./Sumset.m2
--    rerun with: check_2 "Sumset"
--making test results in file /tmp/M2-92-0/10.out
ulimit -t 700; ulimit -m 850000; ulimit -v 850000; ulimit -s 8192; cd /tmp/M2-92-0/11-rundir/; /usr/bin/M2-binary --silent --print-width 77 --stop --int --no-readline --no-randomize -e 'needsPackage("Sumset", FileName => "/home/wanlin/Sumset.m2")' <"/tmp/M2-92-0/10.m2" >>"/tmp/M2-92-0/10.tmp" 2>&1

i48 : 	    k = ZZ/101

o48 = k

o48 : QuotientRing

i49 : 	    R = k[x1,x2,x3,x4]

o49 = R

o49 : PolynomialRing

i50 : 	    I1 = idealFromPts({{0,0,0,0},{1,2,4,8},{1,1,1,1}},R)

                             2                     2                    2                            2
o50 = ideal (- 27x3*x4 + 26x4  + x4, 25x3*x4 - 25x4  + 2x3 - 2x4, - 25x3  + 25x3*x4 - x3 + x4, - 27x3  + 26x3*x4 + x3, - 25x2*x3 + 25x2*x4 + 50x3 - 50x4, - 27x2*x3 + 26x2*x4 - 49x3 + 50x4, 27x2*x3 - 26x2*x4 - x2,
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
      - 25x1*x3 + 25x1*x4 + 25x3 - 25x4, - 27x1*x3 + 26x1*x4 + 27x3 - 26x4, 27x1*x3 - 26x1*x4 - x1)

o50 : Ideal of R

i51 :     	    I2 = idealFromPts({{1,-1,1,-1},{1,3,9,27},{1,0,0,0}},R)

                             2                              2                    2                              2
o51 = ideal (- 14x3*x4 - 14x4  - 26x3 - 26x4, 26x3*x4 + 25x4  + 26x3 + 25x4, 26x3  + 25x3*x4 - 26x3 - 25x4, 14x3  + 14x3*x4 - 25x3 - 25x4, - 26x2*x3 - 25x2*x4 - 26x3 - 25x4, 26x2*x3 + 25x2*x4 - x2 - 42x3 - 42x4,
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
      14x2*x3 + 14x2*x4 - 42x3 - 42x4, - 26x1*x3 - 25x1*x4 + 26x3 + 25x4, 26x1*x3 + 25x1*x4 - x1 - 26x3 - 25x4 + 1, 14x1*x3 + 14x1*x4 - 14x3 - 14x4)

o51 : Ideal of R

i52 : 	    sumset(I1,I2)

                                         2                                           2                        2                                             2                      2                                 
o52 = ideal (t t  - 28t t  + 15t t  - 23t  + 20t  + 27t  - 10t  - 3t  - 20, t t  + 8t  - 47t t  - 14t t  - 46t  + 26t  + 24t  - 29t  - 24t  - 26, t t  + 37t  - 12t t  + 18t t  - t  - 24t  - 3t  + 37t  + 47t  + 24,
              1 4      2 4      3 4      4      1      2      3     4        2 3     3      2 4      3 4      4      1      2      3      4        1 3      3      2 4      3 4    4      1     2      3      4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       2    2                       2                                            2                      2                                  2             3                        2                                  
      t  + t  - 39t t  + 7t t  + 39t  - 32t  + 32t  + 14t  - 23t  + 32, t t  + 9t  - 35t t  - 7t t  - 7t  - 11t  + 9t  + 38t  + 2t  + 11, t  - 3t  + 2, t  - 37t t  + 47t t  + 37t  + 23t  + 27t  + 39t  - 36t  - 23,
       2    3      2 4     3 4      4      1      2      3      4        1 2     3      2 4     3 4     4      1     2      3     4        1     1       4      2 4      3 4      4      1      2      3      4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
         2      2                      2                                      2      2                     2                                    2                          2                                    3  
      t t  + 47t  + t t  + 41t t  + 45t  - 44t  + 48t  + 29t  + 34t  + 44, t t  - 12t  - t t  - 3t t  - 11t  + 15t  + 11t  - 34t  + 34t  - 15, t t  - 21t t  - 31t t  + 21t  - 31t  - 28t  - 35t  + 23t  + 31, t  +
       3 4      3    2 4      3 4      4      1      2      3      4        2 4      3    2 4     3 4      4      1      2      3      4        3 4      2 4      3 4      4      1      2      3      4        3  
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
         2                       2
      49t  + 48t t  + 23t t  + 4t  - 7t  + 22t  - 48t  + 9t  + 7)
         3      2 4      3 4     4     1      2      3     4

o52 : Ideal of k[t , t , t , t ]
                  1   2   3   4

i53 : 	    minimalPrimes(S)

o53 = {ideal (t  + 1, t  - 2), ideal (t  - 1, t  - 2)}
               2       1               2       1

o53 : List

i54 : 	    S = sumset(I1,I2)

                                         2                                           2                        2                                             2                      2                                 
o54 = ideal (t t  - 28t t  + 15t t  - 23t  + 20t  + 27t  - 10t  - 3t  - 20, t t  + 8t  - 47t t  - 14t t  - 46t  + 26t  + 24t  - 29t  - 24t  - 26, t t  + 37t  - 12t t  + 18t t  - t  - 24t  - 3t  + 37t  + 47t  + 24,
              1 4      2 4      3 4      4      1      2      3     4        2 3     3      2 4      3 4      4      1      2      3      4        1 3      3      2 4      3 4    4      1     2      3      4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
       2    2                       2                                            2                      2                                  2             3                        2                                  
      t  + t  - 39t t  + 7t t  + 39t  - 32t  + 32t  + 14t  - 23t  + 32, t t  + 9t  - 35t t  - 7t t  - 7t  - 11t  + 9t  + 38t  + 2t  + 11, t  - 3t  + 2, t  - 37t t  + 47t t  + 37t  + 23t  + 27t  + 39t  - 36t  - 23,
       2    3      2 4     3 4      4      1      2      3      4        1 2     3      2 4     3 4     4      1     2      3     4        1     1       4      2 4      3 4      4      1      2      3      4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
         2      2                      2                                      2      2                     2                                    2                          2                                    3  
      t t  + 47t  + t t  + 41t t  + 45t  - 44t  + 48t  + 29t  + 34t  + 44, t t  - 12t  - t t  - 3t t  - 11t  + 15t  + 11t  - 34t  + 34t  - 15, t t  - 21t t  - 31t t  + 21t  - 31t  - 28t  - 35t  + 23t  + 31, t  +
       3 4      3    2 4      3 4      4      1      2      3      4        2 4      3    2 4     3 4      4      1      2      3      4        3 4      2 4      3 4      4      1      2      3      4        3  
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
         2                       2
      49t  + 48t t  + 23t t  + 4t  - 7t  + 22t  - 48t  + 9t  + 7)
         3      2 4      3 4     4     1      2      3     4

o54 : Ideal of k[t , t , t , t ]
                  1   2   3   4

i55 : 	    minimalPrimes(S)

o55 = {ideal (t , t , t  - 1, t ), ideal (t  - 5, t  - 7, t  - 2, t  - 1), ideal (t  - 4, t  - 8, t  - 2, t  - 2), ideal (t  - 9, t  - 27, t  - 1, t  - 3), ideal (t  - 2, t , t  - 2, t ), ideal (t  - 13, t  - 35,
               3   4   1       2           3       4       1       2               3       4       1       2               3       4        1       2               3       4   1       2           3        4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
      t  - 2, t  - 5), ideal (t  - 1, t  + 1, t  - 1, t  + 1), ideal (t  - 1, t  - 1, t  - 2, t  - 1), ideal (t  - 10, t  - 28, t  - 2, t  - 4)}
       1       2               3       4       1       2               3       4       1       2               3        4        1       2

o55 : List

i56 : 	    netList minimalPrimes S

      +----------------------------------------+
o56 = |ideal (t , t , t  - 1, t )              |
      |        3   4   1       2               |
      +----------------------------------------+
      |ideal (t  - 5, t  - 7, t  - 2, t  - 1)  |
      |        3       4       1       2       |
      +----------------------------------------+
      |ideal (t  - 4, t  - 8, t  - 2, t  - 2)  |
      |        3       4       1       2       |
      +----------------------------------------+
      |ideal (t  - 9, t  - 27, t  - 1, t  - 3) |
      |        3       4        1       2      |
      +----------------------------------------+
      |ideal (t  - 2, t , t  - 2, t )          |
      |        3       4   1       2           |
      +----------------------------------------+
      |ideal (t  - 13, t  - 35, t  - 2, t  - 5)|
      |        3        4        1       2     |
      +----------------------------------------+
      |ideal (t  - 1, t  + 1, t  - 1, t  + 1)  |
      |        3       4       1       2       |
      +----------------------------------------+
      |ideal (t  - 1, t  - 1, t  - 2, t  - 1)  |
      |        3       4       1       2       |
      +----------------------------------------+
      |ideal (t  - 10, t  - 28, t  - 2, t  - 4)|
      |        3        4        1       2     |
      +----------------------------------------+

i57 : 	    pts = minimalPrimes S

o57 = {ideal (t , t , t  - 1, t ), ideal (t  - 5, t  - 7, t  - 2, t  - 1), ideal (t  - 4, t  - 8, t  - 2, t  - 2), ideal (t  - 9, t  - 27, t  - 1, t  - 3), ideal (t  - 2, t , t  - 2, t ), ideal (t  - 13, t  - 35,
               3   4   1       2           3       4       1       2               3       4       1       2               3       4        1       2               3       4   1       2           3        4      
      ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
      t  - 2, t  - 5), ideal (t  - 1, t  + 1, t  - 1, t  + 1), ideal (t  - 1, t  - 1, t  - 2, t  - 1), ideal (t  - 10, t  - 28, t  - 2, t  - 4)}
       1       2               3       4       1       2               3       4       1       2               3        4        1       2

o57 : List

i58 : 	    intersect pts == S

o58 = true

i59 : 