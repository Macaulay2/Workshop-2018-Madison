
//Please see this example to use the function
//This algorithm is based on the paper:
//"Kapur, D., Sun, Y., and Wang, D.K., 2010. A new algorithm for computing comprehensive Gr\"obner systems. In Proceedings of ISSAC'2010, ACM Press, New York, 29-36."
//The algorithm is implemented by Yao SUN (sunyao@amss.ac.cn)
//Last revised: April, 4th, 2011.

//Main function: ParaGB(P, varlen, ZE, NE, PS)
//Input: P ---- a polynomial ring
//       varlen ----- number of variables (not including parameters)
//       ZE ---- initial zero constaints
//       NE ---- initial non-zero constaints
//       PS ---- a set of polynomials in the ring P
//Output: A comprehensive Groebner systems of PS


//load the functions from the file "cgs-online.txt" 
load "d:\\cgs-online.txt"; 


//set the polynomial ring
P<x,a,b,c,d>:=PolynomialRing(RationalField(),5,"elim",[1],[2,3,4,5]);

//number of variables (not including parameters)
varlen:=1;

//initial zero constraints: ZE={a, b} means a=0 AND b=0
ZE:=[];

//intial non-zero constraints: NE={a, b} means a<>0 AND b<>0, which is slightly different from the set N in the paper. If NE is empty, then no initial non-zero constraints are considered
NE:=[];

//inital polynomial set
PS:=[x^4+a*x^3+b*x^2+c*x+d,4*x^3+3*a*x^2+2*b*x+c];

//main function
time cgs:=ParaGB(P, varlen, ZE, NE, PS); 

//number of branches
"Number of branches: ", #cgs; 

//print the outputs to the file "output.txt"
PrintPGB(P, PS, cgs);