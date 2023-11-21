
Attach("g2-jac.m");
Attach("add.m");

// search for points on Jacobian J over number field K
// up to 'height' B (see code below)
searchJ:=function(J,B);
	K:=BaseField(J);
	OK:=Integers(K);
	d:=Degree(K);
	bas:=Basis(OK);
	KS:=KummerSurface(J);
	E:=KS`Equation;
	S:=CartesianPower([-B..B],d);	
	S:=[&+[a[i]*bas[i] : i in [1..d]] : a in S]; // all elts of OK with coeffs le B
	_<x4>:=PolynomialRing(K);
	pointsKS:={};
	for a1,a2,a3 in S do
        	if <a1,a2,a3> ne <K!0,K!0,K!0> then
                	f:=Evaluate(E,[a1,a2,a3,x4]);
            		pointsKS:=pointsKS join {KS![a1,a2,a3,r[1]] : r in Roots(f)};
        	end if;
	end for;
	pointsJ:=[];
	for P in pointsKS do
		QP:=Points(J,P);
		if #QP ne 0 then
			Append(~pointsJ, Random(QP)); // only want one up to sign
		end if;
		//pointsJ:=pointsJ cat [Q : Q in Points(J,P)];
	end for;
	f:=func<P,Q | Degree(P[1])-Degree(Q[1])>;
	return Sort(pointsJ,f);  // put the degree 1 points first
end function;

// search for points on genus 2 curve over number field K
// up to 'height' B (see code below)
searchC:=function(C,B);
	K:=BaseField(C);
	OK:=Integers(K);
	d:=Degree(K);
	bas:=Basis(OK);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	S:=CartesianPower([-B..B],d);	
	S:=[&+[a[i]*bas[i] : i in [1..d]] : a in S]; // all elts of OK with coeffs le B
	ptsinf:=PointsAtInfinity(C);
	pts:=[Universe(ptsinf) | ];
	if #ptsinf ne 0 then
		Include(~pts,Random(ptsinf));
	end if;
	for s in S do
		for t in Exclude(S,OK!0) do
			u:=s/t;
			vsq:=Evaluate(f,u);
			tf,v:=IsSquare(vsq);
			if tf then
				Include(~pts,C![u,v]);
			end if;
		end for;
	end for;
	return pts;	
end function;

// pointsJ is a list of points on Jacobian J of a genus 2 curve
// over a number field K
// returns ptsJ,T,f
// where ptsJ is a basis for a free subgroup of span of pointsJ
// T is isomorphic to a subgroup of the torsion subgroup of span of pointsJ
// f is the isomorphism T->subgroup of torsion subgroup of span of pointsJ
// and very very likely:
// ptsJ is a free basis for (span of pointsJ)/torsion
// T is isomorphic to the whole torsion subgroup of span(pointsJ)
reduce:=function(pointsJ);
	J:=Universe(pointsJ);
	if #pointsJ eq 0 then
		T:=FreeAbelianGroup(0);
		f:=func<t | J!0>;
		return pointsJ,T,f;
	end if;
	K:=BaseField(J);
	OK:=Integers(K);
	disc:=OK!(Discriminant(Curve(J)));
	r:=#pointsJ;
	A:=FreeAbelianGroup(r);
	amb:=StandardLattice(r);	
	ker:=amb;
	l:=2;
	while l lt 50 do
       	        l:=l+1;
               	if IsPrime(l) then
                       	lFac:=[L[1] : L in Factorization(l*OK)];
                        for P in lFac do
       	                        if Valuation(disc*OK,P) eq 0 then
               	                	Jk,pointsP:=reduceModP(J,pointsJ,P);
                       	                B,phi:=AbelianGroup(Jk);
					pointsB:=[b@@phi : b in pointsP];
					psi:=hom<A->B | pointsB>;
					ker:=ker meet sub<amb | [amb!Eltseq(A!k) : k in Generators(Kernel(psi))]>;
					ker:=sub<amb | [amb!k : k in Basis(ker)]>;
				end if;
			end for;
		end if;
	end while;
	kermat:=Rows(LLLBasisMatrix(ker));
	kermat:=[amb!k : k in kermat];
	ker:=[Eltseq(k) : k in kermat | Length(k) lt 100];
	//ker:=[Eltseq(amb!k) : k in Basis(ker) | Length(k) lt 100];
	ker:=[k : k in ker | &+[J | k[i]*pointsJ[i] : i in [1..r]] eq J!0];
	if #ker ge 1 then
		M:=Matrix(ker);
		N,U,V:=SmithForm(M);
		Vin:=V^(-1);
		pointsJ:=[&+[J | v[i]*pointsJ[i] : i in [1..r]] : v in Rows(Vin)];
		D:=Diagonal(N);
		j:=Max([i : i in [1..#D] | D[i] ne 0]);
		newPointsJ:=[pointsJ[i] : i in [(j+1)..r]];
		if independentModTorsion(newPointsJ) eq false then
			error("this is extremely unlikely to happen!!!");
		end if;
		l:=Max([i : i in [1..#D] | D[i] eq 1]);
		tors:=[pointsJ[i] : i in [(l+1)..j]];
		T:=AbelianGroup([D[i] : i in [(l+1)..j]]);
		f:=func<t | &+[J| Eltseq(t)[i]*tors[i] : i in [1..#tors]] >;
		return newPointsJ,T,f;
	else
		if independentModTorsion(pointsJ) eq false then
			error("this is extremely unlikely to happen!!!");
		end if;
		T:=FreeAbelianGroup(0);
		f:=func< t | J!0>;
		return pointsJ, T, f;	
	end if;		
end function;

// returns true if we can express P as a linear combination of the 
// elements of S with coefficients in [-3..3]
//inSmallLinComb:=function(S,P);
//	r:=#S;
//	C:=CartesianPower([-3..3],r);
//	for c in C do
//		if P eq &+[Parent(P) | c[i]*S[i] : i in [1..r]] then
//			return true;
//		end if;
//	end for;
//	return false;
//end function;


// S1, S2 are lists of points on J
// with S1 linearly independent 
// attempts to produce a list of independent points whose span contains S1 and S2
// gives an error if the method fails
//reduce:=function(S1,S2);
//	for P in S2 do
//		if inSmallLinComb(S1,P) then
//			Exclude(~S2,P);
//		end if;
//	end for;
//	if #S2 eq 0 then
//		return S1;
//	end if;
//	for P in S2 do
//		S3:=Append(S1,P);
//		if independentModTorsion(S3) then
//			return $$(S3,Exclude(S2,P));
//		end if;
//	end for;
//	for P in S2 do
//		for Q in S1 do
//			S3:=Append(Exclude(S1,Q),P);
//			if independentModTorsion(S3) and inSmallLinComb(S3,Q) then
//				return $$(S3,Exclude(S2,P));
//			end if;
//		end for;
//	end for;
//	error("given up in reduce--needs to be programmed more cleverly!");
//end function;


// J is the Jacobian of a genus 2 curve defined by y^2=f(x)
// where f has degree 5 over a number field.
// determines upper bound r for the rank (via computing the 2-Selmer rank) 
// and an upper bound for the torsion subgroup via reduction at lots of primes
// and then searches for enough independent points on J
// to give basis for a subgroup of J(K) of rank r and finite index
// and enough torsion
// if successful will return
// basfree,T,f, ptsC
// where basfree is a basis for a subgroup of J of finite index
// T is isomorphic to the torsion subgroup of J(K)
// f:T->J(K) gives this isomorphism onto torsion
// ptsC is a set of $K$-rational points on C found.
// WARNING 1: THIS WILL NOT TERMINATE until enough independent points are found 
// which could be forever if SHA[2] is non-trivial, or a very long time
// if the generators are large
// WARNING 2: THIS WILL NOT TERMINATE if the bound for the torsion given
// by reduction at the lots of primes is not sharp
pseudoBasis:=function(J);
	C:=Curve(J);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	assert Degree(f) eq 5;
	T:=torsionSubgroupBound(J);
	print "it appears that the Torsion subgroup is isomorphic to", T;
	print "computing the 2-Selmer group";
	print "might take a very long time";
	S:=TwoSelmerGroup(J);
	r:=#Generators(S);
	print "2-Selmer rank is", r;
	T2,g:=TwoTorsionSubgroup(J);
	print "two torsion subgroup is", T2;
	r:=r-#Generators(T2);
	print "Hence rank is at most",r;	
	B:=0;
	pointsJ:=[g(t) : t in Generators(T2)];
	print "searching for enough torsion points and for", r, "independent points on J";
	print "this could take forever!";
	ptsC:=[];
	repeat
		B:=B+1;
		// first will get some points on J as differences of points on C
		pointsC:=searchC(C,2*B); // searching on C
		if #pointsC ge 1 then
			P:=pointsC[1];
			for i in [1..#pointsC] do
				Include(~pointsJ,J![pointsC[i],P]);
				Include(~pointsJ,J![pointsC[i],-P]);
				Include(~ptsC,pointsC[i]);
			end for;
		end if;
		for P in searchJ(J,B) do   //now searching on J
			Include(~pointsJ,P);
		end for;
		Exclude(~pointsJ,J!0);
		basfree,Tlb,f:=reduce(pointsJ);
		pointsJ:=basfree cat [f(t) : t in Generators(Tlb)];
	until (#basfree eq r) and IsIsomorphic(Tlb,T);
	print "found", r, "independent points on J and enough torsion";
	print "basis for torsion is", [f(t) : t in Generators(Tlb)];
	print "torsion subgroup isomorphic to", Tlb;
	print "basis for a free subgroup of finite index is", basfree;
	return basfree, Tlb, f, ptsC;
end function;


// given a curve of genus $2$ of the form $y^2=quintic$
// over a number field $K$ attempts to provably determine all rational points by
// (i) determine the 2-Selmer rank
// (ii) an upper bound for the torsion via reduction
// then search on the curve and the Kummer until it finds enough rational points
// to provably determine both the torsion subgroup and a subgroup of the 
// Mordell--Weil group of finite index. This part of the program might
// not terminate.
// Assuming the previous step is successful it searches for rational points
// on C and then applies Chabauty plus the Mordell--Weil sieve (Theorem 3 of the paper)
// to show that the points found are the only ones (this step can succeed or fail).
ratPointsC:=function(C);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	assert Degree(f) eq 5;
	inf:=PointsAtInfinity(C)[1];
	J:=Jacobian(C);
	basfree,T,phi,ptsC:=pseudoBasis(J);
	pointsC:=Include(ptsC,inf);
	if #basfree eq 0 then
		for t in T do
			D:=phi(t);
			if D ne J!0 then
				if Degree(D[1]) eq 1 then
					beta:=Roots(D[1])[1,1];
                                        alpha:=Evaluate(D[2],beta);
                                        Include(~pointsC,C![beta,alpha]);
                                end if;
			end if;
		end for;
		print "Mordell--Weil rank is 0 and we know the torsion";
		print "succeeded in showing that the only $K$-rational points are", pointsC;
		return pointsC;
	end if;
	r:=#basfree;
	cart:=CartesianPower([-3..3],r);
	// trying to look for some other rational points on the curve C
	// by taking linear combinations of the known points on the Jacobian
	for c in cart do
		D1:=&+[J | c[i]*basfree[i] : i in [1..r]];
		for t in T do
			D:=D1+phi(t);
			if D ne J!0 then
                		if Degree(D[1]) eq 1 then
                        		beta:=Roots(D[1])[1,1];
		        		alpha:=Evaluate(D[2],beta);
                        		Include(~pointsC,C![beta,alpha]);
				end if;
                	end if;
		end for;
        end for;
	print "it appears that a complete list of rational points on C is", pointsC;
	print "want to prove this using Chabauty and the Mordell--Weil sieve";
	ptCand:=[P: P in pointsC | IsWeierstrassPlace(Place(P)) eq false];
	if #ptCand eq 0 then
		error("failed to find a non-Weierstrass rational point on C--program
		needs rewriting to cope with this case");
	else
		pt0:=ptCand[1];
	end if;
	torsbas:=[f(T.i) : i in [1..#Generators(T)]];
	tf:=chabMW(pt0,pointsC,T,basfree,torsbas);	
	if tf then 
		print "succeeded in proving that the only K-rational points are", pointsC;
		return pointsC;
	else
		print "failed in provably determining the K-rational points on C";
		return [];
	end if;	
end function;

