
Attach("add.m");   
// needed for arithmetic on genus 2 Jacobians over P-adic fields


// from Michael Stoll

intrinsic JPttoCoords(pt::JacHypPt) -> SeqEnum
{ Given a point on the genus 2 Jacobian J, return the sequence of coordinates
  of its image on the model of J in P^15.}
  J := Parent(pt);
  C := Curve(J);
  require Genus(C) eq 2: "pt must be on the Jacobian of a genus 2 curve.";
  R := BaseField(C);
  f, h := HyperellipticPolynomials(C);
  require h eq 0: "The curve of pt must be of the form y^2 = f(x).";
  f2,f3,f4,f5,f6 := Explode([Coefficient(f, i) : i in [2..6]]);
  a := pt[1]; b := pt[2]; d := pt[3];
  if Degree(a) eq 2 then
    al1 := -Coefficient(a, 1); al2 := Coefficient(a, 0);
    b1 := Coefficient(b, 1); b2 := Coefficient(b, 0);
    a15 := al1^2 - 4*al2;
    a14 := 1;
    a13 := al1;
    a12 := al2;
    a11 := al1*al2;
    a10 := al2^2;
    a9 := b1;
    a8 := -b2;
    a7 := -(al2*b1 + al1*b2);
    a6 := al1*a7 + al2*b2;
    c := al1^2 - al2;
    a5 := b1^2 - (f6*c^2 + f5*al1*c + f4*al1^2 + f3*al1 + f2);
    a4 := -(b1*b2 + f6*al1*al2*c + f5*al1^2*al2 + f4*al1*al2 + f3*al2);
    a3 := al2*a5;
    a2 := a5*a9 - f3*a8 - 2*f4*a7 - 2*f5*a6 - 2*f6*a6*al1 - f5*a8*al2;
    a1 := a5*a8 - 2*f6*a6*al2 - f5*a7*al2;
    a0 := a5^2;
  elif Degree(a) eq 1 then
    s := Coefficient(b, 3);
    assert s^2 eq f6;
    u := -Coefficient(a, 0);
    v := Evaluate(b, u);
    a15 := 1; a14 := 0; a13 := 0; a12 := 0;
    a11 := u; a10 := u^2; a9 := s; a8 := s*u;
    a7 := s*u^2; a6 := s*u^3 - v; a5 := 0; a4 := s*a6;
    t := 2*s*a6 + f5*u^2;
    a3 := t*u; a2 := s*a3; 
    a1 := a7*(4*f6*u^3 + 3*f5*u^2 + 2*f4*u + f3) - u*v*(4*f6*u + f5);
    a0 := t^2;
  elif d eq 2 then // and Degree(a) eq 0
    s := Coefficient(b, 3);
    assert s ne 0 and s^2 eq f6;
    a15 := 0; a14 := 0; a13 := 0; a12 := 0;
    a11 := 0; a10 := 1; a9 := 0; a8 := 0;
    a7 := s; a6 := -f5/(2*s); a5 := 0; a4 := s*a6;
    a3 := a6^2 - f4; a2 := s*a3; a1 := a3*a6 - s*f3; a0 := a3^2;
  else // origin
    return [R | 1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
  end if;
  return [R | a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15];
end intrinsic;


// from Michael Stoll

intrinsic coordsToJPt(seq::SeqEnum,J::JacHyp) -> JacHypPt
	{Given a sequence of 16 coordinates for a point on the 
	projective embedding of J, gives the corresponding point on J}
	polring:=Parent(HyperellipticPolynomials(Curve(J)));
	if &and[seq[i] eq 0 : i in [2..16]] then
		assert seq[1] ne 0;
		return J!0;
	elif (seq[16] eq 0) and (seq[15] eq 0) then
		i:=seq[11]; 
		assert i ne 0;
		seq:=[j/i : j in seq];
		return elt<J | polring!1,polring![0,0,-seq[7],seq[8]],2>;
	elif seq[15] eq 0 then
		i:=seq[16];	
		seq:=[j/i: j in seq];
		// BEGINING OF MODIFIED CODE
		if seq[10] ne 0 then  
			// y^2=sextic case
			return elt<J|polring![-seq[12],1], polring![-seq[7],0,0,seq[10]],2>;
		else
			// y^2=quintic
			return elt<J|polring![-seq[12],1], polring![-seq[7]]>;
		end if;
		// END OF MODIFIED CODE
		// Michael's original code :
		// return J![polring![-seq[12],1], polring![-seq[7],seq[10]]]; 
	else
		i:=seq[15];
		seq:=[j/i: j in seq];
		return J![polring![seq[13],-seq[14],1],polring![-seq[9],seq[10]]];		
	end if;
end intrinsic;

intrinsic reduceModP(a::FldNumElt,P::RngOrdIdl,phi::Map) -> FldFinElt
	{  K is number field
	 P is a prime ideal of OK
	 phi:OK-> ResidueClassField
	 a in K has non-negative valuation at P (checked)
	 determines the image of a in ResidueClassField
	 (using Bang(K,k) does not seem to work!)
	}
	OK:=Integers(Parent(a));
	if a in OK then
		return (OK!a)@phi;
	end if;
	v:=Valuation(a*OK,P);
	assert v ge 0;
	if v gt 1 then
		return 0@phi;
	end if;
	d:=Denominator(a*OK);
	if Valuation(d*OK,P) eq 0 then
		return ((OK!(a*d))@phi)/(d@phi);
	else
		I:=&*[fac[1]^(-fac[2]) : fac in Factorisation(a*OK) | fac[2] lt 0];
		c:=ChineseRemainderTheorem(P,I,OK!1,OK!0);   // this makes things slow I think!
							// is there a way round it?
		return (OK!(c*a))@phi;
	end if;
end intrinsic;

intrinsic reduceModP(pt::PtHyp,P::RngOrdIdl,phi::Map) -> SeqEnum 
	{  
	 K is number field
	 P is a prime ideal of OK
	 phi:OK-> ResidueClassField
	 pt is a point on a genus 2 curve C/K
	 reduces the pt modulo P
	}
	x:=pt[1];y:=pt[2];z:=pt[3];
	OK:=Integers(Parent(x));
	m:=Min([3*Valuation(x*OK,P),Valuation(y*OK,P),3*Valuation(z*OK,P)]) div 3;
	piCand:=[g : g in Generators(P) | Valuation(g*OK,P) eq 1]; 
	pi:=piCand[1];  // uniformizer for P
	x:=x/pi^m;
	y:=y/pi^(3*m);
	z:=z/pi^m;
	return [reduceModP(x,P,phi),reduceModP(y,P,phi),reduceModP(z,P,phi)];
end intrinsic;


intrinsic reduceModP(J::JacHyp,bas::SeqEnum,P::RngOrdIdl)  -> JacHyp,SeqEnum
	{
	J: genus $2$ Jacobian over number field K,
	bas: a sequence of elements of J(K),
	P: prime ideal of K of good reduction,
	returns the corresponding Jacobian over the residue class field of P
	and the image of the elements in bas modulo P
	}
	assert IsPrime(P);
	k,phi:=ResidueClassField(P);
	C:=Curve(J);
	K:=BaseRing(J);
	OK:=Integers(K);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	assert &and [Valuation((OK!c)*OK,P) ge 0 : c in Coefficients(f)];
	assert Valuation(2*OK,P) eq 0;
	assert Valuation(Discriminant(C)*OK,P) eq 0;
	ky<y>:=PolynomialRing(k);
	fk:=ky![reduceModP(c,P,phi) : c in Coefficients(f)];
	Ck:=HyperellipticCurve(fk);
	Jk:=Jacobian(Ck);
	piCandidates:=[g : g in Generators(P) | Valuation(g*OK,P) eq 1];
	pi:=piCandidates[1]; // uniformizer for P
	bask:=[];
	for Q in bas do
		seq:=JPttoCoords(Q);
		m:=Min([Valuation(g*OK,P) : g in seq]);
		seq:=[g/pi^m : g in seq];
		seqk:=[reduceModP(g,P,phi) : g in seq];
		Append(~bask,coordsToJPt(seqk,Jk));
	end for;	
	return Jk,bask;
end intrinsic;



intrinsic torsionExponentBound(J::JacHyp) -> RngIntElt 
	{
	J :  genus 2 Jacobian over number field K
	returns a positive integer m such that m*P=0 for all torsion elements P in J.
	This is NOT necessarily the least such integer m, but is likely to be.
	}
	// we make use of the following result (stated for example
	// in N. Katz, "Galois properties of torsion points on abelian varieties",
	// Invent Math 62 (1981), 481--502):
	// if A is an abelian variety over a number field K
	// P a prime ideal of good reduction for A with residue field k, above rational prime p
	// such that e_P<p-1,
	// then Torsion(A(\Q))->A(k) is injective.
	K:=BaseRing(J);
	OK:=Integers(K);
	disc:=OK!(Discriminant(Curve(J)));
	expgcd:=0;
	l:=2;
	while l lt 50 do	
		l:=l+1;
		if IsPrime(l) then
			lFac:=[L[1] : L in Factorization(l*OK)];
			for P in lFac do
				if Valuation(disc*OK,P) eq 0 then
					e:=RamificationIndex(P);
					if e lt l-1 then 
						Jk:=reduceModP(J,[],P);
						A:=AbelianGroup(Jk);
						expgcd:=GCD(expgcd,LCM([Order(g) : g in Generators(A)]));
						if expgcd eq 1 then
							return 1;
						end if;
					end if;
				end if;
			end for;
		end if;
	end while;	
	return expgcd;
end intrinsic;

intrinsic torsionSubgroupBound(J::JacHyp) -> GrpAb 
	{
	J :  genus 2 Jacobian over number field K
	returns a finite abelian group which contains the torsion
	subgroup as an abstract group (and is likely to equal it)
	}
	// we make use of the following result (stated for example
	// in N. Katz, "Galois properties of torsion points on abelian varieties",
	// Invent Math 62 (1981), 481--502):
	// if A is an abelian variety over a number field K
	// P a prime ideal of good reduction for A with residue field k, above rational prime p
	// such that e_P<p-1,
	// then Torsion(A(\Q))->A(k) is injective.
	K:=BaseRing(J);
	OK:=Integers(K);
	disc:=OK!(Discriminant(Curve(J)));
	expgcd:=[0,0,0,0];
	l:=2;
	while l lt 50 do	
		l:=l+1;
		if IsPrime(l) then
			lFac:=[L[1] : L in Factorization(l*OK)];
			for P in lFac do
				if Valuation(disc*OK,P) eq 0 then
					e:=RamificationIndex(P);
					if e lt l-1 then 
						Jk:=reduceModP(J,[],P);
						A:=AbelianGroup(Jk);
						expP:=[Order(g) : g in Generators(A)];
						if #expP eq 1 then
							expP:=[1,1,1] cat expP;
						elif #expP eq 2 then
							expP:=[1,1] cat expP;
						elif #expP eq 3 then
							expP:=[1] cat expP;
						end if;
						expP:=Sort(expP);
						expgcd:=[GCD(expP[i],expgcd[i]) : i in [1..4]];
						if expgcd eq [1,1,1,1] then
							return FreeAbelianGroup(0);
						end if;
					end if;
				end if;
			end for;
		end if;
	end while;	
	A:=AbelianGroup<a,b,c,d | expgcd[1]*a,expgcd[2]*b,expgcd[3]*c,expgcd[4]*d>;
	return A;
end intrinsic;


intrinsic torsionSubgroup(J::JacHyp) -> GrpAb,UserProgram
	{
	J genus 2 Jacobian over number field K
	returns an abstract abelian group T
	and a function f:T -> J(K)
	so that f is an isomorphism of T onto the torsion subgroup of J(K)
	WARNINGS: 
		(1) THIS IS NOT GUARANTEED TO TERMINATE
		(2) IT IS STUPIDLY PROGRAMMED, SO WILL BE VERY SLOW 		
	Basic idea, bound torsion using reduction for lots of primes,
	obtain a group T which will contain a subgroup isomorphic to the torsion
	subgroup. Next search for points on the Kummer and lift to the Jacobian
	until we find #T torsion points. Then constructing f is easy. The slow
	part is searching on the Kummer. The fact that we don't know that T is
	isomorphic to the torsion subgroup means that the program might not terminate.
	}
	T:=torsionSubgroupBound(J);
	m:=Exponent(T);
	torspts:={};
	A,phi:=TwoTorsionSubgroup(J);
	torspts:={phi(a) : a in A};
	K:=BaseField(J);
        OK:=Integers(K);
	d:=Degree(K);
        bas:=Basis(OK);
        KS:=KummerSurface(J);
        E:=KS`Equation; // will search for torsion points by doing a search on
			// the Kummer surface
	B:=0;
	while #torspts ne #T do	
		B:=B+1;
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
        	pointsJ:=[J!0];
        	for P in pointsKS do
			QP:=Points(J,P);
			if #QP ge 1 then
				Append(~pointsJ,Random(QP));  // we only want one point 
								// up to sign
                	//pointsJ:=pointsJ cat [Q : Q in Points(J,P)];
			end if;
        	end for;
		torspts1:={Q-P : Q,P in pointsJ | m*(Q-P) eq J!0};
		torspts2:={Q+P : Q,P  in pointsJ | m*(Q+P) eq J!0};
		torspts:=torspts join torspts1 join torspts2;
		for Q in torspts do
			for i in [1..(m-1)] do
				Include(~torspts,i*Q);
			end for;
		end for;		
	end while;
	r:=#Generators(T);
	gens:=[J!0 : i in [1..r]];
	i:=r;
	while i ge 1 do
		ord:=Order(T.i);
		divs:=[d : d in Divisors(ord) | d ne ord];
		cands:={P : P in torspts | ord*P eq J!0};
		notcands:=&join[{P : P in cands | d*P eq J!0} : d in divs];
		cands:=cands diff notcands;
		// now cands will contain elements of order precisely ord
		P:=Random(cands);
		gens[i]:=P;
		torspts:=torspts diff {j*P : j in [1..ord]};	
		i:=i-1;
	end while;
	phi:=func<t | &+[J | Eltseq(t)[i]*gens[i] : i in [1..r]] >;
	return T, phi;
end intrinsic;










intrinsic independentModTorsion(bas::SeqEnum) -> BoolElt
	{
	bas : a sequence of points on a genus 2 Jacobian
		J over a number field K, 
	tries to prove that the points are 
	independent in J(K)/Torsion. Returns true if it is successful
	in proving this, false otherwise.
	}
	J:=Parent(bas[1]);
	m:=torsionExponentBound(J);   // this kills the torsion subgroup
	divm:=Set(PrimeDivisors(m));
	K:=BaseRing(J);
	OK:=Integers(K);
	disc:=OK!(Discriminant(Curve(J)));
	A:=FreeAbelianGroup(#bas);
	S:=A; 
	// S will always contain the kernel of A->J(Q)
	// It will be enough to show that S is contained in pA for some prime p
	// not dividing m
	l:=2;
	while l lt 50 do   // how many attempts before giving up? 
			// I didn't think about it.	
		l:=l+1;
		if IsPrime(l) then
			lFac:=[L[1] : L in Factorization(l*OK)];
			for P in lFac do
				if Valuation(disc*OK,P) eq 0 then
					Jk,bask:=reduceModP(J,bas,P);  
					B,psi:=AbelianGroup(Jk);
					bask:=[b@@psi : b in bask];
					phi:=hom<A->B | bask >;	
					S:=S meet Kernel(phi);
					S:=sub<A | [A!g : g in Generators(S)]>;
					M:=GCD([GCD(Eltseq(A!g)) : g in Generators(S)]);	
					// S \subset M.A
					if not(Set(PrimeDivisors(M)) subset divm) then
						return true;
					end if;
				end if;
			end for;
		end if;
	end while;
	return false;				
end intrinsic;


// Jk Jacobian of a hyperelliptic curve over a finite field
// returns tf,B,phi
// where if tf is true, B is an abstract abelian group 
// isomorphic to Jk
// and phi:B->Jk is the isomorphism
// if tf is false, then the calculation failed.
 
abelianGroup:=function(Jk);
	try
		B,phi:=AbelianGroup(Jk);
		return true,B,phi;
	catch e
		print "caught error";
		return false,0,0;
	end try;
end function;

// check saturation


intrinsic isSaturatedAtp(A::GrpAb,bas::SeqEnum,p::RngIntElt) -> BoolElt
	{
	J genus 2 Jacobian over number field K
	bas is a sequence of elements of J(K)
	A is an Abelian Group with #bas generators so that A--> J(K)
	mapping A.i to bas[i] gives a well-defined hm
	p prime number
	returns true if it verifies that the image of A is p-saturated
	}
	pA:=sub<A | [p*g : g in Generators(A)]>;
	Amodp,pi:=quo<A|pA>;
	lim:=4*#Generators(Amodp); // that many auxilliary primes we will try
	M:=Amodp;
	J:=Parent(bas[1]);
	K:=BaseRing(J);
	OK:=Integers(K);
	disc:=OK!(Discriminant(Curve(J)));
	relNo:=0;  // number of relations
	l:=2;
	while relNo lt lim do	
		l:=l+1;
		if IsPrime(l) then
			lFac:=[L[1] : L in Factorization(l*OK)];
			for P in lFac do
				if (Valuation(disc*OK,P) eq 0) and (Degree(P) eq 1 or Norm(P) le 10^5) then
					Jk,bask:=reduceModP(J,bas,P);
					tf,B,psi:=abelianGroup(Jk);
					if tf then
					if IsDivisibleBy(#B,p) then
						relNo:=relNo+1;
						pB:=sub<B | [p*g : g in Generators(B)]>;
						Bmodp,mu:=quo<B|pB>;
						eps:=hom<A->Bmodp | [ (P@@psi)@mu : P in bask ]>;
						delta:=hom<M->Bmodp | x:->((Amodp!x)@@pi)@eps>;
						M:=Kernel(delta);
						M:=sub<Amodp | [Amodp!g : g in Generators(M)]>;	
						if #M eq 1 then
							return true;
						end if;
					end if;
					end if;
				end if;
			end for;
		end if;
	end while;	
	return false;
end intrinsic;



intrinsic reductionInfo(pt0::PtHyp,A::GrpAb,bas::SeqEnum,lRange::SeqEnum,smoothBase::SetEnum) -> SeqEnum 
	{
	this function gives useful information needed for the Mordell--Weil sieve
	pt0: is a point on genus 2 curve C over a number field K
		with Jacobian J 
	bas: is a sequence of elements of J(K)
	A: is an Abelian Group with #bas generators so that A--> J(K)
	   mapping A.i to bas[i] gives a well-defined hm
	lRange: a sequence of integers
	smoothBase: a set of primes $p$ such that the subgroup of J(K)
	   given by bas is p-saturated (not checked here)
	returns a sequence of quadruples [* P, B, psi, imC *] such that
	P :  is a prime of good reduction,
		with residue class k such that the prime divisors of #J(k) 
		are in smoothBase
	B :  abstract abelian group isomorphic to J(k)
	psi : homomorphism A --> B obtained by composing A-->J(K)-->J(k)-->B
	imC : the intersection of the image of psi with the image of 
		C(k)-->J(k)-->B
	      given by pt:->pt-pt0 	
	}
	J:=Parent(bas[1]);
	K:=BaseRing(J);
	OK:=Integers(K);
	C:=Curve(J);
	disc:=OK!Discriminant(C);
	res:=[Parent([* *]) | ];
	lRange:=[l : l in lRange | IsOdd(l) and IsPrime(l)];
	for l in lRange do
		Pset:=[fac[1] : fac in Factorization(l*OK) | 
			Valuation(disc*OK,fac[1]) eq 0 and 
		((Norm(fac[1]) lt 200) or (Norm(fac[1]) lt 10^4 and Degree(fac[1]) eq 1))];
						// second condition used to be 10^5
						// third condition wasn't there
						// but for now it speeds things up
		for P in Pset do
			k,pi:=ResidueClassField(P);
			Jk,bask:=reduceModP(J,bas,P);
			tf,B,phi:=abelianGroup(Jk);
			if tf then
				if Set(PrimeDivisors(#B)) subset smoothBase then
					psi:=hom<A->B | [g@@phi : g in bask]>;
					imA:=Image(psi);
					Ck:=Curve(Jk);
					ptk0:=Ck!reduceModP(pt0,P,pi);
					imC:=[(pt-ptk0)@@phi : pt in RationalPoints(Ck)];
					imC:=[ Eltseq(c) : c in imC | c in imA];	
					//redP:=func<pt | ((Ck!reduceModP(pt,P,pi))-ptk0)@@phi>;
					Append(~res,[* P, B, psi, imC *]);
					print Norm(P),#B,#imC;
				end if;
			end if;
		end for;
	end for;
	maxC:=func<sI1,sI2 | #sI1[4] - #sI2[4]>;
	maxB:=func<sI1,sI2 | Max(PrimeDivisors(#sI1[2])) - Max(PrimeDivisors(#sI2[2]))>;
	print "sorting sieving information";
	Sort(~res, maxC);
	Sort(~res, maxB);  // put quintuples with B divisible only by small primes first
	return res;	
end intrinsic; 


project:=function(A,W,L,targetNum,targetMod);
	G:=GCD([GCD(Eltseq(A!g)) : g in Generators(L)]);
	if IsDivisibleBy(G,targetMod) then
		reduce:=func<w,M | [a mod M : a in w]>;
		WMod:={reduce(Eltseq(A!w),targetMod) : w in W};
		return #WMod eq targetNum;
	else
		return false;
	end if;
end function;

intrinsic MWSieve(pt0::PtHyp,A::GrpAb,bas::SeqEnum,targetNum::RngIntElt, targetMod::RngIntElt) -> SeqEnum,GrpAb,SeqEnum
	{
	Mordell-Weil sieve
	pt0 : is a point on genus 2 curve C over a number field K
		with Jacobian J 
	bas : is a sequence of elements of J(K)
	A abstract group such that A-->J(K) mapping A.i to bas[i] is an isomorphism,
	returns W, L, sieveInf
	where L is a (hopefully) smaller subgroup of A 
	and W is a sequence of elements of A such that C(K) maps into W+L
	under C(K) -> J(K) -> A where the first map is the Abel-Jacobi map associated with pt0.
	and sieveInf is the result of reductionInfo
	}
	L:=A;
	W:=[A!0];
	J:=Parent(bas[1]);
	K:=BaseRing(J);
	OK:=Integers(K);
	C:=Curve(J);
	disc:=OK!Discriminant(C);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	smoothBase:=[];
	for p in PrimesInInterval(1,75) do
                if isSaturatedAtp(A,bas,p) then
                        print "verified saturation at", p;
                        Append(~smoothBase,p);
                else
                        print "haven't verified saturation at", p;
                        print "will simply not include", p, "in smoothBase";
                end if;
        end for;
	print "getting sieving information";
	sieveInf:=reductionInfo(pt0,A,bas,[3..1200],Set(smoothBase));
					// 1200 was 3500 before
	//Sort(~sieveInf,  func<y,x| #y[4]/#y[2] - #x[4]/#x[2]>);
	//maxB:=func<sI1,sI2 | Max(PrimeDivisors(#sI1[2])) - Max(PrimeDivisors(#sI2[2]))>;
	//print "sorting sieving information";
	//Sort(~sieveInf, maxB);
	placeCount:=0;
	print "Mordell--Weil sieve";
	for sI in sieveInf do
		P,B,psi,imC:=Explode(sI);
		Lnew:=Kernel(psi) meet L;
		Lnew:=sub<A | [A!l : l in Generators(Lnew)]>;
		Q,pi:=quo<L|Lnew>;
		Qreps:=[A!(q@@pi) : q in Q]; 
		W:=[w+q : w in W, q in Qreps | Eltseq((w+q)@psi) in imC];
		L:=Lnew;
		//print #W, Index(A,L);
		//if (#W eq target) and (Index(A,L) gt 10^30) then
		placeCount:=placeCount+1;
		//G:=GCD([GCD(Eltseq(A!g)) : g in Generators(L)]);
		if project(A,W,L,targetNum,targetMod) and (#W le (targetNum+10)) then 	
		//if G gt 10^20 and (#W le (targetNum+10)) then
			print "used", placeCount, "places for the Mordell--Weil sieve";
			return W,L, sieveInf;
		end if;
	end for;
	print "used", placeCount, "places for the Mordell--Weil sieve"; 
	return W, L, sieveInf;
end intrinsic;


intrinsic integrals(D::JacHypPt,P::RngOrdIdl,pt0::PtHyp,prec::RngIntElt) -> SeqEnum 
	{
		Evaluate \int_D dx/y and \int_D xdx/y  in K_P
		C curve of genus 2 over number field K
		D in J(K)
		pt0 is in C(K) 
		prec is the $p$-adic precision where p is the prime below P
		we use pt0 as our base for integration
		for now, pt0 must be a non-Weierstrass affine point
		with x-coordinate 0 which reduces to a non-Weierstrass affine point
	}	
	if IsWeierstrassPlace(Place(pt0)) then
		error("not programmed yet");
	end if;
	J:=Parent(D);
	C:=Curve(J);
	K:=BaseField(C);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	assert &and[Valuation(c,P) ge 0 : c in Coefficients(f)];
	assert (Valuation(pt0[1],P) ge 0) and (Valuation(pt0[2],P) ge 0);
	Kx<x>:=Parent(f);
	k,phi:=ResidueClassField(P);
	Jk,bask:=reduceModP(J,[D],P);
	Dk:=bask[1];
	Ck:=Curve(Jk);
	ptk0:=Ck!reduceModP(pt0,P,phi);
	if IsWeierstrassPlace(Place(ptk0)) then
		error("not programmed yet");
	end if;
	// thus x-pt0[1] is a uniformizor at pt0 and its reduction ptk0 and regular in the whole residue class
	ord:=Order(Dk);		
	nprec:=prec+Valuation(ord,Characteristic(k));   // we will have to divide the integral later
					// by this order, so we need to increase the precision
	//
	// now want to compute 2*pt0-(divisor at infinity)
	beta:=pt0[1];
	alpha:=pt0[2];
	fdb:=Evaluate(Derivative(f),beta)/(2*alpha);
	Dpt0:=elt<J|(x-beta)^2,fdb*x+alpha-fdb*beta,2>;  // 2*pt0-(divisor at infinity)
	//
	// now we want to calculate the necessary P-adic precision
	e:=RamificationIndex(P);
	p:=Characteristic(k); // prime below P
	Pprec:=e*nprec; // for now P-adic precision instead of p-adic precision
	//
	//R:=ord*D+Dpt0;
	R,h,hx:=preIntLocal(D,Dpt0,ord,P,Pprec);
			// now R is congruent modulo P^Pprec to the divisor represented by 
			//	R_1+R_2-div_\infty
			// what matters to us is R_1+R_2-2pt0 is in the kernel of reduction
			// and	\int_D=1/ord \int_{R_1+R_2-2pt0}
			// moreover since pt0 does not reduce to a Weierstrass point,
			// R_1 and R_2 both reduce to pt0 modulo P
	u:=R[1];
	assert Degree(u) eq 2;
	c1,c2,c3:=Explode(Coefficients(u));
	assert c3@@h eq 1;
	assert Valuation(c2+2*beta@h) gt 0;
	assert Valuation(c1-(beta@h)^2) gt 0;
	assert Valuation(Evaluate(R[2],beta@h)-alpha@h) gt 0;
	//assert reduceModP(c2+2*beta,P,phi) eq 0;
	//assert reduceModP(c1-beta^2,P,phi) eq 0;
	//
	// then Valuation((x(R_1)-beta)^n+(x(R_2)-beta)^n,P)  \ge Ceiling(n/2) for all n \ge 0
	// where beta is the x-coordinate of pt0
	//
	noOfTerms:=Max(2*Pprec,Ceiling(2*e/Log(p)));
	while ((noOfTerms/2-e*Log(noOfTerms)/Log(p)) lt prec) do
		noOfTerms:=noOfTerms+1;
	end while;  // will give us how many terms in the powerseries we need
	KPx<x>:=Parent(u);
	A,psi:=quo<KPx|[u]>;
	sym:=func<n|Trace(psi((x-beta@h)^n))>;
	Kz<z>:=PowerSeriesRing(K : Precision:=(noOfTerms+1));  // z will be the same as x-beta
	alpha:=pt0[2];
	y:=alpha*(Kz!(Evaluate(f,z+beta)/alpha^2))^(1/2);
	omega1:=1/y; // dx/y
	omega2:=(z+beta)/y; // xdx/y
	//L,h:=Completion(K,P: Precision:=e*prec);
	int1:=&+[(Coefficient(omega1,i-1)/(i*ord))@h*sym(i) : i in [1..noOfTerms]]; // +L!0;
	int2:=&+[(Coefficient(omega2,i-1)/(i*ord))@h*sym(i) : i in [1..noOfTerms]];  //+L!0;
	return [int1,int2];
end intrinsic;

function integrationMatrixP(bas,P,pt0,prec)  
	assert IsUnramified(P);  
	ints:=[* integrals(D,P,pt0,prec) : D in bas *];
	print "the integrals of the basis with place P are", ints;
	assert Valuation(Parent(ints[1,1]).1) eq 0;  
	mat1:=[Eltseq(pair[1]) : pair in ints];
	mat1:=Transpose(Matrix(mat1));
	mat2:=[Eltseq(pair[2]): pair in ints];
	mat2:=Transpose(Matrix(mat2));
	return VerticalJoin(mat1,mat2); 
end function;

intrinsic integrationMatrix(bas::SeqEnum,p::RngIntElt,pt0::PtHyp,prec::RngIntElt) -> AlgMatElt 
	{
	}
	assert IsPrime(p);
	K:=BaseRing(Parent(bas[1]));
	OK:=Integers(K);
	assert IsUnramified(p,OK);
	primes:=[fact[1] : fact in Factorization(p*OK)];
	flag:=false;
	for P in primes do
		matP:=integrationMatrixP(bas,P,pt0,prec);
		if flag eq false then
			mat:=matP;
			flag:=true;
		else
			mat:=VerticalJoin(mat,matP);
		end if;
	end for;
	return mat;
end intrinsic;


// given a matrix M with entries in a local field, 
// returns M',E 
// (i) where M' is upper triangular
// (ii) M'=E*M
// (iii) the entries of E are integers of the local ring

upperTriangular:=function(M);
	m:=NumberOfRows(M);
	n:=NumberOfColumns(M);
	Qp:=Parent(M[1,1]);
	I:=IdentityMatrix(Qp,m);
	E:=I;
	for j in [1..(Minimum(m,n))] do
		_,i:=Minimum([Valuation(M[k,j]) : k in [j..m]]);
		i:=i+(j-1);
		SwapRows(~M,i,j);
		E:=SwapRows(I,i,j)*E;
		for k in [(j+1)..m] do
			h:=M[k,j]/M[j,j];
			if AbsolutePrecision(h) le 1 then
				error("too much loss of precision");
			end if;
			AddRow(~M,-h,j,k);
			E:=AddRow(I,-h,j,k)*E;
		end for;
	end for;	
	return M,E;
end function;



intrinsic leadingTerms(pt::PtHyp,P::RngOrdIdl) -> SeqEnum
	{
	leading terms of the expansions for dx/y and xdx/y
	in terms of a well-behaved uniformizer of pt, and pt mod P
	}
	C:=Curve(pt);
	K:=BaseRing(C);
	OK:=MaximalOrder(K);
	f,h:=HyperellipticPolynomials(C);
	//assert IsMonic(f);
	//assert Valuation(LeadingCoefficient(f)*OK,P) eq 0;
	assert h eq 0;
	assert &and [Valuation(c*OK,P) ge 0 : c in Coefficients(f)];
	assert Valuation(2*OK,P) eq 0;
	assert Valuation(Discriminant(C)*OK,P) eq 0;
	F<x,y>:=FunctionField(C);	
	k,phi:=ResidueClassField(P);	
	ky:=PolynomialRing(k);
        fk:=ky![reduceModP(c,P,phi) : c in Coefficients(f)];
        Ck:=HyperellipticCurve(fk);  // the curve C modulo P
	Fk<xt,yt>:=FunctionField(Ck);
	ptt:=Ck!reduceModP(pt,P,phi);
	// now want to choose a "good uniformizer" u
	// throughout, ut will denote the reduction of u on Ck
	if pt[3] eq 0 then
		// point pt is at infinity
		assert pt[1] eq 1;
		if Degree(f) eq 5 then
			u:=y/x^3;
			ut:=yt/xt^3;
		else
			beta:=pt[2];
			assert beta^2 eq LeadingCoefficient(f);
			if Valuation(beta*OK,P) eq 0 then
				u:=1/x;
				ut:=1/xt;
			elif Valuation(beta*OK,P) gt 0 then
				u:=y/x^3-beta;
				ut:=yt/xt^3;
			else
				error("should not arrive here as the coeffs have non-neg valuation");
			end if;
		end if;
	else		
		// point pt belong to affine part	
		assert pt[3] eq 1;
		alpha:=pt[1];
		beta:=pt[2];
		if Valuation(beta*OK,P) eq 0 then
			// pt is not a Weierstrass point
			// nor reduces to one
			u:=x-alpha;
			ut:=xt-ptt[1];
		elif Valuation(beta*OK,P) gt 0 then
			// pt reduces to Weierstrass point
			u:=y-beta;
			ut:=yt;
		elif Valuation(beta*OK) gt 3*Valuation(alpha*OK) then
			// pt reduces to the point at infinity
			// which is Weierstrass
			assert ptt eq PointsAtInfinity(Ck)[1];
			u:=y/x^3-beta/alpha^3;
			ut:=yt/xt^3;
		else
			// pt reduces infinity not Weierstrass
			u:=1/x-1/alpha;	
			ut:=1/xt;
		end if;
	end if;
	pl:=Place(pt);
	plt:=Place(ptt);
	assert Valuation(u,pl) eq 1;
	assert Valuation(ut,plt) eq 1; // check that we have chosen u correctly!
	dx:=Differential(x);
	diff1:=dx/y;
	diff2:=x*dx/y;
	return [Residue(diff1/u,pl),Residue(diff2/u,pl)];
end intrinsic;

intrinsic leadingTerms(pt::PtHyp,p::RngIntElt,prec::RngIntElt) -> SeqEnum
	{
	pt is a point on C over number field K
	p rational prime
	prec positive integer
	constructs a matrix over the \Q_p to precision prec
	of dimension 2d \times d where d is the degree of K
	}
	assert IsPrime(p);
	K:=BaseRing(Curve(pt));
	d:=Degree(K);
	OK:=Integers(K);
	assert IsUnramified(p,OK);
	primes:=[fact[1] : fact in Factorization(p*OK)];
	flag:=false;
	for P in primes do
		KP,h:=Completion(K,P:Precision:=prec);
		dP:=Degree(KP);
		mu:=KP.1;
		assert Valuation(mu) eq 0;
		lT:=leadingTerms(pt,P);
		alpha1:=lT[1];
		alpha2:=lT[2];
		matP1:=Transpose(Matrix([Eltseq(h(alpha1)*mu^(i-1)) : i in [1..dP]]));
		matP2:=Transpose(Matrix([Eltseq(h(alpha2)*mu^(i-1)) : i in [1..dP]]));
		matP:=VerticalJoin(matP1,matP2);
		if flag eq false then
			Qp:=BaseRing(matP);
			if d eq dP then
				mat:=matP;
			else
				mat:=HorizontalJoin(matP,ZeroMatrix(Qp,2*dP,d-dP));
			end if;
			flag:=true;
			dTot:=dP;
		else
			matP:=HorizontalJoin(ZeroMatrix(Qp,2*dP,dTot),matP);
			dTot:=dTot+dP;
			if dTot lt d then
				matP:=HorizontalJoin(matP,ZeroMatrix(Qp,2*dP,d-dTot));	
			end if;
			mat:=VerticalJoin(mat,matP);
		end if;
	end for;
	return mat;
end intrinsic;

// reduce the pAdic precision for the entries of a matrix
// used for display purposes only
truncMat:=function(M,p,v);
	R:=pAdicField(p,v);
	r:=NumberOfRows(M);
	s:=NumberOfColumns(M);
	return Transpose(Matrix([[R!(M[i,j]): i in [1..r]]: j in [1..s]]));
end function;

intrinsic chabauty(bas::SeqEnum,ptList::SeqEnum,pt0::PtHyp,p::RngIntElt)->SeqEnum
	{
		C is a genus two curve of the form y^2=quintic over
		    number field K
		bas is a basis for the free part of J(K), or at least
		  a basis for something of finite index in the free part of J(K)
		  where the index is not divisible by p
		ptList is a list of K-rational points on C 
		pt0 is a fixed non-Weierstrass point in C(K),
		  which does not reduce to a Weierstrass point modulo any ideal above p
		  (pt0 is used as a basis for integration)
		p is a rational prime

		returns a sequences whose ith term is true or false depending on
		whether our Chabauty criterion succeeds or fails for ith point in
		ptList. If the ith entry is true, then the ith point is the unique
		rational point in its residue class mod p. If false, then there
		might be another rational point in the residue class.
	}
	assert IsPrime(p);
	if IsWeierstrassPlace(Place(pt0)) then
		error("for now, pt0 must be a non-Weierstras point");
	end if;
	C:=Curve(pt0);
	K:=BaseRing(C);
	//assert IsNumberField(K) and IsAbsoluteField(K);
	r:=#bas;
	d:=Degree(K);
	if r ge 2*d then
		error("rank must be less than 2*Degree(K)");
	end if;
	disc:=Discriminant(C);
	if IsDivisibleBy(Integers()!Norm(2*disc),p) then
		return [false : i in [1..#ptList]];
	end if;	
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	//assert IsMonic(f);
	assert Degree(f) eq 5;
	OK:=Integers(K);
	pDiv:=[fact[1] : fact in Factorisation(p*OK)];		
	for P in pDiv do
		for c in Coefficients(f) do
			if Valuation(c,P) lt 0 then
				return [false : i in [1..#ptList]];
			end if;	
		end for;
	end for;
	if IsRamified(p,OK) then
		return [false : i in [1..#ptList]];
	end if;
	M:=integrationMatrix(bas,p,pt0,5);	
	print "the integration matrix is", truncMat(M,p,3);
	_,E:=upperTriangular(M);
	print "the matrix E is", truncMat(E,p,3);
	tfreturn:=[];
	Fp:=GF(p);
	for pt in ptList do
		print "point", pt;
		Npt:=leadingTerms(pt,p,5);
		print "the leading terms matrix is", truncMat(Npt,p,3);
		ENpt:=E*Npt;
		print "E*Npt=", truncMat(ENpt,p,3);
		redSubMat:=Matrix([[Fp!(Integers()!ENpt[i,j]) : j in [1..d]] : i in [(r+1)..(2*d)]]);		
		print "redSubMat=", redSubMat;
		Append(~tfreturn,(Rank(redSubMat) eq d));
	end for;
	return tfreturn;
end intrinsic;


// ptJ is a point on Jacobian/number field J(K)
// basfree is a basis for a subgroup of full rank of J(K)
// T is an abstract abelian group isomorphic to the torsion subgroup of J(K)
// torsbas is such that T.i :-> torsbas[i] gives an isomorphism T->Torsion(J(K))
// returns [c1,..,cr],t such that c1*basfree[1]+...+cr*basfree[r]+(image of t)=ptJ
// if it fails to find suitable ci and t it gives an error 

expressLC:=function(ptJ,basfree,T,torsbas);
	J:=Parent((basfree cat torsbas)[1]);
	s:=#torsbas;
	r:=#basfree;
	for R in [1..10] do
		C:=CartesianPower([-R..R],r);
		for t in T do
			tpt:=&+[J | Eltseq[i]*torsbas[i] : i in [1..s]];
			for c in C do
				if ptJ eq (tpt+ (&+[J | c[i]*basfree[i] : i in [1..r]])) then
					return [c[i] : i in [1..r]],t;
				end if;
			end for;	
		end for;
	end for;
	error "expressLC failed";		
end function;

intrinsic chabMW(pt0::PtHyp,ptList::SeqEnum,T::GrpAb,basfree::SeqEnum,torsbas::SeqEnum) -> GrpAb,SeqEnum
	{
	Chabauty+Mordell-Weil sieve (Theorem 3 of paper)
	
		C is a genus two curve of the form y^2=quintic over
		    number field K
		
		pt0 is a fixed non-Weierstrass point in C(K),
		  (pt0 is used as a base for integration and the Abel-Jacobi map)
		
		basfree is a basis for the free part of J(K), or at least
		  a basis for something of finite index in the free part of J(K)
	
		torsbas is a basis for the torsion subgroup of J(K)
		
		ptList is a list of the known K-rational points on C 

		T an abstract group such that T-->J(K) mapping T.i to torsbas[i] 
		  is an isomorphism onto the torsion subgroup,
	}
	J:=Parent(basfree[1]);
	K:=BaseRing(J);
	OK:=Integers(K);
	C:=Curve(J);
	r1:=#basfree;
	A1:=FreeAbelianGroup(r1);
	phi1:=func<a | &+[J | Eltseq(a)[i]*basfree[i] : i in [1..r1] ]>;
	r2:=#torsbas;
	phi2:=func<a | &+[J | Eltseq(a)[i]*torsbas[i] : i in [1..r2] ]>;
	A,u,v,m,n:=DirectSum(A1,T);
	r:=#Generators(A);
	bas:=[ phi1(m(A.i)) + phi2(n(A.i)) : i in [1..r]];
	// now A is an abstract Abelian group
	// map A -> J(K) given by A.i:->bas[i] gives an injection 
	print "working with a subgroup A of the Mordell--Weil group isomorphic to ",A;
	print "the basis for this subgroup is", bas;
	ptsJ:=[pt-pt0 : pt in ptList];
	imRat:=[ ];  
	for qt in ptsJ do 
		c,t:=expressLC(qt,basfree,T,torsbas);	
		Append(~imRat,u(A1!c)+v(t));
	end for;  // now imRat is the image of known rational points in A 
	// under C(K) -> J(K) -> A where the first map is pt :-> pt-pt0
	print "using", pt0, "as base point for Abel-Jacobi map";
	print "the image of the known rational points on C in A is", imRat;
	targetNum:=#ptsJ;
	targetMod:=2^3*3^2*5*7*11;
	print "applying the Mordell--Weil sieve";
	W,L,sieveInf:=MWSieve(pt0,A,bas,targetNum,targetMod);
	print "after the Mordell--Weil sieve W=", W;
	print "and L=", L;
	print "the index of L in A is", Index(A,L); 
	pCands:=[]; // these will be rational primes used for Chabauty	
	PCands:={q[1] : q in sieveInf}; //
	primeBelow:=func<P | Factorisation(Norm(P))[1,1]>;
        primesAbove:=func<p | {s[1] : s in Factorisation(p*OK)}>;
	aboveInSet:=func<p,S | primesAbove(p) subset Set(S)>;
	for p in PrimesInInterval(3,200) do
		if aboveInSet(p,PCands) then
			sIp:=[* sI : sI in sieveInf | sI[1] in primesAbove(p) *];
			Kp:=A;
			for sI in sIp do
				P,B,psi,imC:=Explode(sI);
				Kp:=Kernel(psi) meet Kp;
				Kp:=sub<A | [A!l : l in Generators(Kp)]>;
			end for;	
			if &and[l in Kp : l in Generators(L)] then
				print "using prime p=",p,"for Chabauty";
				print "there are", #sIp, "places above", p;
				print "the structures of J(k_v) above these places are";
				for sI in sIp do
					print sI[2];
				end for;
				chab:=chabauty(basfree,ptList,pt0,p);
				print "having applied Chabauty to the points", ptList;
				print "Chabauty is respectively successful at", chab;
				for i in [1..#chab] do
					if chab[i] then
						Q:=imRat[i];
						for w in W do
							if (Q-w) in Kp then
								Exclude(~W,w);
							end if;
						end for;				
					end if;
				end for;
				print "after applying Chabauty with prime", p;
				print "W has", #W, "elements";
				if #W eq 0 then
					return true;
				end if;
			end if;
		end if;	
	end for;
	return false;
end intrinsic;


intrinsic chabMWOld(pt0::PtHyp,ptList::SeqEnum,T::GrpAb,basfree::SeqEnum,torsbas::SeqEnum) -> GrpAb,SeqEnum
	{
	Chabauty+Mordell-Weil sieve (Theorem 3 of paper)
	
		C is a genus two curve of the form y^2=quintic over
		    number field K
		
		pt0 is a fixed non-Weierstrass point in C(K),
		  (pt0 is used as a base for integration and the Abel-Jacobi map)
		
		basfree is a basis for the free part of J(K), or at least
		  a basis for something of finite index in the free part of J(K)
	
		torsbas is a basis for the torsion subgroup of J(K)
		
		ptList is a list of the known K-rational points on C 

		T an abstract group such that T-->J(K) mapping T.i to torsbas[i] 
		  is an isomorphism onto the torsion subgroup,
	}
	J:=Parent(basfree[1]);
	K:=BaseRing(J);
	OK:=Integers(K);
	C:=Curve(J);
	r1:=#basfree;
	A1:=FreeAbelianGroup(r1);
	phi1:=func<a | &+[J | Eltseq(a)[i]*basfree[i] : i in [1..r1] ]>;
	r2:=#torsbas;
	phi2:=func<a | &+[J | Eltseq(a)[i]*torsbas[i] : i in [1..r2] ]>;
	A,u,v,m,n:=DirectSum(A1,T);
	r:=#Generators(A);
	bas:=[ phi1(m(A.i)) + phi2(n(A.i)) : i in [1..r]];
	// now A is an abstract Abelian group
	// map A -> J(K) given by A.i:->bas[i] gives an injection 
	ptsJ:=[pt-pt0 : pt in ptList];
	imRat:=[ ];  // image of known rational points under C(K) -> J(K) -> A where the first map is pt :-> pt-pt0 
	for qt in ptsJ do 
		c,t:=expressLC(qt,basfree,T,torsbas);	
		Append(~imRat,u(A1!c)+v(t));
	end for;  // image of known rational points under C(K) -> J(K) -> A where the first map is pt :-> pt-pt0
	print imRat;
	L:=A;
	W:=[A!0];
	disc:=OK!Discriminant(C);
	f,h:=HyperellipticPolynomials(C);
	assert h eq 0;
	smoothBase:=[];
	for p in PrimesInInterval(1,75) do
		if isSaturatedAtp(A,bas,p) then
			print "verified saturation at", p;
			Append(~smoothBase,p);
		else
			print "haven't verified saturation at", p;
			print "will simply not include", p, "in smoothBase";
		end if;
	end for;
	print "getting sieving information";
	sieveInf:=reductionInfo(pt0,A,bas,[3..1000],Set(smoothBase));
	Pset:=[];  // will contain the list of prime ideals P used in MW sieve
	pCands:=[]; // these will be rational primes used for Chabauty	
	primeBelow:=func<P | Factorisation(Norm(P))[1,1]>;
	primesAbove:=func<p | {s[1] : s in Factorisation(p*OK)}>;
	aboveInSet:=func<p,S | primesAbove(p) subset Set(S)>; //are all primes
								// above p in set S?
	for sI in sieveInf do
		P,B,psi,imC:=Explode(sI);
		Append(~Pset,P);
		p:=primeBelow(P);
		print "prime below P is", p;
		if p lt 200 then
			Include(~pCands,p);
		end if;
		Lnew:=Kernel(psi) meet L;
		Lnew:=sub<A | [A!l : l in Generators(Lnew)]>;
		Q,pi:=quo<L|Lnew>;
		Qreps:=[A!(q@@pi) : q in Q]; 
		W:=[w+q : w in W, q in Qreps | Eltseq((w+q)@psi) in imC];
		L:=Lnew;
		print #W, Index(A,L);
		if IsEmpty(W) then
			return true;
		end if;
		for p in pCands do
			if aboveInSet(p, Pset) then
				print "all primes above", p, "are in Pset";
				Exclude(~pCands,p);
				print "checking saturation at", p;	
				if (p in smoothBase) or isSaturatedAtp(A,bas,p) then
					print "saturated at", p;
					chab:=chabauty(basfree,ptList,pt0,p);
					print chab;
					sieveInfp:=[* q : q in sieveInf | q[1] in primesAbove(p) *];
					Kp:=A;		
					for q in sieveInfp do
						Kp:=Kp meet Kernel(q[3]);
						Kp:=sub<A | [A!k : k in Generators(Kp)]>;
					end for;
					for i in [1..#chab] do
						if chab[i] then
							Q:=imRat[i];
							for w in W do
								if (Q-w) in Kp then
									Exclude(~W,w);
								end if;
							end for;				
						end if;
					end for;
					print "after applying Chabauty with prime", p;
					print "W has", #W, "elements";
					if #W eq 0 then
						return true;
					end if;
				end if;
			end if;
		end for;	
	end for;
	return false;
end intrinsic;
