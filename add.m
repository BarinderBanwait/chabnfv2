

// a is an element of a local field

looksZero:=function(a);
	return (AbsolutePrecision(a)-Valuation(a)) le 3;
end function;

looksEqual:=function(a,b);
	return looksZero(a-b);
end function;





intrinsic add(f::RngUPolElt,D1::SeqEnum,D2::SeqEnum) -> SeqEnum
	{
 add points D1=[p,q] and D2=[r,s] on the Jacobian of a genus 2 curve y^2=f(x)
 over a local field
 p,r are quadratic monic polys over local field
 q,s are linear
 f must be defined over the local field
 will return [] if any of the following happen:
 (i) p and q have a resultant close to zero
 (ii) discriminant of p is close to zero
 (iii) discriminant of q is close to zero
 (iv) a certain determinant is close to zero (see the code)
in all these cases the generic case of the addition law cannot be trusted
will also return [] if either D1 or D2 is []
 otherwise it will return  [P,Q] which represents the sum
	}
	if #D1 ne 2 or #D2 ne 2 then
		return [];
	end if;
	if Degree(D1[1]) ne 2 or Degree(D2[1]) ne 2 then
		return [];
	end if;
	if Degree(D1[2]) ne 1 or Degree(D2[2]) ne 1 then
		return [];
	end if;
	Kx:=Parent(f);
	x:=Kx.1;
	p,q:=Explode(D1);
	r,s:=Explode(D2);
	p0,p1,_:=Explode(Coefficients(p));
	q0,q1:=Explode(Coefficients(q));
	r0,r1,_:=Explode(Coefficients(r));
	s0,s1:=Explode(Coefficients(s));
	K:=Parent(p0);
	res:=p0^2 - p0*p1*r1 - 2*p0*r0 + p0*r1^2 + p1^2*r0 - p1*r0*r1 + r0^2;	
	// resultant of x^2+p1 x+p0 and x^2+r1 x + r0
	if looksZero(res) then 
		return [];
	end if;
	if looksZero(p1^2-4*p0) then
		return [];
	end if;
	if looksZero(r1^2-4*r0) then
		return [];
	end if; 
	M:=Matrix(K,[[1,0,-p0,p0*p1],
			[0,1,-p1,p1^2-p0],
			[1,0,-r0,r0*r1],
			[0,1,-r1,r1^2-r0]]); 
	det:=Determinant(M);
	if looksZero(det) then
		return [];
	end if;
	u:=Matrix(K,[[q0],[q1],[s0],[s1]]);
	v:=M^(-1)*u;
	h0:=v[1,1];
	h1:=v[2,1];
	h2:=v[3,1];
	h3:=v[4,1];
	//h:=v[1,1]+v[2,1]*x+v[3,1]*x^2+v[4,1]*x^3;
	h:=h0+h1*x+h2*x^2+h3*x^3;
	P:=Quotrem(h^2-f,(x^2+p1*x+p0)*(x^2+r1*x+r0));		
	assert(Degree(P)) eq 2;
	P:=P/LeadingCoefficient(P);
	P0:=Coefficient(P,0);
	P1:=Coefficient(P,1);
	Q0:=h0 - h2*P0 + h3*P0*P1;
	Q1:=(h1 - h2*P1 - h3*P0 + h3*P1^2);
	return [P0+P1*x+x^2,-Q0-Q1*x];
end intrinsic;


intrinsic double(f::RngUPolElt,D::SeqEnum) -> SeqEnum
	{
	 return 2*D if the generic duplication law is reliable
	 otherwise returns []
	}
	if #D ne 2 or Degree(D[1]) ne 2 or Degree(D[2]) ne 1 then
		return [];
	end if;	
	Kx:=Parent(f);
	x:=Kx.1;
	u,v:=Explode(D);
	u0,u1,_:=Explode(Coefficients(u));
	if looksZero(u1^2-4*u0) then
		return [];
	end if;
	v0,v1:=Explode(Coefficients(v));
	if Degree(f) eq 6 then
		f0,f1,f2,f3,f4,f5,f6:=Explode(Coefficients(f));
	else
		f0,f1,f2,f3,f4,f5:=Explode(Coefficients(f));
		f6:=0;
	end if;
	K:=Parent(u0);
	M:=Matrix(K,[[1,0,-u0,u0*u1],
			[0,1,-u1,u1^2-u0],
		 [0,2*v0, -4*u0*v1, 6*u0*u1*v1 - 6*u0*v0],
		[ 0,2*v1, -4*u1*v1 + 4*v0, -6*u0*v1 + 6*u1^2*v1 - 6*u1*v0 ]]);
	v:=Matrix(K,[[v0],[v1],
[-12*u0^2*u1*f6 + 5*u0^2*f5 + 6*u0*u1^3*f6 - 5*u0*u1^2*f5 + 4*u0*u1*f4 - 3*u0*f3 + f1],
[6*u0^2*f6 - 18*u0*u1^2*f6 + 10*u0*u1*f5 - 4*u0*f4 + 6*u1^4*f6 - 5*u1^3*f5 + 4*u1^2*f4 - 3*u1*f3 +
    2*f2]]);
	if looksZero(Determinant(M)) then
		return [];
	end if;
	h:=M^(-1)*v;
	h0:=h[1,1];
	h1:=h[2,1];
	h2:=h[3,1];
	h3:=h[4,1];	
	h:=h0+h1*x+h2*x^2+h3*x^3;
	P:=Quotrem(h^2-f,u^2);		
	if (Degree(P) ne 2) or looksZero(LeadingCoefficient(P)) then 
		return [];
	end if;
	P:=P/LeadingCoefficient(P);
	P0:=Coefficient(P,0);
	P1:=Coefficient(P,1);
	Q0:=h0 - h2*P0 + h3*P0*P1;
	Q1:=(h1 - h2*P1 - h3*P0 + h3*P1^2);
	return [P0+P1*x+x^2,-Q0-Q1*x];
end intrinsic;
//end function;	

neg:=function(D);
	if #D ne 2 then
		return [];
	else
		return [D[1],-D[2]];
	end if;
end function;


intrinsic pow(f::RngUPolElt,D::SeqEnum,n::RngIntElt) -> SeqEnum
	{
	 return n*D if it can do the computation reliably 
	 otherwise returns []
	}
	if #D ne 2 or Degree(D[1]) ne 2 or Degree(D[2]) ne 1 then
		return [];
	end if;
	assert n ne 0;
	if n lt 0 then
		n:=-n;
		D:=neg(D);
	end if;
	if n eq 1 then
		return D;
	end if;
	if IsEven(n) then
		return double(f,$$(f,D,n div 2));
	else
		if IsPrime(n) eq false then 
					// if n is composite with largest prime
					// factor p then we compute
					// n*D=(n/p)*(p*D) 
					// this way is of course theoretically slower
					// than the alternative in "else"
					// but is faster in practice
					// and does not lose as much accuracy
			p:=Maximum(PrimeDivisors(n));
			pD:=$$(f,D,p);
			return $$(f,pD,n div p);
		else	
			m:=n div 2;
			mD:=$$(f,D,m);
			tmD:=double(f,mD);
			return add(f,D,tmD);
		end if;
	end if;
end intrinsic;

intrinsic localpow(D::JacHypPt,n::RngIntElt,P::RngOrdIdl,prec::RngIntElt) -> SeqEnum
	{
	Here D is a point on a genus 2 Jacobian over number field K 
	P is a prime ideal of the ring of integers of K
	return n*D in K_P to precision prec if it can do the computation reliably 
	 otherwise returns []
	}
	J:=Parent(D);
	K:=BaseRing(J);
	KP,h:=Completion(K,P : Precision:=prec);
	if D[3] ne 2 or  Degree(D[1]) ne 2 or  Degree(D[2]) ne 1 then
		return [];
	end if;
	assert IsMonic(D[1]);
	C:=Curve(J);
	f,g:=HyperellipticPolynomials(C);
	assert g eq 0;
	KPx<x>:=PolynomialRing(KP);
	hx:=func<f | KPx!Polynomial([h(c) : c in Coefficients(f)])>;
	f:=hx(f);
	D:=[hx(D[1]),hx(D[2])];
	return pow(f,D,n);
end intrinsic;



intrinsic preIntLocal(D1::JacHypPt,D2::JacHypPt,n::RngIntElt,P::RngOrdIdl,prec::RngIntElt)->SeqEnum,Map,Map
	{
	want to compute n*D1+D2 P-adically
	where n is possibly huge
	moreover, we want to do this using the generic group laws on C^(2)
	this will return a P-adic answer whose absolute precision is at least prec
	it will also return maps h, hx
	h:K->K_P
	hx: K->K_P[x]
	}
	J:=Parent(D1);
	K:=BaseRing(J);
	C:=Curve(J);
	f,g:=HyperellipticPolynomials(C);
	assert g eq 0;
	kD1:=5*D1;
	k:=5;
	while Degree(kD1[1]) ne 2 or Discriminant(kD1[1]) eq 0 or Degree(kD1[2]) ne 1 do
		kD1:=kD1+D1;
		k:=k+1;
	end while;  // at then kD1=k*D1 is a "good" multiple of D1
	res:=[];  // this will eventually be n*D1+D2
	calcprec:=Max(prec,50);  // this the precision we will use for the P-adic field
	// and will adjust this upwards if the result is not accurate enough
	//
	resPrec := func<D | Min([AbsolutePrecision(c) : c in (Coefficients(D[1]) cat Coefficients(D[2]))])>;   // this will measure the precision of our result
	//
	while #res eq 0 or resPrec(res) lt prec do
		res:=[];
		KP,h:=Completion(K,P : Precision:=calcprec);
		KPx<x>:=PolynomialRing(KP);
		hx:=func<pl | KPx!Polynomial([h(K!c) : c in Coefficients(pl)])>; // hx: K[x] -> K_P[x]
		fP:=hx(f);
		PkD1:=[hx(kD1[1]),hx(kD1[2])]; // make k*D1 P-adic
		m:=0;	
		while #res eq 0 do
			m:=m+1;
			if IsDivisibleBy(n+m,k) then
				F2:=-m*D1+D2;  
				if Degree(F2[1]) eq 2 and Discriminant(F2[1]) ne 0 and Degree(F2[2]) eq 1then
					F2:=[hx(F2[1]),hx(F2[2])];
					F1:=pow(fP,PkD1,(n+m) div k);  // this is (n+m)*D1a
					res:=add(fP,F1,F2);  // this will be n*D1+D2 unless we obtain [] from
						// falling down one of the non-generic cases.
				end if;
			end if;
		end while;
		calcprec:=calcprec+50;
	end while;	
	return res,h,hx;
end intrinsic;


intrinsic preInt(D1::JacHypPt,D2::JacHypPt,n::RngIntElt,P::RngOrdIdl,prec::RngIntElt)->SeqEnum
	{
	compute n*D1+D2 P-adically
	and then lift the answer to the global field 
	}
	D,h,_:=preIntLocal(D1,D2,n,P,prec);
	u:=Coefficients(D[1]);
	v:=Coefficients(D[2]);
	assert #u eq 3 and #v eq 2;
	u:=[c@@h : c in u];
	assert u[3] eq 1;
	v:=[c@@h : c in v];
	Kx:=Parent(D1[1]);
	return [Kx!u,Kx!v];	
end intrinsic;

