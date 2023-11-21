# chabnfv2
## Siksek's chabnf code, souped up

Here's how to run the code on one example from Siksek's paper: open MAGMA at the top level, and execeute the following:

```
Attach("g2-jac.m");
Attach("add.m");
load "JSearch.m";

Qu<u>:=PolynomialRing(Rationals());
K<t>:=NumberField(u^3-2);
eps:=1-t;

Kx<x>:=PolynomialRing(K);

s := 0;
C:=HyperellipticCurve(3*(4*eps^(-s)*x^5-eps^(2*s)));
pts:=ratPointsC(C);
```

This currently works (although it takes a while).

This is a unit test; any changes made to underlying routines should be such that this example still works.