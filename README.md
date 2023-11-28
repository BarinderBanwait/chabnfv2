# chabnfv2
## Siksek's chabnf code, souped up

Here's how to run the code on one example from Siksek's paper: open MAGMA at the top level, and execeute the following:

```
Attach("g2-jac.m");
Attach("add.m");
load "JSearch.m";
SetClassGroupBounds("GRH");

Qu<u>:=PolynomialRing(Rationals());
K<t>:=NumberField(u^3-2);
eps:=1-t;

Kx<x>:=PolynomialRing(K);

s := 0;
C:=HyperellipticCurve(3*(4*eps^(-s)*x^5-eps^(2*s)));
pts:=ratPointsC(C);
```

This currently does not work; I'm getting a Runtime error:

```
In file "/home/barinder/chabnfv2/g2-jac.m", line 729, column 42:
>>                         mat:=VerticalJoin(mat,matP);

Runtime error in 'VerticalJoin': Arguments have incompatible coefficient rings
```

This is probably some change in MAGMA in the intervening 13 years since Siksek wrote his code; I am currently debugging this.

This is a unit test; any changes made to underlying routines should be such that this example still works.

## Some comments on changing Coleman integration

The Coleman integration modules seem to be in `g2-jac.m`, specifically the `integrals` and `integrationMatrix` intrinsics.