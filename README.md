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

If all is well, you should see the following:

```
Chabauty is respectively successful at [ true, true, true, true, true ]
after applying Chabauty with prime 31
W has 0 elements
succeeded in proving that the only K-rational points are [ (1 : 0 : 0), (1 : 3 :
1), (1/3*(t^2 + 2*t + 1) : 1/3*(-10*t^2 - 8*t - 13) : 1), (1 : -3 : 1), 
(1/3*(t^2 + 2*t + 1) : 1/3*(10*t^2 + 8*t + 13) : 1) ]
```

This is a unit test; any changes made to underlying routines should be such that this example still works.

## Some comments on changing Coleman integration

The Coleman integration modules seem to be in `g2-jac.m`, specifically the `integrals` and `integrationMatrix` intrinsics.