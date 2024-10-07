loadPackage "ReactionNetworks"
N = reactionNetwork "XD<--> X,X <--> XT, XT --> Xp, Xp+Y <--> XpY, XpY --> X+Yp, XT+Yp <--> XTYp, XTYP --> XT+Y,XD+Yp <-->XDYp, XDYp -->XD + Y"
R=createRing(N,QQ)
SS = flatten entries steadyStateEquations N
K = apply(#N.ReactionRates, i->random QQ)
Rr = N.ReactionRates/value
P = apply(#Rr, i->Rr#i=>sub(K#i,R))
F' = apply(SS, s-> sub(s,P)) 
I1 = ideal(F')  -- steady-state ideal
C = conservationEquations N
L = {0,0,0,0,0,0,0,0,0,0}
Iv = N.InitialValues
S = apply(#Iv, i->R_(Iv#i)=>L#i)
F'' = apply(C, c->sub(c,S)) 
I2 = ideal(F'') -- conservation laws ideal
F = join(F',F'')
I = ideal F 
groebnerBasis(I1)