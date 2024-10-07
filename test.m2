loadPackage "ReactionNetworks"
N = reactionNetwork "S1 + C0 <--> C1,C1 --> S2+C0, S2+C1 <-->  C2, C2 --> S1+C1"
R=createRing(N,QQ)
SS = flatten entries steadyStateEquations N
K = apply(#N.ReactionRates, i->random QQ)
Rr = N.ReactionRates/value
P = apply(#Rr, i->Rr#i=>sub(K#i,R))
F' = apply(SS, s-> sub(s,P))
C = conservationEquations N
L = {0,0,0,0,0}
Iv = N.InitialValues
S = apply(#Iv, i->R_(Iv#i)=>L#i)
F'' = apply(C, c->sub(c,S))
F = join(F',F'')
I = ideal F
isPrime(I)
groebnerBasis(I)