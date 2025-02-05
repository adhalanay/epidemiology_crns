using Oscar
using Symbolics
using Catalyst

"""
complex_balancing_ideal(rn::ReactionSystem)
Computes the complex balancing ideal as defined in G.Craciun et al. *J. of Symbolic Computaion* **44**(2009) no.11, 1551-1565

"""
function complex_balancing_ideal(rn::ReactionSystem)
   in1=Catalyst.assemble_oderhs(rn,species(rn))
   f1,f2=Symbolics.build_function(in1,vcat(species(rn),parameters(rn))...)
   f=eval(f1)
   R1,vars1=polynomial_ring(QQ,map(p -> Symbolics.tosymbol(p;escape=false),parameters(rn)))
   K1=fraction_field(R1)
   R2,vars2=polynomial_ring(K1,map(s -> Symbolics.tosymbol(s;escape=false),species(rn)))
   R2 
   x=prod(vars2)
   J=ideal(R2,x)
   I=ideal(R2,Base.invokelatest(f,vars2...,vars1...)) #avoid the world problem
   saturation(I,J)
end