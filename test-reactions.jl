using Catalyst

rn1 = @reaction_network begin
    k12, A+B --> C
    k21, C --> A+B
    k23, C --> D
    k31, D --> A+B 
end

reacts = reactions(rn1)
oderatelaw.(reacts)
osys = convert(ODESystem, rn1)
equations(osys)
incidencematgraph(rn1)