using Symbolics
using LinearAlgebra

function NGM(M, var)
    M = simplify.(M) # normalize all expressions
    F = map(e -> begin
        expr = string(e)
        depends = any(v -> occursin(string(v), expr), var)
        positive = !occursin("-", expr)
        depends && positive ? e : 0
    end, M)
    A = simplify.(M - F)
    return F, A
end

@variables β γ μ N s r
var = [s, r]

M = [
    β*s/N - γ - μ - 1    β*r/N - 2
    -γ - 3               β*s/N - γ - μ - 4
]

F, A = NGM(M, var)

#display(F)
#display(A)