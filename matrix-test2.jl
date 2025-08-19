using Symbolics

function decompose_negative(M)
    n, m = size(M)
    pos = similar(M)
    neg = similar(M)
    for i in 1:n
        for j in 1:m
            expr = M[i, j]
            expr_expanded = expand(expr)
            terms = get_terms(expr_expanded)
            pos_terms = []
            neg_terms = []
            for term in terms
                ifelse(is_negative_term(term), push!(neg_terms, term),push!(pos_terms, term))
            end
            pos[i, j] = sum(pos_terms)
            neg[i, j] = sum(neg_terms)
        end
    end
    return pos, neg
end

function get_terms(expr)
    if istree(expr) && operation(expr) == (+)
        return vcat([get_terms(arg) for arg in arguments(expr)]...)
    else
        return [expr]
    end
end

function is_negative_term(term)
    # Check if term is a numeric constant
    if term isa Number
        return term < 0
    end
    
    # Check if term is a symbolic constant with a numeric value
    if Symbolics.isconstant(term)
        val = Symbolics.value(term)
        if val isa Number
            return val < 0
        else
            # Recursively check the structure of the constant's value
            return is_negative_term(val)
        end
    end
    
    # Check structural negativity for symbolic expressions
    if istree(term)
        op = operation(term)
        args = arguments(term)
        
        # Case 1: Direct unary minus (e.g., -x)
        if op == (-) && length(args) == 1
            return true
        # Case 2: Multiplication/division with a negative component
        elseif op == (*) || op == (/)
            return any(is_negative_term, args)
        # Case 3: Recursively check nested operations
        else
            return any(is_negative_term, args)
        end
    end
    
    # Default case: term is not structurally negative
    return false
end
@variables β γ μ N s r

M = [
    β*s/N - γ - μ - 1    β*r/N - 2;
    -γ - 3               β*s/N - γ - μ - 4
]
F,A = decompose_negative(M)