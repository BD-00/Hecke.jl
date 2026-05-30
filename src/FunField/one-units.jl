#rational function fields over Fp

@doc raw"""
    one_unit_quotient_fp(f::T, k::Int) where T <: PolyRingElem{FinFieldElem} -> Vector{T}, ZZMatrix

Given an irreducible polynomial $0\neq f \in R$ for $R = \mathbb{F}_p[x]$ generating the prime ideal $P=R*f$
and an integer $k$, compute the factor group $1+P/1+P^k$ of one-unit groups in $\mathbb{Z}-module$ representation
in terms of a list of generators and the relation matrix with row-wise relations.
Output: 
"""

function one_unit_quotient_fp(f::T, k::Int) where T <: PolyRingElem{<:FinFieldElem}
  @req k > 0 "k must be greater than zero"
  @req is_irreducible(f) "f must be irreducible"
  Fx = parent(f)
  x = gen(Fx)

  Fp = base_ring(f)
  p = characteristic(Fp)

  d = degree(f)

  #TODO: _rels as sparse matrix?

  k == 1 && return [Fx(1)], identity_matrix(ZZ, 1)

  #k is at least 2, 1+P/1+P^k can be computed directly:
  _gens = [1+x^i*f for i in 0:d-1]
  _rels = diagonal_matrix(p, d) #TODO:seems to be wrong, always one gen, so one relation

  k == 2 && return _gens, _rels

  #Assume that k>=3, so we need to divide k and work with exact sequences:
  steps = Int(ceil(log2(k))) #compute 1
  #a = 1
  b = 2
  for i in 2:steps-1
    #compute 1+P/1+P^(2^i)
    a=b
    b*=2
    _gens, _rels = group_extension_fp(f, a, b, _gens, _rels)
  end
  _gens, _rels = group_extension_fp(f, b, k, _gens, _rels)
  return _gens, _rels #TODO: output snf here?
end


@doc raw"""
    group_extension_fp(f::T, a::Int, b::Int, _gens_right, _rels_right) where T <: PolyRingElem{<:FinFieldElem} -> Vector{T}, ZZMatrix

Compute generators and relations of $1+P/1+P^b$ using generators and relations of $1+P/1+P^a$ and $1+P^a/1+P^b$
and the exact sequence $1 -> 1+P^a/1+P^b -> 1+P/1+P^b -> 1+P/1+P^a -> 1$.
"""

function group_extension_fp(f::T, a::Int, b::Int, _gens_right, _rels_right) where T <: PolyRingElem{<:FinFieldElem} #TODO: type declaration to f
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  Fx = parent(f)
  x = gen(Fx)

  Fp = base_ring(f)
  p = characteristic(Fp)

  d = degree(f)

  f_pow_a = f^a
  f_pow_b = f^b

  deg_bound = d*(b-a)

  _gens_left = [1+x^i*f_pow_a for i in 0:deg_bound-1]
  _rels_left = diagonal_matrix(p, deg_bound)
  _rels = block_diagonal_matrix([_rels_right, _rels_left])

  n, m = size(_rels_right)
  for i = 1:n
    #Compose relation on the right to a polynomial in 1+P^a and translate to the left mod f^b, so
    #for gens g_1,...,g_m and entries r_1, ..., r_m compute \prod g_j^r_j mod f^b:
    _rel = one(Fx)
    for j = 1:m
      r_j = _rels_right[i,j]
      if r_j > 0
        _rel = mulmod(_rel, powermod(_gens_right[j], r_j, f_pow_b), f_pow_b)  #TODO: smart reduction mod f^b
      end
    end
    
    _rel-=1
    iszero(_rel) && continue #1+0*f^a
    h = divexact(_rel-1, f_pow_a) #_rel = 1+h*f^a mod 1+f^b with h not in f^(b-a)
    @assert degree(h) < d*(b-a) 
    
    #h = \sum h_jx^j  with j<d*(b-a), hence
    #_rel = \prod (1+x_j*f^a)^h_j
    coeff_h = coefficients(h)
    j = m+1
    for h_j in coeff_h
      if !iszero(h_j)
        _rels[i, j] = lift(ZZ, -h_j)
      end
      j+=1
    end
  end
  return append!(_gens_right, _gens_left), _rels
end


#rational function fields over Fq

@doc raw"""
    one_unit_quotient_fp(f::T, k::Int) where T <: PolyRingElem{FinFieldElem} -> Vector{T}, ZZMatrix

Given an irreducible polynomial $0\neq f \in R$ for $R = \mathbb{F}_q[x]$ generating the prime ideal $P=R*f$
and an integer $k$, compute the factor group $1+P/1+P^k$ of one-unit groups in $\mathbb{Z}-module$ representation
in terms of a list of generators and the relation matrix with row-wise relations.
Output: 
"""

function one_unit_quotient_fq(f::T, k::Int) where T <: PolyRingElem{<:FinFieldElem}
  @req k > 0 "k must be greater than zero"
  @req is_irreducible(f) "f must be irreducible"
  Fx = parent(f)
  x = gen(Fx)

  Fq = base_ring(f)
  p = characteristic(Fq)

  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  d = degree(f)

  k == 1 && return Fx.Fp_basis, identity_matrix(ZZ, l)

  _gens = T[]
  #TODO: _rels as sparse matrix?

  #for k = 2, 1+P/1+P^k can be computed directly:
  _gens = [1+c*x^i*f for i in 0:d-1 for c in Fp_basis]
  _rels = diagonal_matrix(p, d*l)

  k == 2 && return _gens, _rels

  #Assume that k>=3, so we need to divide k and work with exact sequences:
  steps = Int(ceil(log2(k))) #compute 1
  #a = 1
  b = 2
  for i in 2:steps-1
    #compute 1+P/1+P^(2^i)
    a=b
    b*=2
    _gens, _rels = group_extension_fq(f, a, b, _gens, _rels)
  end
  _gens, _rels = group_extension_fq(f, b, k, _gens, _rels)
  return _gens, _rels #TODO: output snf here?
end


@doc raw"""
    group_extension_fq(f::T, a::Int, b::Int, _gens_right, _rels_right) where T <: PolyRingElem{<:FinFieldElem} -> Vector{T}, ZZMatrix

Compute generators and relations of $1+P/1+P^b$ using generators and relations of $1+P/1+P^a$ and $1+P^a/1+P^b$
and the exact sequence $1 -> 1+P^a/1+P^b -> 1+P/1+P^b -> 1+P/1+P^a -> 1$.
"""

function group_extension_fq(f::T, a::Int, b::Int, _gens_right, _rels_right) where T <: PolyRingElem{<:FinFieldElem} #TODO: type declaration to f
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  
  @show a,b #test
  
  Fx = parent(f)
  x = gen(Fx)

  Fq = base_ring(f)
  p = characteristic(Fq)

  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  d = degree(f)

  f_pow_a = f^a
  f_pow_b = f^b

  deg_bound = d*(b-a)

  _gens_left = [1+c*x^i*f_pow_a for i in 0:deg_bound-1 for c in Fp_basis]
  _rels_left = diagonal_matrix(p, deg_bound*l)
  _rels = block_diagonal_matrix([_rels_right, _rels_left])

  n, m = size(_rels_right)
  for i = 1:n
    #Compose relation on the right to a polynomial in 1+P^a and translate to the left mod f^b, so
    #for gens g_1,...,g_m and entries r_1, ..., r_m compute \prod g_j^r_j mod f^b:
    _rel = one(Fx)
    for j = 1:m
      r_j = _rels_right[i,j]
      if r_j > 0
        _rel = mulmod(_rel, powermod(_gens_right[j], r_j, f_pow_b), f_pow_b)  #TODO: smart reduction mod f^b
      end
    end
    @show i #test
    @show _rel
    @show _rel-=1
    iszero(_rel) && continue
    h = divexact(_rel, f_pow_a) #_rel = 1+h*f^a mod 1+f^b with h not in f^(b-a)
    @assert degree(h) < d*(b-a) 
    
    #h = \sum h_jx^j  with j<d*(b-a), hence
    #_rel = \prod (1+x_j*f^a)^h_j
    coeff_h = coefficients(h)
    j = m+1
    for h_j in coeff_h #coeffs in Fq, need coefficient to Fp-basis
      if !iszero(h_j)
        neg!(h_j)
        for idx in 0:l-1
          lambda = coeff(h_j, idx)
          if !iszero(lambda)
            _rels[i, j] = lift(ZZ, lambda)
          end
        end
        j+=1
      else
        j+=l
      end
    end
  end
  return append!(_gens_right, _gens_left), _rels
end

#TODO: add case where middle part is the direct sum of left and right?

#check whether polynomial described by the relation in row i is congruent to 1 mod f^a
function test_relation(_gens::_rels::ZZMatrix, i::Int, f_pow_a)

end