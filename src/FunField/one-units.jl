#Hecke.mod changed locally in GenOrd/Ideal.jl!!!

################################################################################
#
#  1+p/1+p^k
#
################################################################################

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

  k == 1 && return Fx(Fp_basis), identity_matrix(ZZ, l)

  _gens = T[]
  #TODO: _rels as sparse matrix?

  #for k = 2, 1+P/1+P^k can be computed directly:
  _gens = [1+c*x^i*f for i in 0:d-1 for c in Fp_basis]
  _rels = diagonal_matrix(p, d*l)
  test_relation_matrix(_gens, _rels, f^2) #test

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
    test_relation_matrix(_gens, _rels, f^b) #test
  end
  _gens, _rels = group_extension_fq(f, b, k, _gens, _rels)
  test_relation_matrix(_gens, _rels, f^k) #test
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

  _gens_left = [1+c*x^i*f_pow_a for i in 0:deg_bound-1 for c in Fp_basis] #x^i blockwise, iterating over coeffs in block
  _rels_left = diagonal_matrix(p, deg_bound*l)
  _rels = block_diagonal_matrix([_rels_right, _rels_left])
  _gens = append!(_gens_right, _gens_left)

  n, m = size(_rels_right)
  for i = 1:n
    #Compose relation on the right to a polynomial in 1+P^a and translate to the left mod f^b, so
    #for gens g_1,...,g_m and entries r_1, ..., r_m compute \prod g_j^r_j mod f^b:
    _rel = one(Fx)
    for j = 1:m
      r_j = _rels_right[i,j]
      if r_j > 0 #not unequal???
        _rel = mulmod(_rel, powermod(_gens_right[j], r_j, f_pow_b), f_pow_b)  #TODO: smart reduction mod f^b
      end
    end
    _rel-=1
    iszero(_rel) && continue
    h = divexact(_rel, f_pow_a) #_rel = 1+h*f^a mod 1+f^b with h not in f^(b-a)
    @assert degree(h) < d*(b-a) 
    
    #h = \sum h_jx^j  with j<d*(b-a), hence
    #_rel = \prod (1+x_j*f^a)^h_j
    coeff_h = coefficients(h)
    j = m+1
    for h_j in coeff_h #coeffs in Fq, need coefficient to Fp-basis
      if !iszero(h_j)
        neg!(h_j) #careful: inplace might not work for all types
        for idx in 0:l-1
          lambda = coeff(h_j, idx)
          if !iszero(lambda)
            _rels[i, j] = lift(ZZ, lambda)
          end
          j+=1
        end
      else
        j+=l
      end
    end

    test_relation(_gens, _rels, i, f_pow_b) #test
  end 
  return _gens, _rels
end

#TODO: add case where middle part is the direct sum of left and right?
#TODO: compare to composition of relations on module side via generators there


#TODO: How to distinguish GenOrdIdl for function and number fields in type declarations?

function one_unit_quotient(P::Hecke.GenOrdIdl, k::Int)::Tuple{Vector{<:GenOrdElem}, ZZMatrix}
  @req k > 0 "k must be greater than zero"
  @req is_prime(P) "P must be a prime ideal"

  O = order(P)
  n = degree(O)

  k == 1 && return Hecke.GenOrdElem[], zero_matrix(ZZ, 0, 0) #trivial group

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  f = degree(P)
  gen_P = P.gen_two
  @assert isone(valuation(ideal(gen_P), P)) #test
  
  M = basis_matrix(P)
  #=
  if f!= n
    @assert isone(M[f+1, f+1]) #test (n only needed here)
  end
  =#
  d = 0
  _gens = Hecke.GenOrdElem[]
  for i = 1:f
    d_i = degree(M[i, i])
    omega_i = gen_P*B[i]
    append!(_gens, [1+c*x^j*omega_i for j in 0:d_i-1 for c in Fp_basis]) #TODO: test and write better
    d += d_i
  end
  
  _rels = diagonal_matrix(p, d*l) #TODO: make sure that p in ZZ
  #Hecke.test_relation_matrix(_gens, _rels, P^2)

  #for k = 2, 1+P/1+P^k can be computed directly:
  k == 2 && return _gens, _rels

  steps = Int(ceil(log2(k)))

  b = 2
  for i in 2:steps-1
    #compute 1+P/1+P^(2^i)
    a=b
    b*=2
    _gens, _rels = Hecke.group_extension(P, a, b, _gens, _rels)
    #Hecke.test_relation_matrix(_gens, _rels, P^b) #test
  end
  _gens, _rels = group_extension(P, b, k, _gens, _rels)
  #Hecke.test_relation_matrix(_gens, _rels, P^k) #test
  return _gens, _rels #TODO: output snf here?
end

function group_extension(P::Hecke.GenOrdIdl, a::Int, b::Int, _gens_right, _rels_right)
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  
  @show a,b
  O = order(P)
  n = degree(O)

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  f = degree(P)
  gen_I = P.gen_two^a
  #@assert valuation(ideal(gen_I), P) == a #test
  
  P_pow_b = P^b
  Mb = basis_matrix(P_pow_b)
  P_pow_diff = P^(b-a)
  M = basis_matrix(P_pow_diff)
  if f!= n #test
    @assert isone(M[f+1, f+1]) 
  end
  d = 0
  _gens_left = Hecke.GenOrdElem[]
  for i = 1:f
    d_i = degree(M[i, i]) #TODO: degrees all equal to deg(min^(b-a))=deg(min)*(b-a)???
    omega_i = gen_I*B[i]
    _gens_left = append!(_gens_left, [1+c*x^j*omega_i for j in 0:d_i-1 for c in Fp_basis]) #TODO: test and write better
    d += d_i
  end
  
  _rels_left = diagonal_matrix(p, d*l) #TODO: make sure that p in ZZ
  _rels = block_diagonal_matrix([_rels_right, _rels_left])
  _gens = append!(_gens_right, _gens_left) #changes _gens_right!!!

  #Compose relation on the right to an element in 1+P^a and translate to the left mod P^b, so
  #for gens g_1,...,g_m and entries r_1, ..., r_m compute \prod g_j^r_j mod P^b:
  nr, nc = size(_rels_right)
  #@assert _rels[1:nr, 1:nc] == _rels_right #test
  #Hecke.test_relation_matrix(_gens, _rels[nc+1:end, :], P^b) #test
  Mrep = representation_matrix(gen_I) #representation matrix for x -> (gen_P)^a * x
  y = one(O)
  for i = 1:nr
    #@show i
    y = one(O)
    for j = 1:nc
      r_j = _rels_right[i,j]
      if r_j != 0
        y*=powermod(_gens_right[j], r_j, P_pow_b)
      end
    end

    #Go over to P^a/P^b:
    y = mod(y-1, P_pow_b)
    #iszero(y) && Hecke.test_relation(_gens, _rels, i, P^b)#test
    #iszero(y) && continue #correct??? y = 0 mod P^b <=> z = 0 mod P^(b-a)
    @assert y in P^a #test
    @assert iszero(y) || !(y in P^b) #test, change if y not zero
    #Given the isomorphism O/P^(b-a) -> P^a/P^b, z -> gen_I * z, 
    #compute a preimage of y = gen_I * z mod P^(b-a) via (Mrep|M) * (coord(z),_)^T = y:
    A = vcat(Mrep, Mb)
    coord_y = Fx.(coordinates(y))
    #@assert coord_y == [numerator(x) for x in coordinates(y)] #test
    vec_z = solve(A, coord_y)[1:n]
    z = O(vec_z) #preimage of y in O
    z = mod(z, P_pow_diff) #z mod P^(b-a)
    w = gen_I*z
    @assert w in P^a#test
    @assert iszero(w) || !(w in P^b)#test
    @assert w - y in P^b #test
    if iszero(z)
      @assert y in P^b
      Hecke.test_relation(_gens, _rels, i, P^b)
      continue
    end

    #Complete relation in _rels[i,:] w.r.t. _gens_left:
    z_coord = Fx.(coordinates(-z))
    #=
    @assert z_coord == [numerator(x) for x in coordinates(-z)] #test
    for j = f+1:n #test
      @assert z_coord[j] == 0
    end
    =#
    gen_idx = nc+1 #iterate over _left_gens in (the right part of) _gens
    for j = 1:f
      d_i = degree(M[j,j])
      z_i = z_coord[j]
      #@assert degree(z_i) < d_i #test
      #coefficients of coordinate to B[j] in k:
      #TODO: coeff_i = coefficients(z_i) #order: constant coeff to leading coeff
      _i = 0 #test whether generators are matching
      for s in 0:d_i-1 #Problem with gen_idx when deg(h_j) < d_i using coefficients()
        h_j = coeff(z_i, s)
        #@show gen_idx, 1
        if iszero(h_j)
          gen_idx += l
          _i += 1
          continue
        else
          for Fp_idx in 0:l-1
            #@show gen_idx, 2
            @assert _gens[gen_idx] == _gens_left[gen_idx-nc] #test
            @assert _gens[gen_idx] == 1+Fp_basis[Fp_idx+1]*x^_i*gen_I*B[j] #test whether generators are matching
            lambda = coeff(h_j, Fp_idx)
            !iszero(lambda) && (_rels[i, gen_idx] = lift(ZZ, lambda))
            gen_idx +=1
          end
        end
        _i += 1 #test whether generators are matching
      end
      #gen_idx += d_i - length(coeff_i) #when using coefficients()
    end
    Hecke.test_relation(_gens, _rels, i, P_pow_b) #test 
    #Hecke.test_relation_matrix(_gens, _rels[1:i, :], P_pow_b) #test
  end
  #Hecke.test_relation_matrix(_gens, _rels, P_pow_b)
  return _gens, _rels
end

#=
### Sparse version ###
function one_unit_quotient(::Type{SMat}, P::Hecke.GenOrdIdl, k::Int)::Tuple{Vector{<:GenOrdElem}, SMat}
  @req k > 0 "k must be greater than zero"
  @req is_prime(P) "P must be a prime ideal"

  O = order(P)
  n = degree(O)

  k == 1 && return Hecke.GenOrdElem[], zero_matrix(ZZ, 0, 0) #trivial group

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  f = degree(P)
  gen_P = P.gen_two
  @assert isone(valuation(ideal(gen_P), P)) #test
  
  M = basis_matrix(P)
  if f!= n #test
    @assert isone(M[f+1, f+1])
  end
  d = 0
  _gens = Hecke.GenOrdElem[]
  for i = 1:f
    d_i = degree(M[i, i])
    omega_i = gen_P*B[i]
    append!(_gens, [1+c*x^j*omega_i for j in 0:d_i-1 for c in Fp_basis]) #TODO: test and write better
    d += d_i
  end
  
  _rels = diagonal_matrix(SMat, ZZ, p, d*l) #TODO: make sure that p in ZZ
  Hecke.test_relation_matrix(_gens, _rels, P^2)

  #for k = 2, 1+P/1+P^k can be computed directly:
  k == 2 && return _gens, _rels

  steps = Int(ceil(log2(k)))

  b = 2
  for i in 2:steps-1
    #compute 1+P/1+P^(2^i)
    a=b
    b*=2
    _gens, _rels = Hecke.group_extension(P, a, b, _gens, _rels)
    Hecke.test_relation_matrix(_gens, _rels, P^b) #test
  end
  _gens, _rels = group_extension(P, b, k, _gens, _rels)
  Hecke.test_relation_matrix(_gens, _rels, P^k) #test
  return _gens, _rels #TODO: output snf here?
end

function group_extension(::Type{SMat}, P::Hecke.GenOrdIdl, a::Int, b::Int, _gens_right, _rels_right)
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  
  @show a,b #test
  
  O = order(P)
  n = degree(O)

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  f = degree(P)
  gen_I = P.gen_two^a
  @assert valuation(ideal(gen_I), P) == a #test
  
  P_pow_b = P^b
  Mb = basis_matrix(P_pow_b)
  P_pow_diff = P^(b-a)
  M = basis_matrix(P_pow_diff)
  if f!= n #test
    @assert isone(M[f+1, f+1]) 
  end
  d = 0
  _gens_left = Hecke.GenOrdElem[]
  for i = 1:f
    d_i = degree(M[i, i])
    omega_i = gen_I*B[i]
    _gens_left = append!(_gens_left, [1+c*x^j*omega_i for j in 0:d_i-1 for c in Fp_basis]) #TODO: test and write better
    d += d_i
  end
  
  _rels_left = diagonal_matrix(SMat, ZZ, p, d*l) #TODO: make sure that p in ZZ
  _rels = block_diagonal_matrix([_rels_right, _rels_left])
  _gens = append!(_gens_right, _gens_left) #changes _gens_right!!!

  #Compose relation on the right to an element in 1+P^a and translate to the left mod P^b, so
  #for gens g_1,...,g_m and entries r_1, ..., r_m compute \prod g_j^r_j mod P^b:
  nr, nc = size(_rels_right)#TODO: check whether nc necessary
  @assert _rels[1:nr, 1:nc] == _rels_right #test
  #Hecke.test_relation_matrix(_gens, _rels[nc+1:end, :], P^b) #test, syntax doesn't work for sparse matrices
  for i = nc+1:nr #test
    Hecke.test_relation(_gens, _rels, i, P^b)
  end
  Mrep = representation_matrix(gen_I) #representation matrix for x -> (gen_P)^a * x
  y = one(O)
  for i = 1:nr
    @show i
    y = one(O)
    for idx = 1:length(_rels_right[i].pos)
      r_j = _rels_right[i].values[idx]
      y*=mod(_gens_right[j]^r_j, P_pow_b) #use powermod
    end

    #Go over to P^a/P^b:
    y = mod(y-1, P_pow_b)
    iszero(y) && Hecke.test_relation(_gens, _rels, i, P^b)#test
    #iszero(y) && continue #correct??? y = 0 mod P^b <=> z = 0 mod P^(b-a)
    @assert y in P^a #test
    @assert iszero(y) || !(y in P^b) #test, change if y not zero
    #Given the isomorphism O/P^(b-a) -> P^a/P^b, z -> gen_I * z, 
    #compute a preimage of y = gen_I * z mod P^(b-a) via (Mrep|M) * (coord(z),_)^T = y:
    A = vcat(Mrep, Mb)
    coord_y = [numerator(x) for x in coordinates(y)]
    for v in coordinates(y) #test
      @assert isone(denominator(v))
    end
    vec_z = solve(A, coord_y)[1:n]
    z = O(vec_z) #preimage of y in O
    z = mod(z, P_pow_diff) #z mod P^(b-a)
    w = gen_I*z
    @assert w in P^a#test
    @assert iszero(w) || !(w in P^b)#test
    @assert w - y in P^b #test
    if iszero(z)
      @assert y in P^b
      Hecke.test_relation(_gens, _rels, i, P^b)
      continue
    end

    #Complete relation in _rels[i,:] w.r.t. _gens_left:
    z_coord = [numerator(x) for x in coordinates(-z)]
    for v in coordinates(-z) #test
      @assert isone(denominator(v))
    end
    for j = f+1:n #test
      @assert z_coord[j] == 0
    end
    gen_idx = nc+1 #iterate over _left_gens in (the right part of) _gens
    for j = 1:f
      d_i = degree(M[j,j])
      z_i = z_coord[j]
      @assert degree(z_i) < d_i #test
      #coefficients of coordinate to B[j] in k:
      #TODO: coeff_i = coefficients(z_i) #order: constant coeff to leading coeff
      _i = 0 #test whether generators are matching
      for s in 0:d_i-1 #Problem with gen_idx when deg(h_j) < d_i using coefficients()
        h_j = coeff(z_i, s)
        #@show gen_idx, 1
        if iszero(h_j)
          gen_idx += l
          _i += 1
          continue
        else
          for Fp_idx in 0:l-1
            #@show gen_idx, 2
            @assert _gens[gen_idx] == _gens_left[gen_idx-nc] #test
            @assert _gens[gen_idx] == 1+Fp_basis[Fp_idx+1]*x^_i*gen_I*B[j] #test whether generators are matching
            lambda = coeff(h_j, Fp_idx)
            !iszero(lambda) && (_rels[i, gen_idx] = lift(ZZ, lambda))
            gen_idx +=1
          end
        end
        _i += 1 #test whether generators are matching
      end
      #gen_idx += d_i - length(coeff_i) #when using coefficients()
    end
    Hecke.test_relation(_gens, _rels, i, P_pow_b) #test 
    #Hecke.test_relation_matrix(_gens, _rels[1:i, :], P_pow_b) #test
  end
  Hecke.test_relation_matrix(_gens, _rels, P_pow_b)
  return _gens, _rels
end
=#

#returns abstract maps together with map and preimage map (disc_log)
function one_unit_quotient_with_maps(P::Hecke.GenOrdIdl, k::Int)::Tuple{Vector{Hecke.GenOrdElem}, ZZMatrix}
  @req k > 0 "k must be greater than zero"
  @req is_prime(P) "P must be a prime ideal"

  O = order(P)
  n = degree(O)

  #TODO: k == 1 && return Hecke.GenOrdElem[], zero_matrix(ZZ, 0, 0) #trivial group

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  f = degree(P)
  gen_P = P.gen_two
  @assert isone(valuation(ideal(gen_P), P)) #test
  
  M = basis_matrix(P)
  if f!= n
    @assert isone(M[f+1, f+1]) #test (n only needed here)
  end
  d = 0
  _gens = Hecke.GenOrdElem[]
  for i = 1:f
    d_i = degree(M[i, i])
    omega_i = gen_P*B[i]
    append!(_gens, [1+c*x^j*omega_i for j in 0:d_i-1 for c in Fp_basis]) #TODO: test and write better
    d += d_i
  end
  
  _rels = diagonal_matrix(p, d*l) #TODO: make sure that p in ZZ
  Hecke.test_relation_matrix(_gens, _rels, P^2)

  G = abelian_group(_rels)
  G.rels = _rels
  
  #for k = 2, 1+P/1+P^k can be computed directly:
  k == 2 && return _gens, _rels

  steps = Int(ceil(log2(k)))

  b = 2
  for i in 2:steps-1
    #compute 1+P/1+P^(2^i)
    a=b
    b*=2
    _gens, _rels = Hecke.group_extension(P, a, b, _gens, _rels)
    Hecke.test_relation_matrix(_gens, _rels, P^b) #test
  end
  _gens, _rels = group_extension(P, b, k, _gens, _rels)
  Hecke.test_relation_matrix(_gens, _rels, P^k) #test
  return _gens, _rels #TODO: output snf here?
end

function group_extension_with_maps(P::Hecke.GenOrdIdl, a::Int, b::Int, _gens_right, _rels_right)
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  
  @show a,b #test
  
  f = degree(P)
  O = order(P)
  n = degree(O)

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  
  gen_I = P.gen_two^a
  @assert valuation(ideal(gen_I), P) == a #test
  
  if f!= n #test
    @assert isone(M[f+1, f+1]) 
  end

  #TODO: check correctness:
  d = degree(minimum(P))*(b-a)
  _gens_left = [1+c*x^j*omega_i for i in 1:f for j in 0:d_i-1 for c in Fp_basis]
  
  _rels_left = diagonal_matrix(p, length(_gens_left)) #TODO: make sure that p in ZZ
  _rels = block_diagonal_matrix([_rels_right, _rels_left])
  _gens = append!(_gens_right, _gens_left) #changes _gens_right!!!

  #Compose relation on the right to an element in 1+P^a and translate to the left mod P^b, so
  #for gens g_1,...,g_m and relation r = [r_1, ..., r_m] compute \prod g_j^r_j mod P^b:
  nr, nc = size(_rels_right)
  @assert _rels[1:nr, 1:nc] == _rels_right #test
  Hecke.test_relation_matrix(_gens, _rels[nc+1:end, :], P^b) #test
  #Mrep = representation_matrix(gen_I) #representation matrix for x -> (gen_P)^a * x
  y = one(O)
  for i = 1:nr
    @show i
    y = _map_abgroup_of_a_to_b(view(_rels_right, i, :), P, b, _gens_right)
    
    #Compute inverse of y in 1+P^a/1+P^b knowing that (1+z)^(-1) = 1-z:
    y = 2-y

    disc_log(y, P, a, b, _gens_left, view(rels, i, length(_gens)))
    
    Hecke.test_relation(_gens, _rels, i, P_pow_b) #test 
  end
  Hecke.test_relation_matrix(_gens, _rels, P_pow_b)
  return _gens, _rels
end

#disclogs

#1+P^a/1+P^b -> "G"
function disc_log(x::GenOrdElem, P::GenOrdIdl, a::Int, b::Int, gens::Vector{<:GenOrdElem}, g::Union{Vector{ZZRingElem}, Nemo.MatrixView{ZZMatrix, ZZRingElem}})
  @req x-1 in P^a "x not in 1 + P^a" #TODO: check whether necessary
  _ngens = length(gens)

  #TODO: prime dependent part outside in a struct
  O = order(P)
  Fx = base_ring(O)
  Fq = base_ring(Fx)
  l = degree(Fq)

  f = degree(P)

  gen_I = P.gen_two^a
  P_pow_b = P^b

  Mrep = representation_matrix(gen_I) #representation matrix for x -> (gen_P)^a * x
  Mb = basis_matrix(P_pow_b)
  P_pow_diff = P^(b-a)

  #Go over to P^a/P^b:
  x = mod(x-1, P_pow_b)

  #Given the isomorphism O/P^(b-a) -> P^a/P^b, y -> gen_I * y, 
  #compute a preimage of x = gen_I * y mod P^(b-a) via
  #(Mrep | M) * (coord(y),_)^T = coord(x):
  A = vcat(Mrep, Mb)
  x_coord = Fx.(coordinates(x))
  vec_y = solve(A, x_coord)[1:n]
  y = mod(O(vec_y), P_pow_diff) #in O/P^(b-a)
  iszero(y) && return g

  #Compute the image of y under O/P^(b-a) -> G by decomposing coord(y):
  y_coord = Fx.(coordinates(y))

  d = degree(minimum(P))*(b-a) #TODO: check correctness

  idx = 1
  for j = 1:f #iterate over coordinates in Fq[x]
    y_j = y_coord[j]
    @assert degree(y_j) < d #test
    for s in 0:d-1 #iterate over powers of x
      h_s = coeff(y_j, s) #coefficient in Fq
      if iszero(h_s)
        idx += l
      else
        for Fp_idx in 0:l-1 #elem in Fq as Fp-vector
          lambda = coeff(h_j, Fp_idx)
          if !iszero(lambda)
            g[idx] = lift(ZZ, lambda)
          end
          idx += 1
        end
      end
    end
  end
  @assert idx == _ngens+1
  return g
end



#with context:

function one_unit_quotient_with_ctx(P::Hecke.GenOrdIdl, k::Int)::Tuple{FinGenAbGroup, Generic.MapWithSection, Vector{<:GenOrdElem}}
  if k == 2
    return one_unit_quotient_a_b(P, 1, 2)
  else
    O = P.order
    b = k
    r = ceil(Int,log2(k))-1 #max r with 2^r < k
    a = 2^r

    #1+P/1+P^b from 1+P^a/1+P^b and 1+P/1+P^a
    G1, iso1, gens1 = Hecke.one_unit_quotient_a_b(P, a, b)
    G2, iso2, gens2 = Hecke.one_unit_quotient_with_ctx(P, a)

    func_mod_a = x->mod(x, P^a)
    func_mod_b = x->mod(x, P^b)

    #1+P^a/1+P^b -> 1+P/1+P^b
    mu1 = Hecke.map_with_preimage_from_func(func_mod_b, func_mod_b, O, O)
    #1+P/1+P^b -> 1+P/1+P^a
    mu2 = Hecke.map_with_preimage_from_func(func_mod_a, func_mod_b, O, O)
    
    func = x-> Hecke.map_G_mod_b(x, P, b, gens2)
    ctx = Hecke.B_from_A_and_C(G1, G2, mu1, mu2, iso1, iso2, gens1, gens2, func)
    return ctx.G3, ctx.iso3, ctx.gens3
  end
end

#Gomputes G ≅ 1+P^a/1+P^b with generators and respective isomorphisms.
function one_unit_quotient_a_b(P, a, b)
  @show a,b
  #Abelian group and generators:
  gens, rels = gens_and_rels_a_b(P, a, b)
  G = abelian_group(rels)
  G.rels = rels

  #G -> 1+P^a/1+P^b:
  func = x-> map_G_mod_b(x, P, b, gens)

  #1+P^a/1+P^b -> G
  preim = x -> disc_log_a_b(x, P, a, b, G, gens)

  iso = map_with_preimage_from_func(func, preim, G, P.order)

  return G, iso, gens
end

function gens_and_rels_a_b(P, a, b)
  @req a < b <= 2*a "b must lie between a and 2*a (not necess. strictly)"
  
  f = degree(P)
  O = order(P)
  n = degree(O)

  B = basis(O)

  Fx = base_ring(O)
  x = gen(Fx)
  Fq = base_ring(Fx)
  p = characteristic(Fq)
  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq) #q = p^l

  
  gen_I = P.gen_two^a
  @assert valuation(ideal(gen_I), P) == a #test

  #TODO: check correctness:
  d = degree(minimum(P))*(b-a)
  gens = [1+c*x^j*gen_I*B[i] for i in 1:f for j in 0:d-1 for c in Fp_basis]
  
  rels = diagonal_matrix(p, length(gens)) #TODO: make sure that p in ZZ

  return gens, rels
end

#G -> 1+P^a/1+P^b, works for all a<b
function map_G_mod_b(x::Union{FinGenAbGroupElem, Nemo.MatrixView{ZZMatrix, ZZRingElem}}, P::GenOrdIdl, b::Int, gens::Vector{<:GenOrdElem})
  P_pow_b = P^b
  _ngens = length(gens)
  y = one(P.order)
  
  #Note that inv(1+x) = 1-x in 1+P^a/1+P^b
  #y = 1+x => -y+2 = 1-x
  for i in 1:_ngens
    e = x[i]
    if e > 0 #TODO: problem for e < 0
      y = mod(y*powermod(gens[i], e, P_pow_b), P_pow_b)
    elseif e < 0
      y = mod(y*powermod(-gens[i]+2, -e, P_pow_b), P_pow_b)
    end
  end
  return y
end

#1+P^a/1+P^b -> G
function disc_log_a_b(x::GenOrdElem, P::GenOrdIdl, a::Int, b::Int, G::FinGenAbGroup, gens::Vector{<:GenOrdElem})
  @req x-1 in P^a "x not in 1 + P^a" #TODO: check whether necessary
  _ngens = length(gens)

  #TODO: prime dependent part outside in a struct
  O = order(P)
  n = degree(O)
  Fx = base_ring(O)
  Fq = base_ring(Fx)
  l = degree(Fq)

  f = degree(P)

  gen_I = P.gen_two^a
  P_pow_b = P^b
  Mrep = representation_matrix(gen_I) #representation matrix for x -> (gen_P)^a * x
  Mb = basis_matrix(P_pow_b)
  P_pow_diff = P^(b-a)

  #Go over to P^a/P^b:
  x = mod(x-1, P_pow_b)

  #Given the isomorphism O/P^(b-a) -> P^a/P^b, y -> gen_I * y, 
  #compute a preimage of x = gen_I * y mod P^(b-a) via
  #(Mrep | M) * (coord(y),_)^T = coord(x):
  A = vcat(Mrep, Mb)
  x_coord = Fx.(coordinates(x))
  vec_y = solve(A, x_coord)[1:n]
  y = mod(O(vec_y), P_pow_diff) #in O/P^(b-a)
  iszero(y) && return G()

  #Compute the image of y under O/P^(b-a) -> G by decomposing coord(y):
  y_coord = Fx.(coordinates(y))

  d = degree(minimum(P))*(b-a) #TODO: check correctness

  g = zeros(ZZ, _ngens)
  idx = 1
  for j = 1:f #iterate over coordinates in Fq[x]
    y_j = y_coord[j]
    @assert degree(y_j) < d #test
    for s in 0:d-1 #iterate over powers of x
      h_s = coeff(y_j, s) #coefficient in Fq
      if iszero(h_s)
        idx += l
      else
        for Fp_idx in 0:l-1 #elem in Fq as Fp-vector
          lambda = coeff(h_s, Fp_idx)
          if !iszero(lambda)
            g[idx] = lift(ZZ, lambda)
          end
          idx += 1
        end
      end
    end
  end
  @assert idx == _ngens+1
  return G(g)
end


#"abelian_group(1+P/1+P^a)" -> 1+P/1+P^b

#TODO: rename
function _map_abgroup_of_a_to_b(elem::Union{Vector{ZZRingElem}, Nemo.MatrixView{ZZMatrix, ZZRingElem}}, P::GenOrdIdl, b::Int, gens::Vector{<:GenOrdElem})::GenOrdElem
  x = one(P.order)
  P_pow_b = P^b
  n = length(gens)
  for j in 1:n
    e = elem[j]
    if e != 0
      x*=powermod(gens[j], e, P_pow_b) #TODO add mod P^b around mul
    end
  end
  return x
end

################################################################################
#
#  (O/P^k)*
#
################################################################################

#Compute the multiplicative group (O/P^k)* using the exact sequence 1 -> 1+P/1+P^k -> (O/P^k)* -> (O/P)* -> 1.

#Order of (O/P)* is q^deg(P)-1, where deg(P) = f(P|<min(P)>)*deg(min(P)).
#Note that degree(p) outputs the inertia degree.


#Find a random element in O\P that is reduced mod P
#Idea: Coordinates c_i = 0 for i > inertia degree and deg(c_i) < deg(min(P)) otherwise (see diagonal of basis_matrix(P)) 
function rand_elem_mod_P(P::GenOrdIdl, minP = minimum(P))
  #TODO: type assertions
  O = order(P)
  n = degree(O)
  f = degree(P)
  dmin = degree(minP)
  R = parent(minP) #Fq[x]
  _coord = [rand(R, 0:dmin-1) for _ in 1:f]
  return O(_coord)
end

#Find generator g\in O with <g mod p> = (O/P)*:
function primitive_elem_residue_field(P::GenOrdIdl)
  O = order(P)
  minP = minimum(P)
  dmin = degree(minP)
  f = degree(P)
  d = f*dmin
  q = size(constant_field(O.F))
  M = q^d-1 #order of (O/P)*
  fM = factor(M)

  root_found = false
  counter = 0
  while counter < 10 #TODO: check probability of success
    @show counter += 1
    root_found = true
    g = rand_elem_mod_P(P, minP)
    
    #is_primitive_root(g), inspired by Misc/UnitsModM.jl
    for (p,_) in fM
      if powermod(g,divexact(M,p), P) == 1 #too slow :/ -> square and multiply
        root_found = false
        break
      end
    end
    if root_found
      return true, g, M
    end
  end
  return false, zero(O), M
end

#TODO: generator with "good" properties?

#Given element a in 1+P \subseteq O mod P^k, find it's representation in the ZZ-module.


#Use 1 -> 1+P/1+P^k -> (O/P^k)* -> (O/P)* -> 1 and g\in O to find missing relation.

#Compute (O/P^k)* for given prime ideal P and an integer k.
function mult_group_mod_prime_power(P::GenOrdIdl, k::Int)
  _gens, _rels = one_unit_quotient(P, k) #Z-module structure of 1+P/1+P^k given by gens and rels
  bool, g, M = primitive_elem_residue_field(P)
  y = powermod(g, M, P^k) #g^M mod P^k

  #disclog(y) in 1+P/1+P^k:
end



################################################################################
#
#  Auxiliary
#
################################################################################


### auxiliary stuff TODO: move to Sparse ###
function diagonal_matrix(::Type{SMat}, R::Ring, x::T, n::Int)::SMat{T} where T
  A = sparse_matrix(R)
  A.c = n
  for i in 1:n
    push!(A, sparse_row(R, [(i, x)]))
  end
  return A
end

#compute mod(f^e, I) using square and multiply
#inspired by powermod in GenOrd/GenOrd.jl
function Hecke.powermod(a::Hecke.GenOrdElem, e::ZZRingElem, I::Hecke.GenOrdIdl)
  @assert e > 0 #negative exponents not needed for the moment
  r = one(parent(a))
  e == 0 && return r
  for i = bits(e)
    r *= r
    if i
      r *= a
    end
    r = mod(r, I)
  end
  return r
end

#=
function pow(I::Hecke.GenOrdIdl, e::ZZRingElem)#only better for high exponents
  @assert e > 0 #negative exponents not needed for the moment
  O = order(I)
  J = ideal(O, O(1)) #TODO: better syntax available?
  e == 0 && return J
  for i = bits(e)
    J *= J
    if i
      J *= I
    end
  end
  return J
end
=#

################################################################################
#
#  Test functions
#
################################################################################

#test whether relation = 1 mod I
function test_relation(_gens::Vector{<:Hecke.GenOrdElem}, _rels::ZZMatrix, i::Int, I)
  #@show i
  y = one(parent(_gens[1]))
  for j = 1:size(_rels)[2]
      y*=_gens[j]^_rels[i, j]
  end
  @assert isone(mod(y, I))
end

#test whether relation = 1 mod I
function test_relation_matrix(_gens::Vector{<:Hecke.GenOrdElem}, _rels::ZZMatrix, I)
  y = one(parent(_gens[1]))
  m, n = size(_rels)
  for i = 1:m
    #@show i
    y = one(parent(_gens[1]))
    for j = 1:n
        y*=_gens[j]^_rels[i, j]
    end
    @assert isone(mod(y, I))
  end
end


### Sparse tests ###
#test whether relation = 1 mod I
function test_relation(_gens::Vector{<:Hecke.GenOrdElem}, _rels::SMat{ZZRingElem}, i::Int, I)
  y = one(parent(_gens[1]))
  for idx in 1:length(_rels[i].pos)
      j = _rels[i].pos[idx]
      y*=_gens[j]^_rels[i].values[idx]
  end
  @assert isone(mod(y, I))
end

#test whether relation = 1 mod I
function test_relation_matrix(_gens::Vector{<:Hecke.GenOrdElem}, _rels::SMat{ZZRingElem}, I)
  y = one(parent(_gens[1]))
  m = nrows(_rels)
  for i = 1:m
    y = one(parent(_gens[1]))
    for idx in 1:length(_rels[i].pos)
        j = _rels[i].pos[idx]
        y*=_gens[j]^_rels[i].values[idx]
    end
    @assert isone(mod(y, I))
  end
end


### Polynomial tests ###
#check whether polynomial described by the relation in row i is congruent to 1 mod f^a
function test_relation(_gens::Vector{T}, _rels::ZZMatrix, i::Int, f_pow_a) where T <: PolyRingElem{<:FinFieldElem}
  l = length(_gens)
  @assert l == size(_rels)[2]
  g = one(parent(_gens[1]))
  for j in 1:l
    g*=powermod( _gens[j], _rels[i, j], f_pow_a)
  end
  m = mod(g, f_pow_a)
  @assert m == 1
end

function test_relation_matrix(_gens::Vector{T}, _rels::ZZMatrix, f_pow_k) where T <: PolyRingElem{<:FinFieldElem}
  l = length(_gens)
  @assert l == size(_rels)[2]
  for i in 1:size(_rels)[1]
    g = one(parent(_gens[1]))
    for j in 1:l
      g*=powermod( _gens[j], _rels[i, j], f_pow_k)
    end
    m = mod(g, f_pow_k)
    @assert m == 1
  end
end

#test whether h results from relation resp. whether rel*relright = 1



#try with ideal in Fq[x] as k[x]-module:
function one_unit_quotient_fqx(f::T, k::Int) where T <: PolyRingElem{<:FinFieldElem}
  @req k > 0 "k must be greater than zero"
  @req is_irreducible(f) "f must be irreducible"
  #TODO
end

#computes (1+f)^g mod m, where f, g=\sum g_i*x^i are polynomials
#as \prod (1+x^i*f)^g_i 
function gen_pow_poly_mod(f, g, m)
  #TODO: assertion such that x^i*f makes sense (closed operation)
  Fx = parent(f)
  x = gen(Fx)

  Fq = base_ring(f)

  Fp_basis = basis(Fq) #[1, o, o^2, ...] indexed by 0, 1, 2, ... when using coeff(a, i) 
  l = degree(Fq)

  elem = one(x)
  coeff_g = collect(coefficients(g))
  for i in 1:length(coeff_g)
    x_pow_i = x^(i-1)
    for j = 1:l
      elem=mulmod(elem, powermod((1+Fp_basis[j]*x_pow_i*f), lift(ZZ, coeff(coeff_g[i], j-1)), m), m)
    end
  end
  return elem
end