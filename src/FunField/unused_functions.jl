### one unit quotient with maps ###


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
  for i = 1:n
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

#TODO: delete
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
  _gens_left = [1+c*x^j*gen_I*B[i] for i in 1:f for j in 0:d_i-1 for c in Fp_basis]
  
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
