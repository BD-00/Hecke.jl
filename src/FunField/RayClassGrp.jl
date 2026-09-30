#=
add_verbosity_scope(:RayClass)
set_verbosity_level(:RayClass, 1)

add_assertion_scope(:RayClass)
set_assertion_level(:RayClass, 1)
=#

#TODO: replace .section with preimage

mutable struct UnitGroupCtx
  G::FinGenAbGroup
  iso
  gens
  function UnitGroupCtx(G, iso::S, gens::T) where {S, T}
    return new(G, iso, gens)
  end
end

#Compute the multiplicative group (O/P^k)* using the exact sequence
#1 -> 1+P/1+P^k -> (O/P^k)* -> (O/P)* -> 1.

#Order of (O/P)* is q^deg(P)-1, where deg(P) = f(P|<min(P)>)*deg(min(P)).
#Note that degree(p) outputs the inertia degree.

function unit_group_mod_P_pow(P::GenOrdIdl, k::Int)
  O = P.order

  G1, iso1, gens1 = Hecke.one_unit_quotient_with_ctx(P, k)
  G2, iso2, gens2, mu2, func, func_mod_k = Hecke.mult_group_of_residue_field(P, k)

  #mu1: 1+P/1+P^k -> (O/P^k)* (actually O -> O)
  mu1 = map_with_preimage_from_func(func_mod_k, func_mod_k, O, O)

  #Operation in (O/P^k)*
  oper = (x,y) -> func_mod_k(x*y)

  ctx = B_from_A_and_C(G1, G2, mu1, mu2, iso1, iso2, gens1, gens2, func, oper) #ERROR for Q, 2
  return ctx.G3, ctx.iso3, ctx.gens3
end


#Construct O -> FP -> FP*, FP::FqField and FP*::FinGenAbGroup
#where phi1: O -> FP with preimage
#phi2: FP -> FP* with generator of FP* in FP.
#mu: O -> FP with preimage
#Note that only the preimages of phi2 are given, phi2.header.image is not defined.
function mult_group_of_residue_field(P::GenOrdIdl, k::Int)
  O = P.order
  P_pow_k = P^k
  FP, phi1 = residue_field(O, P)
  G, phi2 = unit_group(FP)

  @hassert :RayClass 3 order(G) == order(constant_field(O.F))^(degree(P)*degree(minimum(P)))-1
  G.rels = matrix(ZZ, 1, 1, [order(G)])

  func_mod_k = x -> mod(x, P_pow_k)
  preim_mod_k = x-> func_mod_k(phi1.header.preimage(x)) #FP -> O mod P^k
  mu = map_with_preimage_from_func(phi1.header.image, preim_mod_k, O, FP) #iso: O -> FP
  
  #isomorphism between G and FP(*):
  gen_q = phi2.generator #FqFieldElem generating FP*

  #G -> FP(*)
  im_func = x -> gen_q^x[1]

  #FP(*) -> G
  preim_func = x -> G([disc_log(gen_q, x)])

  iso = map_with_preimage_from_func(im_func, preim_func, G, FP)

  #map from G to O mod P^k:
  #preim_gen = preim_mod_k(gen_q)
  func = (x, gens) -> powermod(gens[1], x[1], P_pow_k) #problem: negative x
  return G, iso, [gen_q], mu, func, func_mod_k
end


#CRT
#Compute (O/m)*=(O/mfin)* X (O/minf)* 
function unit_group_mod_m(m::Divisor)
  F = m.function_field

  Mfin, Minf = ideals(m)
  fac_fin = factor(Mfin)
  fac_inf = factor(Minf)

  #unit_groups_fin = Dict{Hecke.GenOrdIdl, UnitGroupCtx}()
  #unit_groups_inf = Dict{Hecke.GenOrdIdl, UnitGroupCtx}()
  unit_groups = Dict{Hecke.GenOrdIdl, Hecke.UnitGroupCtx}() 

  S = []
  r = []

  #Compute (O/P^k)* for all P^k | m for finite and infinite ideals.
  for P in keys(fac_fin)
    push!(S, P)
    k = fac_fin[P]
    push!(r, k)
    G, iso, gens = Hecke.unit_group_mod_P_pow(P, k)
    unit_groups[P] = Hecke.UnitGroupCtx(G, iso, gens)
  end

  for P in keys(fac_inf)
    push!(S, P)
    k = fac_inf[P]
    push!(r, k)
    G, iso, gens = Hecke.unit_group_mod_P_pow(P, k)
    unit_groups[P] = Hecke.UnitGroupCtx(G, iso, gens)
  end

  rels = block_diagonal_matrix([unit_groups[P].G.rels for P in S])
  G = abelian_group(rels)
  G.rels = rels

  gens = reduce(vcat, [unit_groups[P].gens for P in S])

  #map from G to F
  func = function(g, S, unit_groups, r)
    x = []
    idx = 1
    for i in 1:length(S) 
      P = S[i]
      len = length(unit_groups[P].gens)
      x_i = unit_groups[P].iso(g[idx:idx+len])
      push!(x, x_i)
      idx += len
    end
    return weak_approximation(S, x, r, gens)
  end
  func_inv = function(c, r, unit_groups, G)
    g = matrix(ZZ, 1, 0, [])
    for i in 1:length(S)
      P = S[i]
      O = P.order
      P_pow = P^r[i]
      c_num = numerator(c, O)
      c_den = denominator(c, O)
      u = mod(c_num*invmod(c_den, P_pow), P_pow)
      g_i = unit_groups[P].iso.section(u)
      hcat!(g, g_i.coeff)
    end
    return G(g)
  end
  iso_map = x -> func(x, S, unit_groups, r)
  iso_map_inv = x -> func_inv(x, r, unit_groups, G)
  iso = map_with_preimage_from_func(iso_map, iso_map_inv, G, F)
  return UnitGroupCtx(G, iso, gens)
end

################################################################################
#
#  Weak Approximation
#
################################################################################

#TODO: adapt to get smaller result?
#u Vector with quotients gen_P/prod(gen_Q, Q not P)
function weak_approximation(S::Vector, x::Vector, r::Vector{Int})
  P = S[1]
  F = order(P).F
  gen_P = F(P.gen_two)
  u_den = gen_P
  u = [gen_P^2]
  y = [gen_P^r[1]]
  len = length(S)

  for i in 2:len
    P = S[i]
    gen_P = F(P.gen_two)
    u_den *= gen_P
    push!(u, gen_P^2)
    push!(y, gen_P^r[i])
  end
  u./=u_den
  #=
  for i in 1:len #test u
    Du = Hecke.divisor(u[i])
    for j in 1:len
      val_u = valuation(Du, S[j])
      if i == j
        @assert val_u == 1
      else
        @assert val_u == -1
      end
    end
  end #end test

  for i in 1:len #test y
    @assert valuation(Hecke.divisor(y[i]), S[i]) == r[i]
  end
  =#
  z = step_3(S, x, r, u)# + step_3(S, y, r, u) 
  return z
end

function step_3(S::Vector, y::Vector, r::Vector{Int}, u::Vector)
  len = length(r)
  t = minimum([valuation(Hecke.divisor(y[i]), P) for i in 1:len for P in S])
  s = maximum(r) - t

  w = inv(1+u[1]^s)
  #@assert valuation(Hecke.divisor(w-1), S[1]) > r[1]-t #test

  #=
  Dw = Hecke.divisor(w)#test
  for j in 2:len #test
    @show 1, j
    @assert valuation(Dw, S[j]) > r[j]-t
  end
  =#
  
  z = y[1]*w
  for i in 2:len #compute w_i
    w = inv(1+u[i]^s)
    #=
    Dw = Hecke.divisor(w)#test
    for j in 1:len #test ierate over primes
      @show i,j
      if i==j
        @assert valuation(Hecke.divisor(w-1), S[i]) > r[i]-t
      else
        @assert valuation(Dw, S[j]) == s > r[j]-t #ERROR
      end
    end #end test
    =#
    z += y[i]*w
  end
  #=
  for i in 1:len #test
    @assert valuation(divisor(z-y[i]), S[i]) > r[i]
  end
  =#
  return z
end


function test_weak_approximation(z, S, x, r)
  for i in 1:length(r)
    @show i
    @assert valuation(divisor(z-x[i]), S[i]) >=  r[i] # == r[i]
  end
end

################################################################################
#
#  p-class group
#
################################################################################

function class_group_p(F::Generic.AbsSimpleFunctionField)
  #B = basis_of_differentials(F)
  #dx = differential(separating_element(F))
  Fq = constant_field(F)
  Fp = base_field(Fq)
  p = order(Fp)

  Ofin = finite_maximal_order(F)
  J_fin = codifferent(Ofin)

  Oinf = infinite_maximal_order(F)
  x = gen(base_ring(F))
  J_inf = (1//x)^2 * codifferent(Oinf)

  RRCtx = Hecke._riemann_roch_space_with_ctx(J_fin, J_inf, F)

  Hecke.test_RRspace(RRCtx, J_fin, J_inf)

  #Compute representation matrix of (id - cartier operator) w.r.t. Fp-basis of RR space
  #for row vectors, so x->x*Mrep
  B = basis(F)
  B_im = [b - Hecke.cartier_operator(b) for b in RRCtx.gens]
  Mrep = reduce(vcat, [preimage(RRCtx.iso, a).v for a in B_im])

  #Compute right kernel (x*Mrep = 0)
  K = kernel(Mrep) #basis elements row-wise

  #Generators of kernel:
  kernel_gens = K*RRCtx.gens
  V = vector_space(Fp, nrows(K))

  Hecke.test_kernel(kernel_gens) #test

  #disclog for elem in kernel using disclog in whole RR-space resp. F
  function disclog_kernel(a::Generic.AbsSimpleFunctionFieldElem, RRCtx, K)
    a_v = preimage(RRCtx.iso, a).v #elem in Fp-vectorspace of RR
    u = solve(K, a_v) #a_v = u*K -> coordinates w.r.t. kernel basis
    return u
  end

  #test
  function test_disclog_kernel(kernel_gens, V, RRCtx, K)
    v = collect(V)
    kernel_elems = [(v[i].v*kernel_gens)[1] for i in 1:length(V)]
    for i in 1:length(kernel_elems)
      @assert v[i].v == disclog_kernel(kernel_elems[i], RRCtx, K)
    end
  end
  #a->V(disclog_kernel(a))
  Hecke.test_disclog_kernel(kernel_gens, V, RRCtx, K) #test

  #Fp-iso: divisor in class group -> elem in kernel
  
  function Div_to_kernel(D::Divisor)
    F = function_field(D)
    p = characteristic(F)
    princ_div = p.d*D
    bool, a = is_principal_with_data(princ_div)
    @assert bool #input should always be in p-class group

    #map (1/a)da to b dx, so b = 1/a * delta_x(a)
    return inv(a)*Hecke.nth_derivative(a, 1)
  end


  #find a such that p*D = (a)
  P = prime_decomposition(Ofin, numerator(x))[1][1] #naive, TODO: Div of deg 1
  candidate_space = riemann_roch_space(genus(F)*p.d*divisor(P)) #candidates for a
  #da/dx for a in basis of candidates
  candidate_dx = [nth_derivative(a, 1) for a in candidate_space]
  len = length(candidate_space)
  for b in kernel_gens #solve a*b=a'
    M = matrix(F, 1, len, b.*candidate_space-candidate_dx)
    Mker = kernel(M, side = :right)
  end
  a 
  function kernel_to_Div(D::Divisor)
    

  end



  return Mrep
end

#differential omega = a dx
function cartier_operator(a::Generic.AbsSimpleFunctionFieldElem)
  F = parent(a)
  p = characteristic(F) #ZZRingElem
  a = nth_derivative(a, p.d-1)
  @assert isequal(pth_root(-a)^p,-a) #test FAILS
  return pth_root(-a)
end

#Computes the derivative of f w.r.t. the separating element
function derivative_in_sep_elem(f::Generic.AbsSimpleFunctionFieldElem)
  F = parent(f)
  y = gen(F)
  y_diff = differential(y).f
  C = coefficients(f)
  Cdiff = F.(derivative.(C))
  z = Cdiff[1]
  for (i, c) in enumerate(C)
    i == 1 && continue
    z += Cdiff[i]*y^(i-1)+c*(i-1)*y^(i-2)*y_diff
  end
  return z
end

function nth_derivative(f::Generic.AbsSimpleFunctionFieldElem, n::Int)
  F = parent(f)
  i = 0
  while i < n
    fden = denominator(f)
    fnum = f*fden
    dfnum = derivative_in_sep_elem(fnum)
    dfden = derivative(fden)
    f = (dfnum * fden - fnum * dfden)//F(fden^2) #TODO: prettify
    i+=1
  end
  return F(f)
end

#TODO: if pth root in Fq expensive, use LinALg
function Hecke.pth_root(a::Generic.AbsSimpleFunctionFieldElem{FqFieldElem, FqPolyRingElem})
  F = parent(a)
  p = characteristic(F)
  n = degree(F)
  kx = base_ring(F)

  #M maps p powers of coordinates of a to coordinates of a^p 
  M = matrix(base_ring(F), [coordinates(b^p) for b in basis(F)])
  Minv = inv(M)

  coord = coordinates(a)*Minv
  for i in 1:n
    c = coord[i]

    c_num_test = numerator(c) #test

    c_num = numerator(c)
    c_num = deflate(c_num, p.d)
    c_num = map_coefficients(pth_root, c_num)

    @assert isequal(c_num^p, c_num_test) #test

    c_den_test = denominator(c) #test
   
    c_den = denominator(c) 
    c_den = deflate(c_den, p.d)
    c_den = map_coefficients(pth_root, c_den)

    @assert isequal(c_den^p, c_den_test) #test
    @assert isequal(kx(c_num, c_den)^p, c) #test

    coord[i] = kx(c_num, c_den)
  end
  return F(coord)
end

################################################################################
#
#  Divisor of degree one
#
################################################################################

#returns a divisor of degree one
function divisor_of_degree_one(F::Generic.AbsSimpleFunctionField)
  
  poly_deg = 1 #degree of polynomials we iterate over
  place_deg = 1 #degree of place we try to find
  deg_gcd = 0 #gcd of currently found places (0 until first place is found)

  #extra loop for degree 1 polys, since irreducible ones are trivial


end



################################################################################
#
#  Tests
#
################################################################################



#test pth_root of poly in k[x]
function test_pth_root(R::FqPolyRing)
  k = base_ring(R)
  p = characteristic(k)
  c = rand(k, 4)
  h = R(c)
  hp = h^p
  g = deflate(hp, p.d)
  g = map_coefficients(pth_root, g)
  @assert isequal(g,h)
end


#test iso to Fp-vectorspace

function test_RRiso(RRCtx)#::RiemannRochCtx)
  iso = RRCtx.iso
  V = domain(iso)
  v = collect(V)
  RR = [(v[i].v*RRCtx.gens)[1] for i in 1:length(V)]
  for i in 1:length(RR)
    w = V(v[i])
    x = RR[i]
    @assert x == iso(w)
    @assert preimage(iso, x) == v[i]
  end
end

  #TODO: test via inverse ideals and in
#test whether generators g_i satisfy D+(g_i) >= 0 
function test_RRspace(RRCtx, J_fin, J_inf)
  Oinf = order(J_inf)
  F = function_field(Oinf)
  for g in RRCtx.gens
    @assert g in J_fin
    g2 = F(denominator(J_inf))*g
    @assert mod(Oinf(g2), numerator(J_inf)) == 0
  end
end

function test_kernel(kernel_gens)
  for g in kernel_gens
    @assert cartier_operator(g) == g
  end
end