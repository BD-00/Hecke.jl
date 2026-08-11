#=
add_verbosity_scope(:RayClass)
set_verbosity_level(:RayClass, 1)

add_assertion_scope(:RayClass)
set_assertion_level(:RayClass, 1)
=#

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