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

  #Operation in 1+P/1+P^k
  oper = (x,y) -> func_mod_k(x*y)

  ctx = B_from_A_and_C(G1, G2, mu1, mu2, iso1, iso2, gens1, gens2, func, oper)
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
  G.rels = matrix(ZZ, 1, 1, [length(G)])

  func_mod_k = x -> mod(x, P_pow_k)
  preim_mod_k = x-> func_mod_k(phi1.header.preimage(x))
  mu = map_with_preimage_from_func(phi1.header.image, preim_mod_k, O, FP)
  
  #isomorphism between G and FP(*):
  gen_q = phi2.generator #FqFieldElem

  #G -> FP(*)
  im_func = x -> g^x[1]

  #FP(*) -> G
  preim_func = x -> G([disc_log(gen_q, x)])

  iso = map_with_preimage_from_func(im_func, preim_func, G, FP)

  #map from G to O mod P^k:
  #preim_gen = preim_mod_k(gen_q)
  func = (x, gens) -> powermod(gens[1], x[1], P_pow_k) #problem: negative x
  return G, iso, [gen_q], mu, func, func_mod_k
end