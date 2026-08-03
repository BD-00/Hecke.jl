mutable struct ShExSequCtx{S, T1, T2} #TODO: declaration here with param U for maps
  G1::S
  G2::S
  G3::S
  mu1::Generic.MapWithSection #A->B with preimage (even though some might not exist)
  mu2::Generic.MapWithSection #B->C with preimage
  gens1::T1 #generators in A 
  gens2::T2 #generators in B
  gens3::Vector #generators in C
  iso1::Generic.MapWithSection #discrete logarithm in A
  iso2::Generic.MapWithSection #discrete logarithm in B
  iso3::Generic.MapWithSection #discrete logarithm in C
  function ShExSequCtx(G1::S, G2::S, gens1::T1, gens2::T2) where {S<:FinGenAbGroup, T1<:Vector, T2<:Vector}
    r = new{S, T1, T2}()
    r.G1 = G1
    r.G2 = G2
    r.gens1 = gens1
    r.gens2 = gens2
    return r
  end
end
#TODO: add A, B, C?, rel_preimage?

#Given an exact sequence of finitely generated abelian groups
#1 -> A -> B -> C -> 1 by mu1: A -> B, mu2: B -> C;
#'Z-modules' G1 ≅ A, G2 ≅ C together with iso1, iso2 (maps with preimages)
#generators gens1 for A, gens2 for C,
#func mapping a relation in G2 to an element in B,
#oper defining the operation of x and y in B,
#we compute G ≅ B.

#TODO: check for superfluous maps (e.g. mu2?)
#TODO: rename to group extension?
function B_from_A_and_C(G1, G2, mu1, mu2, iso1, iso2, gens1, gens2, func, oper)#::Function) where {S<:FinGenAbGroup, T<:Generic.MapWithSection, U<:Vector}
  @assert codomain(mu1) == domain(mu2)
  @assert length(gens1) == ncols(G1.rels)
  @assert length(gens2) == ncols(G2.rels)
  Ctx = Hecke.ShExSequCtx(G1, G2, gens1, gens2)
  Ctx.mu1 = mu1
  Ctx.mu2 = mu2
  Ctx.iso1 = iso1
  Ctx.iso2 = iso2
  A, B , C = domain(mu1), codomain(mu1), codomain(mu2) #TODO: necessary???

  #Compose relation matrix from existing ones:
  rels = block_diagonal_matrix([G2.rels, G1.rels])
  preim_gens2 = [mu2.section(c) for c in gens2]
  im_gens1 = [mu1(a) for a in gens1]
  Ctx.gens3 = vcat(preim_gens2, im_gens1)

  #Extend relations of G2:
  len = length(im_gens1) #number of gens in A
  r2, c2 = size(G2.rels)
  for i in 1:r2
    #relation in G2 -> elem in B via preimages of generators of C in B
    b = func(view(G2.rels, i, 1:c2), preim_gens2) #PROBLEM when negative entries 
    a = mu1.section(b) #preimage under mu1
    #TODO: take inverse of a to get positive coefficients in rel matrix?
    g_a = iso1.section(a) #preimage under iso1 (g_a in image by construction)
    rel = -g_a
    for j = 1:len
      if !iszero(g_a[j]) #improvement with pointer possible?
        rels[i, c2+j] = rel[j] #TODO: no negative entries!!!
      end
    end
    _rel = func(@view(rels[i, :]), Ctx.gens3) #test
    @assert isone(_rel) #test
  end
  Hecke.test_relation_matrix(rels, Ctx.gens3, func) #test

  #Construct abelian group from relation matrix:
  Ctx.G3 = abelian_group(rels)
  Ctx.G3.rels = rels

  #Compute isomorphism between G3 and B:
  iso3_func = x->func(x, Ctx.gens3) #G3 -> B
  iso3_func(rand(Ctx.G3))#test
  iso3_preim = x-> Hecke.disc_log_B_from_A_and_C(x, Ctx, func, oper)#B -> G3
  iso3_preim(one(B))
  Ctx.iso3 = map_with_preimage_from_func(iso3_func, iso3_preim, Ctx.G3, B)

  return Ctx #TODO: return G3 and iso3 as readable information for user? 
end

#function from B to G3 using disclogs in A and C
function disc_log_B_from_A_and_C(b, Ctx::ShExSequCtx, func::Function, oper::Function)
  c = Ctx.mu2(b)
  g_c = Ctx.iso2.section(c)
  len2 = length(Ctx.gens2)
  b2 = func(-g_c, Ctx.gens3[1:len2]) #inverse of elem corresponding to g_c in B
  a = Ctx.mu1.section(oper(b, b2))
  g_a = Ctx.iso1.section(a)
  return Ctx.G3(hcat(g_c.coeff, g_a.coeff))
end