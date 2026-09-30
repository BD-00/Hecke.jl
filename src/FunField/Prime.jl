#find all irreducible monic polynomials over Fq up to degree d
#naive: degree-wise enumeration of monic polys and test for irreducibility

function irreducible_polynomials_up_to(R::FqPolyRing, d::Int)::Vector{FqPolyRingElem}
 t = gen(R)
 Fq = base_ring(R)
 I = [t+c for c in Fq]
 for i in 2:d
  V = vector_space(Fq, i)
  for v in V
    g = t^i + R([v[idx] for idx in 1:i])
    is_irreducible(g) && push!(I, g)
  end
 end
 return I
end

function irreducible_polynomials(R::FqPolyRing, d::Int)::Vector{FqPolyRingElem}
  if d == 1
    return [t+c for c in Fq]
  else
    I = FqPolyRingElem[]
    V = vector_space(Fq, d)
    for v in V
      g = t^d + R([v[idx] for idx in 1:d])
      is_irreducible(g) && push!(I, g)
    end
  end
end

################################################################################
#
#  Divisor of degree one
#
################################################################################

#returns a divisor of degree one
function divisor_of_degree_one(F::Generic.AbsSimpleFunctionField)
  D = Dict{ZZRingElem, Hecke.GenOrdIdl}()
  
  poly_deg = 1 #degree of polynomials we iterate over
  place_deg = 1 #degree of place we try to find
  deg_gcd = 0 #gcd of currently found places (0 until first place is found)
  
  degree_list #list of degrees for which we've found places

  Ofin = finite_maximal_order(F)
  Rfin = coefficient_ring(Ofin)
  Fq = base_ring(Rfin)
  t = gen(Rinf)
  #extra loop for degree 1 polys, since irreducible ones are trivial
  for c in Fq
    prime_dec = prime_decomposition(Ofin, t+c)
    for (P, _) in prime_dec
      d = ZZ(degree(P))
      if d == 1
        return P
      else
        if !haskey(D, d)
          D[d] = P
          deg_gcd = gcd(deg_gcd, d)
        end
      end
    end

    #no finite rational place exists, check infinite places:
    inf_dec = prim
  end

  Oinf = infinite_maximal_order(F)
  Rinf = coefficient_ring(Oinf)
  
  
end