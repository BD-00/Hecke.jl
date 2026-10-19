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
  t = gen(R)
  Fq = base_ring(R)
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
  return I
end

################################################################################
#
#  Divisor of degree one
#
################################################################################

####################
#
#  Improvements:
#
####################

#returns a divisor of degree one
function divisor_of_degree_one(F::Generic.AbsSimpleFunctionField)
  prime_support = Dict{Int, Divisor}()
  
  deg_gcd = 0 #gcd of currently found places (0 until first place is found)
  degree_list = Int[] #list of degrees for which we've found places

  trivial_div = trivial_divisor(F)

  Ofin = finite_maximal_order(F)
  Rfin = coefficient_ring(Ofin) #k[x]
  Fq = base_ring(Rfin)
  t = gen(Rfin)

  #D is trivial divisor
  function compose_divisor(D::Divisor, prime_support::Dict{Int, Divisor}, degree_list)
    bezout_coeffs = gcdx(degree_list...)[2:end]
    for i in 1:length(bezout_coeffs)
      #TODO: filter out zero coefficients? can exist?
      D += bezout_coeffs[i]*prime_support[degree_list[i]]
    end
    return D
  end

  function examine_place(P::Hecke.GenOrdIdl, d, prime_support, degree_list, trivial_div, deg_gcd)
    if !haskey(prime_support, d)
      g = gcd(deg_gcd, d)
      if iszero(deg_gcd) || g < deg_gcd
        push!(degree_list, d)
        prime_support[d] = Hecke.divisor(P)
        deg_gcd = g
      else 
        prime_support[d] = trivial_div #TODO: other alternative/list?
      end
    end
    return prime_support, degree_list, deg_gcd
  end

  #extra loop for degree 1 polys, since irreducible ones are trivial
  for c in Fq
    prime_dec = prime_decomposition(Ofin, t+c)
    for (P, _) in prime_dec
      @show typeof(P)
      d = degree(P)
      if d == 1
        return Hecke.divisor(P)
      else
        prime_support, degree_list, deg_gcd = examine_place(P, d, prime_support, degree_list, trivial_div, deg_gcd)
        if deg_gcd == 1
          return compose_divisor(trivial_div, prime_support, degree_list)
        end
      end
    end
  end

  @assert deg_gcd > 1

  #no finite rational place exists, check infinite places:
  Oinf = infinite_maximal_order(F)
  Rinf = coefficient_ring(Oinf)
  inf_dec = prime_decomposition(Oinf, gen(Rinf))
  for (P, _) in inf_dec
    d = degree(P)
    if d == 1
      return Hecke.divisor(P)
    else
      prime_support, degree_list, deg_gcd = examine_place(P, d, prime_support, degree_list, trivial_div, deg_gcd)
      if deg_gcd == 1
        return compose_divisor(trivial_div, prime_support, degree_list)
      end
    end
  end
  
  #look at places over degree > 1 polynomials
  poly_deg = 2 #degree of polynomials we iterate over
  while deg_gcd > 1
    @show deg_gcd, poly_deg
    if gcd(deg_gcd, poly_deg) === deg_gcd
      poly_deg += 1
      continue
    end
    irred_polys = Hecke.irreducible_polynomials(Rfin, poly_deg)
    for f in irred_polys
      prime_dec = prime_decomposition(Ofin, f)
      for (P, _) in prime_dec
        d = degree(P)*poly_deg
        prime_support, degree_list, deg_gcd = examine_place(P, d, prime_support, degree_list, trivial_div, deg_gcd)
        if deg_gcd == 1
          return compose_divisor(trivial_div, prime_support, degree_list)
        end
      end
    end
    poly_deg += 1
  end
end