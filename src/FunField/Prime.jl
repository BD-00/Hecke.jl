function rational_primes(F::AbstractAlgebra.Generic.FunctionField{FqFieldElem})
 kt = base_ring(F) #Fq(t)
 t = numerator(gen(kt))
 k = base_ring(kt) #Fq

 I = [t+c for c in k] #irreducible polynomials of deg 1 over Fq (warning: in Fq(t), so no test for irred. possible)
 fin_ord = finite_maximal_order(F)
 fin_places = []
 for p in I
  p_dec = prime_decomposition(fin_ord, numerator(p))
  for (q,e) in p_dec
   isone(degree(q)) && push!(fin_places, q)
  end
 end
 inf_ord = infinite_maximal_order(F)
 inf_places = []
 t_inv = gen(base_ring(inf_ord))
 inf_dec = prime_decomposition(inf_ord, t_inv)
 for (q,e) in inf_dec
  isone(degree(q))&&push!(inf_places, q)
 end
 return FactorBase(fin_places), FactorBase(inf_places)
end


function primes(F::AbstractAlgebra.Generic.FunctionField{FqFieldElem}, d::Int)
 kt = base_ring(F) #Fq(t)
 t = numerator(gen(kt))
 k = base_ring(kt) #Fq

 I = irred_polys(parent(t), d) #irreducible polynomials of deg 1 over Fq

 fin_ord = finite_maximal_order(F)
 fin_places = []
 for p in I
  deg_p = degree(p)
  p_dec = prime_decomposition(fin_ord, p)
  for (q,e) in p_dec
   f = degree(q)
   deg_q = f*deg_p
   deg_q <= d && push!(fin_places, q) #TODO: sort by degree e.g. using Dict
  end
 end
 inf_ord = infinite_maximal_order(F)
 inf_places = []
 t_inv = gen(base_ring(inf_ord))
 inf_dec = prime_decomposition(inf_ord, t_inv)
 for (q,e) in inf_dec
  degree(q) <= d && push!(inf_places, q) #deg of inf place = 1, so f<=d enough?
 end
 return FactorBase(unique(fin_places)), FactorBase(unique(inf_places))
end

function gcd(a::T, b::T) where T<:Hecke.GenOrdIdl
 return a+b
end


function irred_polys(R::FqPolyRing, d::Int)
 t = gen(R)
 Fq = base_ring(R)
 q = length(Fq)
 Fq_elems = collect(Fq)
 I = [t+c for c in Fq]
 for i = 2:d
  for j = 0:q^d-1
   idces = digits(j, base=q, pad=d)
   coeffs = vcat([Fq(1)],[Fq_elems[idx+1] for idx in idces])
   g = R(coeffs)
   is_irreducible(g) && push!(I, g)
  end
 end
 return I
end


################################################################################
#
#  Examples
#
################################################################################

function test_fp()
 kt, t = rational_function_field(GF(13), "t")
 ktx, x = kt[:x]
 F, a = function_field(x^3+3*x*t+t^2+1, :a)
 return rational_primes(F)
end

function test_fq()
 kt, t = rational_function_field(GF(2,3), "t")
 ktx, x = kt[:x]
 F, a = function_field(x^3+3*x*t+t^2+1, :a)
 return rational_primes(F)
end






#=#PrimeIdealsSet PrimesSet prime_ideals_over IdealSet prime_ideals_up_to
kt, t = rational_function_field(GF(13), "t")
ktx, x = kt[:x]
F, a = function_field(x^3+3*x*t+t^2+1, :a)
I = integral_closure(parent(numerator(t)), k)
basis(ans)
integral_closure(localization(kt, degree), F)
basis(ans)

M_fin = finite_maximal_order(F)
prime_decomposition(M_fin, numerator(t+2))
Hecke.divisor(ans[1][1])


F = function_field(x^3+3*x*t+t^2+1, :a)
fi = infinite_maximal_order(F)
base_ring(fi)
gen(ans)
prime_decomposition(fi, ans)
degree(ans[1][1])
=#


#PrimeIdealsSet PrimesSet prime_ideals_over IdealSet prime_ideals_up_to

#=
function prime_ideals_over(O, lp)
 r = []
 for p in lp
  p_dec = prime_decomposition(O, numerator(p))
 end
 for P in p_dec
  push!(r, P[1])
 end
 return r
end
=#



#FactorBase: HeckeTypes, NumFieldOrd/NfOrd/Clgp