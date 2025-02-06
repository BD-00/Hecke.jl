function rational_primes(F::AbstractAlgebra.Generic.FunctionField{FqFieldElem})
 kt = F.base_ring #Fq(t)
 t = gen(kt)
 k = kt.base_ring #Fq

 I = [t+c for c in k] #irreducible polynomials of deg 1 over Fq
 fin_ord = finite_maximal_order(F)
 fin_places = []
 for p in I
  p_dec = prime_decomposition(fin_ord, numerator(p))
  for (p,e) in p_dec
   isone(degree(p)) && push!(fin_places, p_dec[1])
  end
 end
 inf_ord = infinite_maximal_order(F)
 inf_places = []
 t_inv = gen(base_ring(inf_ord))
 inf_dec = prime_decomposition(inf_ord, t_inv)
 for (p,e) in inf_dec
  isone(degree(p))&&push!(inf_places, p)
 end
 return fin_places, inf_places
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