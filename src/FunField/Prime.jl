function rational_primes(F::AbstractAlgebra.Generic.FunctionField{FqFieldElem})
 kt = F.base_ring #Fp(t)
 t = gen(kt)
 k = kt.base_ring #Fp

 #collect irreducible polynomials of deg 1 over Fp
 Irred = [] #TODO: add type 
 for c in k
  push!(Irred, t+c)
 end
 fin_ord = finite_maximal_order(F)
 fin_places = []
 c = 0
 for p in Irred
  p_dec = prime_decomposition(fin_ord, numerator(p))
  #@show [(p[2], degree(p[1])) for p in p_dec]
  for p in p_dec
   c+=1
   #@show degree(p[1]), p[2]
   isone(degree(p[1])) && push!(fin_places, p_dec[1])
  end
 end
 return fin_places
 inf_ord = infinite_maximal_order(F)
end




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


#=
kt, t = rational_function_field(GF(13), "t")
ktx, x = kt[:x]
#F = function_field(x^3+3*x*t+t^2+1, :a)
F, a = function_field(x^3+3*x*t+t^2+1, :a)
I = integral_closure(parent(numerator(t)), k)
basis(ans)
integral_closure(localization(kt, degree), F)
basis(ans)

M_fin = finite_maximal_order(F)
prime_decomposition(M_fin, numerator(t+2))
Hecke.divisor(ans[1][1])

=#

#PrimeIdealsSet PrimesSet prime_ideals_over IdealSet prime_ideals_up_to