function _rand_fin_div(F, fin_primes=Hecke.fin_prime_ideals(F, 1)[2])
 l = min(length(fin_primes), 3)
 I = ideal(one(finite_maximal_order(F)))
 for j = 1:l  #TODO: dependence to number of fin primes
  idx = rand(1:l)
  v = rand(1:10)
  I*= (fin_primes[idx])^v
 end
 return Hecke.divisor(I)
end

F = F1
fin_polys, fin_primes = Hecke.fin_prime_ideals(F, 1)
D = _rand_fin_div(F, fin_primes)
A = pole_divisor(Hecke.separating_element(F))
D_tilde, r, a = Hecke.maximal_reduction(D, A)
Hecke.test_maxreduction(D_tilde, r, a, D, A)