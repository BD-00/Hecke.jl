k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(3t+4)x^2+2x+1)

#for any function field F/k:
Ofin = finite_maximal_order(F)
Oinf = infinite_maximal_order(F)
kt = base_ring(F) #Fq(t)
t = numerator(gen(kt))
dec = prime_decomposition(Ofin, t+1)
P = dec[1][1]

dec_t = prime_decomposition(Ofin, t^5+t^2+2)
Q = dec_t[1][1] #-> assertion error with gens for k > 5 (i=11, j = 2 in group_extension)
#-> does not split or ramify
#two elem rep with equal generators

gen_inf = gen(base_ring(Oinf))
dec_inf = prime_decomposition(Oinf, gen_inf)
Pinf = dec_inf[2][1]

#find mistake in one_unit_quotient_a_b(Pinf, 2) -> trivial group atm
P = Pinf
G, iso, gens = Hecke.one_unit_quotient_a_b(P, 1, 2)

#modulus
m = Hecke.divisor(P^3*Q^2, Pinf^2)


_gens_right, _rels_right = Hecke.one_unit_quotient(P, 4)
a = 4
b = 6
_gens, _rels = Hecke.group_extension(P, a, b, _gens_right, _rels_right)





k2 = GF(8)
ks, s = rational_function_field(k2, "s")
ksy, y = polynomial_ring(ks, "y")
K, b = function_field(y^5-s-1)
OK = finite_maximal_order(K) #geht nicht für k = GF(25)
ks = base_ring(K)
s = numerator(gen(ks))
dec_s = prime_decomposition(OK, s)


#for any function field F/k:
Ofin = finite_maximal_order(F)
Oinf = infinite_maximal_order(F)
kt = base_ring(F) #Fq(t)
t = numerator(gen(kt))
dec = prime_decomposition(Ofin, t+1)
P = dec[1][1]


#weak approximation
#c = 3*_a^2 + 4*_a + 2*t^20 + 3*t^17 + t^15 + 2*t^14 + 3*t^12 + 3*t^11 + 3*t^10 + 3*t^9 + 2*t^8 + t^7 + t^6 + 4*t^5 + 3*t^4 + 4*t^2 + 4*t
c = 3*gen_P + 2*Q.gen_two -t
x = [mod(c, P^2), mod(c, Q^4)]
S = [P, Q]
r = [2, 4]

#modulus
m = Hecke.divisor(P^3*Q^2, Pinf^2)

#magma
#=
k := GF(25);
kt<t> := RationalFunctionField(k);
ktx<x> := PolynomialRing(kt);
kpoly<t> := PolynomialRing(k);
F<a> := FunctionField(x^3 + (3*t + 4)*x^2 + 2*x + 1);
Ofin := MaximalOrderFinite(F);
Oinf := MaximalOrderInfinite(F);

p := t+1;
dec := Decomposition(Ofin, p);
P := dec[3];

dec_t := Decomposition(Ofin, t^5+t^2+2);
Q := dec_t[1];

Inf := InfinitePlaces(F);
Pinf := Inf[2];

M := Divisor(P^3 * Q^2)+2*Pinf;

R := RayResidueRing(M); 

Abelian Group isomorphic to Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 
+ Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/5 + Z/120 + Z/120 + Z/4656612873077392578120
2*Z/5 mehr als bei mir

#problem für k = 1
=#





#assertion error for P, k=10 (a=8, b=10, i=14):
_gens, _rels = Hecke.one_unit_quotient(P, 10)
_gens_right, _rels_right = Hecke.one_unit_quotient(P, 8)
a = 8
b = 10
_gens, _rels = Hecke.group_extension(P, a, b, _gens_right, _rels_right)
i = 14

G, R = Hecke.one_unit_quotient(P, 10)
#unit_quotient(P, 10) does not work, but unit_quotient(P,8) and group_extension(P, 8, 10) does