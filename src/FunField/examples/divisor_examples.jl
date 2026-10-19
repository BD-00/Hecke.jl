include("funfield_examples.jl")

K, x = rational_function_field(QQ, :x)
R, y = polynomial_ring(K, :y)

f = 167706*x^6 + 149072*x^5*y - 745360*x^5 - 335412*x^4*y^2 - 335412*x^4*y + 1097712*x^4 - 315084*x^3*y^3 + 111804*x^3*y^2 - 223608*x^3*y - 894432*x^3 + 367356*x^2*y^4 - 95832*x^2*y^3 - 371228*x^2*y^2 + 505560*x^2*y + 817518*x^2 + 249260*x*y^5 - 236214*x*y^4 - 20148*x*y^3 - 29838*x*y^2 + 271364*x*y - 234424*x - 71700*y^6 - 88544*y^5 + 78800*y^4 + 33368*y^3 + 318716*y^2 - 179816*y - 90824
F, a = function_field(f)

W = canonical_divisor(F)
A = pole_divisor(Hecke.separating_element(F))
D, r, a = Hecke.maximal_reduction(W)

#=
without binary search:
julia> @time D, r, a= Hecke.maximal_reduction(W, pole_divisor(Hecke.separating_element(F)));
 15.264694 seconds (3.82 M allocations: 1.609 GiB, 0.61% gc time)

binary search:
s = 1
julia> @time D, r, A = Hecke.maximal_reduction(W, A);
 12.231868 seconds (3.06 M allocations: 1.290 GiB, 0.40% gc time)
 =#

 #for examples in funfield_examples from 1:20:
for i in 1:20
  @eval $(Symbol("A", i)) = pole_divisor(Hecke.separating_element($(Symbol("F", i))))
  @eval $(Symbol("W", i)) = canonical_divisor($(Symbol("F", i)))
  @eval $(Symbol("D", i)), $(Symbol("r", i)), $(Symbol("a", i)) = Hecke.maximal_reduction($(Symbol("W", i)))
  #Hecke.test_maximal_reduction($(Symbol("W", i)), Hecke.maximal_reduction($(Symbol("W", i))))
end