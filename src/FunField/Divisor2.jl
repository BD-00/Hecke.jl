function divisor_reduction(D::Divisor, A::Divisor)
  #TODO: orders probably not necessary
  F = D.function_field
  Ofin = finite_maximal_order(F)
  Oinf = infinite_maximal_order(F)

  # "binary" decomposition of D
  Dec = Divisor[]
  fin_supp = Hecke.finite_support(D)
  inf_supp = Hecke.infinite_support(D)
  fin_exp = [s[2] for s in fin_supp]
  inf_exp = [s[2] for s in inf_supp]
  m = max(maximum(values(D.finite_support)), maximum(values(D.infinite_support)))
  m = floor(Int, log(2,m))
  for i = m:-1:0
    Dfin = ideal(Ofin, one(Ofin))
    if !isempty(fin_supp)
      for j = 1:length(fin_supp)
        d, rem = divrem(fin_exp[j], 2^i)
        if !iszero(d)
         fin_exp[j] = rem 
         Dfin *= fin_supp[j][1]
        end
      end
    end
    
    Dinf = ideal(Oinf, one(Oinf))
    if !isempty(inf_supp)
      for j = 1:length(inf_supp)
        d, rem = divrem(inf_exp[j], 2^i)
        if !iszero(d)
         inf_exp[j] = rem
         Dinf *= inf_supp[j][1]
        end
      end
    end
    push!(Dec, divisor(Dfin, Dinf))
  end
  #return Dec

  #support reduction
end

@doc raw"""
    maximal_reduction(D::Divisor, A::Divisor) -> Tuple{Divisor, Int}

Return a divisor D_tilde, r \in \mathbb{Z} and a principal divisor (a) 
s.th. D_tilde = D - rA + (a) is reduced maximally along A. 
Note that a unique reduction is only guaranteed if deg(A) = 1.
"""

#TODO: choose r depending on some invariant
function maximal_reduction(D,A)
  @req dimension(D)>0 "Input has dimension zero."
  d = degree(D)
  #deg_A = degree(A)
  if d<0 
    s = -1 # add multiples of A
  else 
    s = 1 # subtract multiples of A
  end
  r = 0
  D_tilde = D
  while dimension(D_tilde - s*10*A) > 0
    D_tilde -= s*10*A
    r += s*10
  end

  lower = r - s*10 # dimension 0
  upper = r # dimension > 0
  mid = div(lower + upper,2) 
  while mid < upper -s #TODO
    diff = upper - mid
    if dimension(D_tilde - diff*A) > 0
      upper = mid
      D_tilde -= diff
    else 
      lower = mid
    end
  end
  return D_tilde, r, D_tilde - D + r*A
end

function height(D::Divisor)
  @req !iszero(D) "Divisor is zero."
  zero_div = zero_divisor(D)
  pole_div = pole_divisor(D)
  h = 0
  !iszero(zero_div) && h+= degree(zero_div)
  !iszero(pole_div) && h+= degree(pole_div)
 return h
end

################################################################################
#
#  Tests
#
################################################################################

function test_reduction(D, Dec)
 m = length(Dec)-1
 D_sum = Dec[end]
 for i = m:-1:1
  D_sum += 2^i*Dec[m-i+1]
 end
 return D_sum == D
end



################################################################################
#
#  Examples
#
################################################################################

#=
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+x+t+2)
MF = finite_maximal_order(F)
MI = infinite_maximal_order(F)
lp = prime_decomposition(MF, numerator(t+1))

I = lp[2][1]^5
Iinv = inv(I)
B = basis_matrix(Iinv)
n, d = integral_split(B, base_ring(MF))
popov(n)
a = MF(ans[1,:])
a * I
divexact(basis_matrix(ans), d)


F, a = function_field(x^3+x+(t^2+2)//(t^3+t+1))
minpoly(a*(t^2+t+2))
F, a = function_field(ans)
MF = finite_maximal_order(F)
MI = infinite_maximal_order(F)
genus(F)
lp = prime_decomposition(MF, numerator(t+1))
lq = prime_decomposition(MF, numerator(t+3))
I = lp[2][1]^10*lq[1][1]^7
Iinv = inv(I)
B = basis_matrix(Iinv)
n, d = integral_split(B, base_ring(MF))
popov(n)
a = MF(ans[1,:])
a * I
divexact(basis_matrix(ans), d)
ideal(MF, ans)


l_inf = prime_decomposition(MI, base_ring(MI)(1//t))
D = Hecke.divisor(I, l_inf[2][1]^3)
A = Hecke.divisor(l_inf[1][1])

#=
julia> dimension(D-14*A)
1

julia> dimension(D-15*A)
0

julia> r = 14
14
=#

r = 14

riemann_roch_space(D-r*A)
a = ans[1]
D_tilde = D-r*A+Hecke.divisor(a)



Examples Hess S.82 ff.
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(2t+1)x^2+(2t^3+t^2+t+1)x+t^2+2)
Ofin = finite_maximal_order(F)
Oinf = infinite_maximal_order(F)

=#


#=
Look into:
class_group_ideal_relation
=#