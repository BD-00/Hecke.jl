AbstractAlgebra.add_verbosity_scope(:Divisor2)
AbstractAlgebra.set_verbosity_level(:Divisor2, 0)

AbstractAlgebra.add_assertion_scope(:Divisor2)
AbstractAlgebra.set_assertion_level(:Divisor2, 0)


function divisor_reduction(D::Divisor, A::Divisor)
 @req !iszero(D) "D is zero"
 F = D.function_field
 Ofin = finite_maximal_order(F)
 Oinf = infinite_maximal_order(F)
 
 # "binary" decomposition of D with reduced support
 supp = support(D)
 exp = [s[2] for s in supp] #TODO: just subtract 2^iD_i instead

 #values always positive?
 m = max(maximum(values(D.finite_support)), maximum(values(D.infinite_support)))
 m = floor(Int, log(2,m))
 D_tilde = Hecke.divisor(ideal(Ofin, one(Ofin)), ideal(Oinf, one(Oinf)))
 D_i = Hecke.divisor(ideal(Ofin, one(Ofin)), ideal(Oinf, one(Oinf)))
 r = 0
 Princ_A = [D_tilde for i = 1:m+1]
 Princ_B = [Array{Divisor}([]) for i = 1:m+1] #lists indexed descendingly
 for i = m+1:-1:1
  two_pow = 2^(i-1)
  D_i = Hecke.divisor(ideal(Ofin, one(Ofin)), ideal(Oinf, one(Oinf)))
   for j = 1:length(supp)
     d, rem = divrem(exp[j], 2^(i-1))
     if !iszero(d)
      exp[j] = rem 
      D_i, l_j, b = Hecke.maximal_reduction(D_i + Hecke.divisor(supp[j][1]), A)
      push!(Princ_B[i], b)
      r+=two_pow*l_j
     end
   end
   D_tilde, r_i, Princ_A[i] = maximal_reduction(2*D_tilde + D_i, A)
   r+=two_pow*r_i
 end
 return D_tilde, r, Princ_A, Princ_B
end


function divisor_reduction2(D::Divisor, A::Divisor)
 #TODO: case iszero(D)

 F = D.function_field
 Ofin = finite_maximal_order(F)
 Oinf = infinite_maximal_order(F)
 
 # "binary" decomposition of D with reduced support
 supp = support(D)
 exp = [s[2] for s in supp]
 Z = Hecke.divisor(ideal(Ofin, one(Ofin)), ideal(Oinf, one(Oinf)))
 #values always positive?
 m = max(maximum(values(D.finite_support)), maximum(values(D.infinite_support)))
 m = floor(Int, log(2,m))
 Dec = fill(Z, m+1)
 L = zeros(Int, m+1) #stores r_i for reduction of D_i
 Princ_B = [Array{Divisor}([]) for i = 1:m+1] #stores principal summand for each prime in D_i in list i
 for i = m+1:-1:1
   if !isempty(supp)
     for j = 1:length(supp)
       d, rem = divrem(exp[j], 2^(i-1))
       if !iszero(d)
        exp[j] = rem 
        Dec[i], l, b = Hecke.maximal_reduction(Dec[i] + Hecke.divisor(supp[j][1]), A)
        L[i] += l
        push!(Princ_B[i], b)
       end
     end
   end
 end
 #return Dec, L, B

 #TODO: do this along the previous reduction without saving Dec if possible
 # exponent reduction
 D_tilde = Hecke.divisor(ideal(Ofin, one(Ofin)), ideal(Oinf, one(Oinf)))
 R = zeros(Int, m+1)
 Princ_A = [D_tilde for i = 1:m+1]
 for i = m+1:-1:1
  D_tilde, R[i], Princ_A[i] = maximal_reduction(2*D_tilde + Dec[i], A)
 end
 r = 0
 for i=1:m+1
  r+=2^(i-1)*(R[i]+L[i])
 end
 return D_tilde, r, Princ_A, Princ_B
end

@doc raw"""
    maximal_reduction(D::Divisor, A::Divisor) -> Tuple{Divisor, Int}

Return a divisor D_tilde, r \in \mathbb{Z} and a principal divisor (a) 
s.th. D_tilde = D - rA + (a) is reduced maximally along A. 
Note that a unique reduction is only guaranteed if deg(A) = 1.
"""

#TODO: choose r depending on some invariant
function maximal_reduction(D::Divisor, A::Divisor)
  @req !iszero(D) "Divisor is zero."
  @req dimension(D)>0 "Dimension of divisor is zero."
  d = degree(D)
  #deg_A = degree(A)
  if d<0 
    s = -1 # add multiples of A
  else 
    s = 1 # subtract multiples of A
  end#
  #@show s
  r = 0
  D_tilde = D
  while dimension(D_tilde - s*10*A) > 0
    D_tilde -= s*10*A
    r += s*10
  end
  while dimension(D_tilde - s*A) > 0
   D_tilde -= s*A
   r += s
  end

  #TODO: fix binary search
  #=
  current = r # dimension > 0
  next = r - s*10 # dimension 0
  mid = next

  while current - mid != s
    @show current, mid
    mid = div(next + current,2) 
    diff = current - mid
    @show diff
    if dimension(D_tilde - diff*A) > 0
      current = mid
      D_tilde -= diff*A
      r += diff
    else 
      next = mid
    end
  end
  =#
  RRSp = riemann_roch_space(D_tilde)
  a = divisor(RRSp[1])
  D_tilde+=a
  return D_tilde, r, a
end

#=
function height(D::Divisor)
  @req !iszero(D) "Divisor is zero."
  zero_div = zero_divisor(D)
  pole_div = pole_divisor(D)
  h = 0
  !iszero(zero_div) && h += degree(zero_div)
  !iszero(pole_div) && h += degree(pole_div)
 return h
end
=#

################################################################################
#
#  Tests
#
################################################################################

function test_reduction(D, A, D_tilde, r, Princ_A, Princ_B)
 F = D.function_field
 Ofin = finite_maximal_order(F)
 Oinf = infinite_maximal_order(F)
 m = length(Princ_A)-1
 Princ = sum([2^(i-1)*(Princ_A[i]+sum(Princ_B[i])) for i = 1:m+1])
 return D == D_tilde + r*A -Princ
end

function test_maxreduction(D_tilde, r, a, D, A, check_deg = false)
 if D == D_tilde + r*A -a #TODO: not true for some reason
   println("equality fulfilled")
 else 
  println("equality not fulfilled")
 end
 is_effective(D_tilde) ? println("D_tilde effective") : println("D_tilde not effective")
 is_principal(a) ? println("a is principal") : ("a is NOT principal")
 dim_tilde = dimension(D_tilde)
 if iszero(dim_tilde) 
  println("too far reduced")
 else
  iszero(dimension(D_tilde-A)) ? println("max reduced") : println("NOT max reduced")
 end
 deg_A = degree(A)
 dim_tilde <= deg_A ? println("dimension bounded correctly") : println("dimension bounded INcorrectly")
 if check_deg
  g = genus(D_tilde.function_field)
  degree(D_tilde) < g + deg_A ? println("degree bounded correctly") : println("degree bounded INcorrectly")
 end
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

k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+x+(t^2+2)//(t^3+t+1))
minpoly(a*(t^2+t+2))
F, a = function_field(ans)
MF = finite_maximal_order(F)
MI = infinite_maximal_order(F)
genus(F)
lp = prime_decomposition(MF, numerator(t+1))
lq = prime_decomposition(MF, numerator(t+3))
ls = prime_decomposition(MF, numerator(t+5))

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
A = Hecke.divisor(ls[1][1])

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
lp = prime_decomposition(Ofin, numerator(t+1))
lq = prime_decomposition(Ofin, numerator(t+2))
ls = prime_decomposition(Ofin, numerator(t^2+t-1))
l_inf = prime_decomposition(Oinf, base_ring(Oinf)(1//t))
D = Hecke.divisor(lp[2][1]^2*lq[1][1]^3*ls[1][1]^5, l_inf[1][1]^11) #dim 26, deg 28
A = Hecke.divisor(lp[1][1])
=#

################################################################################
#
#  TODOs
#
################################################################################

#=
Look into:
class_group_ideal_relation
=#

#TODO: try reduction via ideals
#TODO: write function that outputs trivial divisor
#TODO: write function for 0*Divisor resp. I^0 = R?
#TODO: zero!(::Divisor)

