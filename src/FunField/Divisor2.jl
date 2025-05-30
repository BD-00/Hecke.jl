AbstractAlgebra.add_verbosity_scope(:Divisor2)
AbstractAlgebra.set_verbosity_level(:Divisor2, 0)

AbstractAlgebra.add_assertion_scope(:Divisor2)
AbstractAlgebra.set_assertion_level(:Divisor2, 0)

mutable struct RiemannRochCtx
 RR_basis::Vector{Generic.FunctionFieldElem}
 basis_gens::Vector{Generic.FunctionFieldElem}
 d_limit::Vector{Int}
 function RiemannRochCtx()
    return new([],[],[])
  end
end

#Extends RR-basis of D to RR-basis of D+r*(x)_infty. If r=0, we compute riemann_roch_space(D).
function _riemann_roch_space(D::Divisor, r=0, RR_Ctx=RiemannRochCtx())
 F = function_field(D)
 x = gen(base_ring(F))
 if iszero(r)
  I_fin, I_inf = ideals(D)
  J_fin = inv(I_fin)
  J_inf = inv(I_inf)

  F = function_field(D)
  x = gen(base_ring(F))
  n = degree(F)

  basis_gens = basis(J_fin) #basis over fin max order

  B_fin = matrix(map(coordinates, basis_gens)) #gens of basis elems over k(x)
  B_inf = matrix(map(coordinates, basis(J_inf)))

  M = solve(B_inf, B_fin; side = :left) #basis trafo in k(x)
  d = lcm(vec(map(denominator,collect(M))))
  d_deg = degree(d)
  Mnew = change_base_ring(parent(d), d*M) #embedding of M in F with denom scaled to 1

  T, U = weak_popov_with_transform(Mnew) #row transformation s.th. T = U*Mnew reduced

  RR_Ctx.basis_gens = change_base_ring(F, U) * basis(J_fin) #reduced basis_gens ???
  RR_Ctx.RR_basis = Generic.FunctionFieldElem[]
  empty!(RR_Ctx.d_limit)

  for i in (1:n)
    d_i = maximum(map(degree, T[i,1:n])) #max degree in i-th row
    d_l = - d_i + d_deg
    push!(RR_Ctx.d_limit, d_l)
    for j in (0:d_l)
      push!(RR_Ctx.RR_basis, x^(j) * RR_Ctx.basis_gens[i])
    end
  end
  return RR_Ctx.RR_basis, RR_Ctx
 else
  if r>0
   len = length(RR_Ctx.d_limit)
   new_basis = sizehint!(Generic.FunctionFieldElem[], length(RR_Ctx.RR_basis) + len*r)
   k = 0
   for i in (1:len)
    #insert part of basis belonging to v_i
    d_i = RR_Ctx.d_limit[i]
    for l in (0:d_i)
     k+=1
     push!(new_basis, RR_Ctx.RR_basis[k])
    end
    for j in (1:r)
     _exp = d_i+j
     is_zero(_exp) && push!(new_basis, RR_Ctx.basis_gens[i])
     _exp > 0 && push!(new_basis, x*new_basis[end])
    end
    RR_Ctx.d_limit[i]+=r
   end
   RR_Ctx.RR_basis = new_basis
   return new_basis, RR_Ctx
  else #r<0
   new_basis = sizehint!(Generic.FunctionFieldElem[], length(RR_Ctx.RR_basis))
   for i in 1:length(RR_Ctx.d_limit)
    _lim = RR_Ctx.d_limit[i]+r
    _lim >=0 && push!(new_basis, RR_Ctx.basis_gens[i])
    for j in (1:_lim)
     push!(new_basis, x*new_basis[end])
    end
    RR_Ctx.d_limit[i] = _lim
   end
   RR_Ctx.RR_basis = new_basis
   return new_basis, RR_Ctx
  end
 end
end

function divisor_reduction(D::Divisor, A::Divisor, m=0)
 @req !iszero(D) "D is zero"
 F = D.function_field
 Ofin = finite_maximal_order(F)
 Oinf = infinite_maximal_order(F)
 
 # "binary" decomposition of D with reduced support
 supp = support(D)
 exp = [s[2] for s in supp] #TODO: just subtract 2^iD_i instead

 #values always positive?
 if isempty(D.finite_support)
  m = maximum(values(D.infinite_support))
 elseif isempty(D.infinite_support)
   m = maximum(values(D.finite_support))
 else
  m = max(maximum(values(D.finite_support)), maximum(values(D.infinite_support)))
 end
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
      D_i, l_j, b = Hecke.maximal_reduction(D_i + Hecke.divisor(supp[j][1]), A, m)
      push!(Princ_B[i], b)
      r+=two_pow*l_j
     end
   end
   D_tilde, r_i, Princ_A[i] = maximal_reduction(2*D_tilde + D_i, A, m)
   r+=two_pow*r_i
 end
 return D_tilde, r, Princ_A, Princ_B
end


function divisor_reduction2(D::Divisor, A::Divisor, m=0)
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
        Dec[i], l, b = Hecke.maximal_reduction(Dec[i] + Hecke.divisor(supp[j][1]), A, m)
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
  D_tilde, R[i], Princ_A[i] = maximal_reduction(2*D_tilde + Dec[i], A, m)
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
#TODO: case deg(D) <= 0
#TODO: check if input already max. reduced ?
#TODO: RR computation more efficient
#TODO estimate the size of r and adapt step sizes to it
function maximal_reduction(D::Divisor, A::Divisor, m = 0)
  @req !iszero(D) "Divisor is zero."
  @req degree(A)>0 "Reduction only with divisor of degree > 0."
  #@show d = degree(D) #relevant for cases, or use dimension?
  
  r = 0
  D_tilde = D
  dim_tilde = dimension(D_tilde)
  if dim_tilde > 0
   D_next = D_tilde - 10*A
   while dimension(D_next) > 0
     D_tilde = D_next
     D_next -= 10*A
     r += 10
   end
  else
   while iszero(dim_tilde)
    D_tilde += 10*A
    dim_tilde = dimension(D_tilde)
    r -= 10
   end
  end

  while dimension(D_tilde - A) > 0
   D_tilde -= A
   r += 1
  end
  
#= binary search works, but not efficient for small examples
  current = r # dimension > 0
  next = r + s*10 # dimension 0
  mid = next
  diff = next - current
  while diff != s
    mid = div(next + current,2)
    diff = mid - current
    @show current, mid, next, diff, r
    if dimension(D_tilde - diff*A) > 0
      current = mid
      D_tilde -= diff*A
      r += s*diff
    else 
      next = mid
    end
  end
  =#
  RRSp = riemann_roch_space(D_tilde)
  a = divisor(RRSp[1])
  D_tilde+=a
  if !iszero(m)
   @assert m >= degree(A)
   #up = floor(Int, div(genus(D.function_field)+m-1-degree(D_tilde),m))
   #for j = 0:up
   j = 0
   while dimension(D_tilde + A) <= m
    j+=1
    D_tilde += A
    r -= j
   end
  end
  return D_tilde, r, a
end

function maximal_reduction(D::Divisor, m=0)
 #max reduction with (x)_infty
 F = function_field(D)
 A = pole_divisor(Hecke.separating_element(F))
 @req !iszero(D) "Divisor is zero."
 RR, RRCtx = _riemann_roch_space(D)
 r = maximum(RRCtx.d_limit)
 RR_red, RRCtx = _riemann_roch_space(D, -r, RRCtx)
 @assert RR_red == riemann_roch_space(D-r*A)
 @assert length(RR_red) > 0
 a = divisor(RR_red[1])
 D_tilde = D-r*A+a
 #RR_tilde = RR_red.*inv(RR[1])
 if !iszero(m)
  @assert m >= degree(A)
  d = RRCtx.d_limit
  _ones = ones(Int, length(d))
  d += _ones
  j = 0
  while sum(filter(x->x>0, d+=_ones)) <= m
   j+=1
   r -= j
  end
 end
 return D_tilde, r, a
end

function maximal_reduction_ideals(D::Divisor, A::Divisor, m = 0)
 @req !iszero(D) "Divisor is zero."
 @req degree(A)>0 "Reduction only with divisor of degree > 0."
 #@show d = degree(D) #relevant for cases, or use dimension?
 ID, JD = ideals(D)
 IA, JA = ideals(A)
 r = 0
 I, J = ID, JD
 D_tilde = D
 dim_tilde = dimension(D)
 if dim_tilde > 0
  In, Jn = I//IA^10, J//JA^10
  while dimension(Hecke.divisor(In, Jn)) > 0
    I, J = In, Jn
    In, Jn = In//IA^10, Jn//JA^10
  end
 else
  while iszero(dim_tilde)
   I, J = I*IA^10, J*JA^10
   D_tilde = Hecke.divisor(I, J)
   dim_tilde = dimension(Hecke.divisor(I, J))
   r -= 10
  end
 end

 
 In, Jn = I//IA, J//JA
 D_next = Hecke.divisor(In, Jn)
 while dimension(D_next) > 0
   D_tilde = D_next
   I, J = In, Jn
   In, Jn = In//IA, Jn//JA
   D_next = Hecke.divisor(In, Jn)
 end
 
 RRSp = riemann_roch_space(D_tilde)
 a = divisor(RRSp[1])
 Ia, Ja = ideals(a)
 D_tilde = Hecke.divisor(I*Ia, J*Ja)
 if !iszero(m)
  @assert m >= degree(A)
  #up = floor(Int, div(genus(D.function_field)+m-1-degree(D_tilde),m))
  #for j = 0:up
  j = 0
  In, Jn = I*IA, J*JA
  D_next = Hecke.divisor(In, Jn)
  while dimension(D_next) <= m
   j+=1
   D_tilde = D_next
   In, Jn = In*IA, Jn*JA
   D_next = Hecke.divisor(In, Jn)
   r -= j
  end
 end
 return D_tilde, r, a
end


#TODO: try only test with polys
#TODO: don't separate support
#TODO: schauen wo Zeit reingeht
#TODO: poly FB
#TODO: relations with deg >1 false
#TODO: make Rel_mat sparse
#TODO: consider fin annd inf support together
#TODO: test if creation + addition of two sparse rows cheaper or adding elements to one using minus before

function class_group_naive(F::AbstractAlgebra.Generic.FunctionField)
 Ofin = finite_maximal_order(F)
 A = pole_divisor(Hecke.separating_element(F)) # =(t)_infty
 A_supp = support(A)
 deg_A = degree(A)
 
 #compute degree bound as in Hess, Satz 3.16
 #=
 g = genus(F)
 q = characteristic(base_ring(F)) #TODO: get int
 d = ceil(Int, 2*log(Int(q), 4*g-2))
 =#
 d = 1

 #Factorbases and lists of finite ideals resp. norms
 fin_polys, fin_primes = Hecke.fin_prime_ideals(F, d)
 inf_primes = collect(s[1] for s in A_supp)

 m = length(fin_primes)
 n = length(inf_primes)
 #Find relations:

 #Initialize relation matrix
 #@show l = floor(Int, 1.5*(m+n))
 l = 2*(m+n)
 Rel_mat = sparse_matrix(ZZ, 0, m+n)
 counter = 0 #TODO upper bound using smoothness prob

 while length(Rel_mat) <= l

  #Find Divisor D as linear combination of primes.
  counter +=1
  #@show length(Rel_mat)
  _pos = sort!(unique!(rand(1:m, min(m, 3))))
  len_pos = length(_pos)
  _val = rand(-5:-1, len_pos)
  #@show _val
  @assert length(_val) == len_pos
  I = ideal(one(Ofin))
  for j = 1:len_pos  #TODO: dependence to number of fin primes
   idx = _pos[j]
   I*= fin_primes[idx]^-_val[j]
  end
  D = Hecke.divisor(I)
  #remove later since expensive
  @assert is_effective(D)
  @assert isempty(Hecke.infinite_support(D))

  #Reduce D
  D_tilde, r, a = Hecke.maximal_reduction(D, A, deg_A)
  @show r
  iszero(r) && continue
  #@show "after max_reduction"
  @assert is_effective(D_tilde)
  _bool, _row = Hecke.is_relation3_sp(D_tilde, fin_primes, inf_primes)
  if _bool
   for j = 1:n
    push!(_pos, m+j)
    push!(_val, r*A_supp[j][2])
   end
   Hecke.add_scaled_row!(sparse_row(ZZ, _pos, _val), _row, one(ZZ)) #D_tilde-D+r*A
   push!(Rel_mat, _row)
   #A_row = sparse_row(ZZ, collect(m+1:m+n), [r*A_supp[j][2] for j = 1:n])
  end
 end
 #TODO: SNF, check if enough rels
 return counter, m, n, Rel_mat
end

function class_group_sparse(F::AbstractAlgebra.Generic.FunctionField)
 Ofin = finite_maximal_order(F)
 A = pole_divisor(Hecke.separating_element(F)) # =(t)_infty
 A_supp = support(A)
 deg_A = degree(A)

 #compute degree bound as in Hess, Satz 3.16
 #=
 g = genus(F)
 q = characteristic(base_ring(F)) #TODO: get int
 d = ceil(Int, 2*log(Int(q), 4*g-2))
 =#
 d = 1

 #Factorbases and lists of finite ideals resp. norms
 fin_polys, fin_primes = Hecke.fin_prime_ideals(F, d)
 inf_primes = [p for (p,e) in A_supp]

 m = length(fin_primes)
 n = length(inf_primes)
 #Find relations:

 #Initialize relation matrix
 #@show l = floor(Int, 1.5*(m+n))
 @show l = 2*(m+n)
 Rel_mat = sparse_matrix(ZZ, 0, m+n)
 counter = 0 #TODO upper bound using smoothness prob

 while length(Rel_mat) <= l

  #Find Divisor D as linear combination of primes.
  counter +=1
  #@show length(Rel_mat)
  #_pos = sort!(unique!(rand(1:m, min(m, 3))))
  _pos = sort!(unique!(rand(1:m, floor(Int, 0.2*m+2))))
  len_pos = length(_pos)
  _val = rand(-8:-1, len_pos)
  #@show _val
  @assert length(_val) == len_pos
  I = ideal(one(Ofin))
  for j = 1:len_pos  #TODO: dependence to number of fin primes
   idx = _pos[j]
   I*= fin_primes[idx]^-_val[j]
  end
  D = Hecke.divisor(I)
  #remove later since expensive
  @assert is_effective(D)
  @assert isempty(Hecke.infinite_support(D))

  #Reduce D
  D_tilde, r, a = Hecke.maximal_reduction(D, A, deg_A)
  @show r
  iszero(r) && continue
  #@show "after max_reduction"
  #@assert is_effective(D_tilde)
  _bool, _row = Hecke.is_relation3_sp(D_tilde, fin_primes, inf_primes)
  if _bool
   for j = 1:n
    push!(_pos, m+j)
    push!(_val, r*A_supp[j][2])
   end
   Hecke.add_scaled_row!(sparse_row(ZZ, _pos, _val), _row, one(ZZ)) #D_tilde-D+r*A
   push!(Rel_mat, _row)
   @show length(Rel_mat)
   #A_row = sparse_row(ZZ, collect(m+1:m+n), [r*A_supp[j][2] for j = 1:n])
  end
 end
 #TODO: SNF, check if enough rels
 return counter, m, n, Rel_mat
end

function class_group_dense(F::AbstractAlgebra.Generic.FunctionField)
 Ofin = finite_maximal_order(F)
 Oinf = infinite_maximal_order(F)
 t = gen(base_ring(Ofin)) #element in k(t)
 A = pole_divisor(F(t)) # =(t)_infty
 #A = Hecke.divisor(prime_decomposition(Oinf, base_ring(Oinf)(1//t))[1][1])
 @assert iszero(Hecke.finite_support(A))
 A_supp = support(A)
 deg_A = degree(A)

 #compute degree bound as in Hess, Satz 3.16
 #=
 g = genus(F)
 q = characteristic(base_ring(F)) #TODO: get int
 d = ceil(Int, 2*log(Int(q), 4*g-2))
 =#
 d = 1
 #Factorbases and lists of finite ideals resp. norms
 fin_polys, fin_primes = Hecke.fin_prime_ideals(F, d)

 inf_primes = [p for (p,e) in A_supp]


 m = length(fin_primes)
 n = length(inf_primes)
 #Find relations:

 #Initialize relation matrix
 #l = ceil(Int, 1.5*(m+n))
 l = 2*(m+n)
 Rel_mat = ZZMatrix(l, m+n)
 counter = 0 #TODO upper bound using smoothness prob
 i = 1
 while i <= l
  #Find Divisor D as linear combination of primes.
  counter +=1
  #@show i
  v = zeros(ZZ, m)
  #D = trivial_divisor(F)
  I = ideal(one(Ofin))
  for j = 1:3 #TODO: dependence to number of fin primes
   idx = rand(1:m)
   e = rand(1:5)
   v[idx] += e
   I*= fin_primes[idx]^e
  end
  D = Hecke.divisor(I)
  @assert is_effective(D)
  @assert isempty(Hecke.infinite_support(D))
  #Reduce D
  D_tilde, r, a = Hecke.maximal_reduction(D, A, deg_A)
  @show r
  iszero(r) && continue
  #@show "after max_reduction"
  @assert is_effective(D_tilde)
  _bool, _row = Hecke.is_relation3(D_tilde, d, fin_primes, inf_primes)
  if _bool
   Rel_mat[i, :] += _row #D_tilde
   Rel_mat[i, 1:m] -= v #D
   for j = 1:n
    Rel_mat[i, m+j] += ZZ(r)*A_supp[j][2]
   end
   #@show test_relation3(a, Rel_mat[i, :], fin_primes, inf_primes, Ofin, Oinf)
   i+=1
  end
 end
 #TODO: SNF, check if enough rels
 return counter, m, n, Rel_mat
end

function is_relation2(D_tilde, fin_primes, inf_primes)#slower than sp_3
 _pos = Int[]
 _val = Int[]
 #D0 = Hecke.finite_divisor(D_tilde)
 I = D_tilde.finite_ideal
 len_fin = length(fin_primes)
 len_inf = length(inf_primes)

 for i = 1:len_fin
  P = fin_primes[i]
  #vp = valuation(D0, P)
  vp = valuation(D_tilde, P)
  if !iszero(vp)
    push!(_pos, i)
    push!(_val, vp)
    I = I//(GenOrdFracIdl(P)^vp)
  end
 end
 #!iszero(D0) && return false, sparse_row(ZZ)
 !isone(I) && return false, sparse_row(ZZ)
 #assumed that all infinite primes in factorbase
 for j = 1:len_inf
  Q = inf_primes[j]
  vq = valuation(D_tilde, Q)
  if !iszero(vq)
    push!(_pos, len_fin+j)
    push!(_val, vq)
  end
 end
 return true, sparse_row(ZZ, _pos, _val)
end

function is_relation3(D_tilde, d, fin_primes, inf_primes)
 len_fin = length(fin_primes)
 len_inf = length(inf_primes)
 _val = zeros(ZZ, len_fin+len_inf)

 for (p, e) in finite_support(D_tilde)
  !(p in fin_primes) && return false, _val
 end

 for i = 1:len_fin
  P = fin_primes[i]
  vp = valuation(D_tilde, P)
  if !iszero(vp)
   _val[i] = ZZ(vp)
  end
 end

 for j = 1:len_inf
  Q = inf_primes[j]
  vq = valuation(D_tilde, Q)
  if !iszero(vq)
   _val[len_fin + j] = ZZ(vq)
  end
 end
 return true, _val
end

function is_relation3_sp(D_tilde, fin_primes, inf_primes)
 len_fin = length(fin_primes)
 len_inf = length(inf_primes)
 len = len_fin + len_inf
 _pos = Int[]
 _val = Int[]

 for (p, e) in finite_support(D_tilde)
  !(p in fin_primes) && return false, sparse_row(ZZ)
 end

 for i = 1:len_fin
  P = fin_primes[i]
  vp = valuation(D_tilde, P)
  if !iszero(vp)
   push!(_pos, i)
   push!(_val, vp)
  end
 end

 for j = 1:len_inf
  Q = inf_primes[j]
  vq = valuation(D_tilde, Q)
  if !iszero(vq)
   push!(_pos, len_fin+j)
   push!(_val, vq)
  end
 end
 return true, sparse_row(ZZ, _pos, _val)
end

function is_relation_ord(D_tilde, fin_polys, fin_primes, inf_primes)

end 

function test_relation3(a, _val, fin_primes, inf_primes, Ofin, Oinf)
 m = length(fin_primes)
 n = length(inf_primes)
 @assert length(_val) == n+m
 I = ideal(one(Ofin))
 J = ideal(one(Oinf))
 for i = 1:m
  I*=fin_primes[i]^Int(_val[i])
 end
 for j = 1:n
  J*=inf_primes[j]^Int(_val[m+j])
 end
 D = Hecke.divisor(I, J)
 return a == D
end
#Idea: save primes to poly and _norms that st smoothness,
#then check primes only to corresp._norms

height(D::Divisor) = degree(zero_divisor(D)) + degree(pole_divisor(D))

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

function test_maxreduction(D_tilde, r, a, D, A, m=0)
 if D == D_tilde + r*A -a
   println("equality fulfilled")
 else 
  println("equality not fulfilled")
 end
 is_effective(D_tilde) ? println("D_tilde effective") : println("D_tilde not effective")
 is_principal(a) ? println("a is principal") : ("a is NOT principal")
 dim_tilde = dimension(D_tilde)
 if iszero(dim_tilde) 
  println("too far reduced")
 elseif iszero(m)
  iszero(dimension(D_tilde-A)) ? println("max reduced") : println("NOT max reduced")
 else
  dimension(D_tilde+A) > m ? println("min reduced") : println("NOT min reduced")
 end

 deg_A = degree(A)
 if iszero(m)
  dim_tilde <= deg_A ? println("dimension bounded correctly") : println("dimension bounded INcorrectly")
 else
  dim_tilde <= m ? println("dimension bounded correctly") : println("dimension bounded INcorrectly")
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
#genus(F)
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
(1)
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
A = Hecke.divisor(l_inf[1][1]*l_inf[2][1]^2)
deg 4 -> 10 fin primes

(2)
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(t^2+2)x^2+(2t^2+2)x+2)
deg 2 -> 4 endl Primideale

(3)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(t^2+2t+2)x^2+(t+2)x+2)

(4)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(3t+4)x^2+2x+1)

(5)
k = GF(7)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(2t+3)x^2+1)

(6) way too slow
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+2x^3+(2t^2+3t+4)x+1)

(7)
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(8t^2+t)x^2+(6t^2+3t+3)x+8)
Z/2 x Z/134 x Z

(8)
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+(10t^2+7t+1)x^2+(2t^2+8t+5)x+7)

(9)
k = GF(17)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^3+2x^2+(6t^2+14t+6)x+10t^2+10t+1)

(10)
k = GF(9)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+2x^3+(2t+1)x^2+2x+1)

(11)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+(2t+3)x^3+x^2+(3t+2)x+1)

(12)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+2x^3+(3t+2)x^2+x+2)

(13)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+(2t+3)x^3+x^2+1)

(14)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+(2t+3)x^3+(t+1)x^2+(4t+3)x+1)

(15)
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4+(2t+3)x^3+(3t+2)x^2+(4t+5)x+1)

(16)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^5+(2t+3)x^2+3x+1)
=#

#=
Parameterabfragen
A = pole_divisor(F(t))
suppA = support(A)

_polys, _primes = Hecke.fin_rat_primes(F)
_, FB = Hecke.fin_prime_ideals(F, 3)
length(FB)

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

#Klassenzahl zu klein -> falsche Relationen