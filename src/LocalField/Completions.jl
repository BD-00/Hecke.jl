################################################################################
#
#  Functions for completion map
#
################################################################################

function image(f::CompletionMap, a::AbsSimpleNumFieldElem; pr::Int = precision(codomain(f)))

  if iszero(a)
    return zero(codomain(f))
  end
  Qx = parent(parent(a).pol)
  C = codomain(f)

  v = Int(valuation(denominator(a), minimum(f.P)))
  
#  if pr > 1000
#    error("ASD")
#  end

  old = f.precision

  if f.precision < pr + absolute_ramification_index(C)*v 
    setprecision!(f, pr + absolute_ramification_index(C)*v)
  end
  z = setprecision(C, precision(C)+absolute_ramification_index(C)*v) do
       evaluate(Qx(a), setprecision(f.prim_img, pr + absolute_ramification_index(C)*v))
  end

  if iszero(z) || valuation(z) < 0
    v = valuation(a, f.P)
    av = abs(v)
    b = a*uniformizer(f.P).elem_in_nf^-v

    e = absolute_ramification_index(C)

    vv = Int(valuation(denominator(b), minimum(f.P)))

    if pr +av + vv + e < f.precision
      setprecision!(f, pr +e*vv + av + e)
    end
    @assert parent(f.prim_img) === C
    @assert pr >= 0
    @assert pr+e*vv + av + e >= 0
    z = setprecision(C, pr+e*vv + av + e) do
      setprecision(base_field(C), ceil(Int, (pr+e*vv + av + e)/e)) do
         evaluate(Qx(b), setprecision(f.prim_img, min(f.precision, pr + e*vv  + av + e)))
      end
    end
    z *= uniformizer(parent(z), v; prec = pr)
  end

  if precision(z) < pr
    global last_in = (f, a, pr)
    error("ASD2")
    old_pr = f.precision
    setprecision!(f, 2*f.precision)
    @show :bad, pr, f.precision, precision(z)
    if f.precision > 1000
      @show precision(f.prim_img), precision(base_field(C))
      error("roo bad")
    end
    im = image(f, a; pr)
    setprecision!(f, old_pr)
    return im
  end
  if old != f.precision
    setprecision!(f, old)
  end

# should be multiplied(?) by the abs. or rel. ram index?
#  @assert valuation(z) == valuation(a, f.P)
  return z
end

function _small_lift(f::Map, a::AbsSimpleNumFieldElem, integral::Bool, precision::Int)
  if !haskey(f.lift_data, precision) 
    l = lll(basis_matrix(f.P^precision))
    f.lift_data[precision] = (l, solve_init(map_entries(QQ, l)))
  end
  lift_data = f.lift_data[precision]
  n = degree(domain(f))
  zk = order(f.P)
  @assert denominator(a, zk) == 1
  cc = matrix(ZZ, 1, n, coordinates(zk(a)))
  l = lift_data[1]
  if integral
    s = solve(lift_data[2], QQ.(cc))
    r = round.(ZZRingElem, s)
    cc -= r*l
    return domain(f)(order(f.P)(cc))
  end
  m = [ identity_matrix(ZZ, 1) cc; zero_matrix(ZZ, n, 1) l ]
  lll!(m)
  return domain(f)(order(f.P)(view(m, 1:1, 2:n+1))//m[1,1])
end

function preimage(f::CompletionMap{LocalField{QadicFieldElem, EisensteinLocalField}, LocalFieldElem{QadicFieldElem, EisensteinLocalField}}, a::LocalFieldElem{QadicFieldElem, EisensteinLocalField}; small_lift::Bool = false, integral::Bool = false)
  #Eisenstein/ qadic
  Kp = codomain(f)
  @assert Kp === parent(a)
  Qq = base_field(Kp)
  Qpx = parent(defining_polynomial(Qq))
  coeffs = Vector{AbsSimpleNumFieldElem}()
  #careful: we're working in a limited precision world and the lift
  #can be waaaay to large
  if iszero(a)
    return zero(domain(f))
  end
  if abs(valuation(a)) > 100
    global last_a = a
    error("elem too large")
  end
  pr = ceil(Int, min(f.precision, precision(a)) / ramification_index(Kp))
  for i = 0:degree(a.data)
    as_pol = Qpx(coeff(a.data, i))
    as_fmpq_poly = map_coefficients(x->lift(QQ, setprecision(x, min(precision(x), pr))), as_pol, cached = false)
    push!(coeffs, evaluate(as_fmpq_poly, f.inv_img[1]))
  end
  K = domain(f)
  Kx = polynomial_ring(K, "x")[1]
  r = Kx(coeffs)
  s = evaluate(r, f.inv_img[2])
  if small_lift
    return _small_lift(f, s, integral, precision(a))
  else
    return s
  end
end

function preimage(f::CompletionMap{LocalField{PadicFieldElem, EisensteinLocalField}, LocalFieldElem{PadicFieldElem, EisensteinLocalField}}, a::LocalFieldElem{PadicFieldElem, EisensteinLocalField}; small_lift::Bool = false, integral::Bool = false)
  #Eisenstein/ padic
  @assert codomain(f) === parent(a)
  s = evaluate(map_coefficients(x -> lift(ZZ, x), a.data, cached = false), f.inv_img[2])
  if small_lift
    return _small_lift(f, s, integral, precision(a))
  else
    return s
  end
end

function preimage(f::CompletionMap{QadicField, QadicFieldElem}, a::QadicFieldElem; small_lift::Bool = false, integral::Bool = false)
  #qadic only
  Kp = codomain(f)
  @assert Kp == parent(a)
  Qpx = parent(defining_polynomial(Kp))
  as_pol = Qpx(a)
  as_fmpq_poly = map_coefficients(x -> lift(ZZ, x), as_pol, cached = false)
  r = evaluate(as_fmpq_poly, f.inv_img[1])
  if small_lift
    return _small_lift(f, r, integral, precision(a))
  else
    return r
  end
end

function prime(f::CompletionMap)
  return f.P
end

################################################################################
#
#  Lifting
#
################################################################################

function _lift(a::AbsSimpleNumFieldElem, f::ZZPolyRingElem, prec::Int, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  i = prec
  chain = [i]

  while i > 2
    i = div(i+1, 2)
    push!(chain, i)
  end
  push!(chain, 2)
  der = derivative(f)
  bi = a
  F, mF = residue_field(order(P), P)
  wi = parent(a)(preimage(mF, inv(mF(der(order(P)(a))))))
  local minP2i::ZZRingElem
  for i in length(chain):-1:1
    ex, r = divrem(chain[i], ramification_index(P))
    if r > 0
      ex += 1
    end
    minP2i = minimum(P)^ex
    bi = bi - wi*f(bi)
    bi = mod(bi, minP2i)
    wi = wi*(2-wi*der(bi))
    wi = mod(wi, minP2i)
  end
  O = order(P)
  lp = prime_decomposition(O, minimum(P))
  v = [valuation(bi, p[1]) for p = lp]
  c = one(O)
  Q = P^prec
  for i=1:length(v)
    if v[i] < 0
      @assert lp[i][1] != P
      c = crt(c, Q, uniformizer(lp[i][1])^-v[i], lp[i][1]^(-v[i]+1))
      Q *= lp[i][1]^(-v[i]+1)
    end
  end
  bi *= c
  bi = mod(bi, minP2i)
  @assert denominator(bi, O) == 1

  return bi
end

function _mod_den(a::AbsSimpleNumFieldElem, p::ZZRingElem)
  da = denominator(a)
  b = coordinates(a*da)
  p *= da
  for i=1:length(b)
    b[i] = QQ(numerator(b[i]) % p)
  end
  return parent(a)(b)//da
end

function _increase_precision(a::AbsSimpleNumFieldElem, f::ZZPolyRingElem, prec::Int, new_prec::Int, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem})
  p = minimum(P)
  e = ramification_index(P)
  der = derivative(f)
  ia = inv(der(a))
  den = denominator(ia)
  pp, op = ppio(den, p)
  ia *= invmod(op, p^(prec+1))*op
  @assert denominator(ia) == pp
  # quad lifting:
  # val(f(a)) = k
  # val(f'(a)) = l
  # then lifting increases to 2*k-l
  # thus to reach new_prec = 2*k-l, the lifting needs to start at
  # (new_prec +l)/2
  #
  # we assume valuation(f'(a)) == l == 0 here

  @assert prec < new_prec
  i = new_prec 
  chain = [new_prec]
  while i > prec
    i = div(i+1, 2)
    pushfirst!(chain, max(i, prec))
  end
  
  local minP2i::ZZRingElem
  for i = 2:length(chain)
    ex = chain[i]
    
    minP2i = p^ex
    a = a - f(a)*ia
    ia = ia*(2-ia*der(a))
    a = _mod_den(a, minP2i)
    ia = _mod_den(ia, minP2i)
#    @assert valuation(f(a), P) >= chain[i-1]
  end

  O = order(P)
  lp = prime_decomposition(O, minimum(P))
  v = [valuation(a, p[1]) for p = lp]
  c = one(O)
  Q = P^prec
  for i=1:length(v)
    if v[i] < 0
      @assert lp[i][1] != P
      c = crt(c, Q, uniformizer(lp[i][1])^-v[i], lp[i][1]^(-v[i]+1))
      Q *= lp[i][1]^(-v[i]+1)
    end
  end
  a *= c
  a = mod(a, minP2i)
  @assert denominator(a, O) == 1


#  @show :snd, iszero(f(a)) ? -1 :  valuation(f(a), P), prec
  return a
end

################################################################################
#
#  Generic completion
#
################################################################################

function precision_all(K::Union{QadicField, <:LocalField}; init::Vector{Int}=Int[])
  push!(init, precision(K))
  return precision_all(base_field(K); init)
end

function precision_all(K::PadicField; init::Vector{Int}=Int[])
  push!(init, precision(K))
  return init
end

function setprecision_all!(K::Union{QadicField, <:LocalField}, pr::Vector{Int})
  setprecision!(K, popfirst!(pr))
  setprecision_all!(base_field(K), pr)
end

function setprecision_all!(K::PadicField, pr::Vector{Int})
  setprecision!(K, popfirst!(pr))
end

@doc raw"""
    completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int)
                                                    -> LocalField, CompletionMap

The completion of $K$ wrt to the topology induced by the valuation at $P$,
presented as a Eisenstein extension of an unramified p-adic field.

The map giving the embedding of $K$ into the completion, admits a pointwise
preimage to obtain a lift. Note, that the map is not well defined by this
data: $K$ will have $\deg P$ many embeddings.

The map is guaranteed to yield a relative precision of at least `preciscion`.
"""
function completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int = 64)
  #to guarantee a rel_prec we need to account for the index (or the
  #elementary divisor of the trace mat): the map
  #is for the field (equation order), the precision is measured in the
  #maximal order
  #also, precision in the unram part is counted differently, so
  #we might need to increase by one...
  OK = order(P)
  precision += valuation(denominator(basis_matrix(OK, copy = false)), P)
  @assert is_prime(P)
  @assert nf(OK) == K
  f = degree(P)
  e = ramification_index(P)
  prec_padics = div(precision+e-1, e)
  Qp = padic_field(minimum(P), precision = prec_padics, cached = false)
  Zp = maximal_order(Qp)
  Qq, gQq = qadic_field(minimum(P), f, precision = prec_padics, cached = false)
  Qqx, gQqx = polynomial_ring(Qq, "x")
  q, mq = residue_field(Qq)
  #F, mF = ResidueFieldSmall(OK, P)
  F, mF = residue_field(OK, P)
  mp = find_morphism(q, F)
  g = gen(q)
  gq_in_K = (mF\(mp(g))).elem_in_nf
  Zx = polynomial_ring(ZZ, "x", cached = false)[1]
  pol_gq = map_coefficients(x -> lift(ZZ, x),  defining_polynomial(Qq), cached = false)
  gq_in_K = _lift(gq_in_K, pol_gq, precision, P)
  #@assert mF(OK(gq_in_K)) == mp(g)

  #gq_in_K is PE of the residue field lifted to suitable precision
  #u is the PE of the ramified ext

  coeffs_eisenstein, xZp = _solve_internal(gq_in_K, P, precision, Zp, Qq)

  pol_gen = Qqx(coeffs_eisenstein)
  Kp, gKp = eisenstein_extension(pol_gen, "a", cached = false)
  img_prim_elem = Vector{QadicFieldElem}(undef, e)
  for i = 1:e
    coeff = Qq()
    for j = 0:f-1
      coeff += (gQq^j)*xZp[2, j+1+(i-1)*f].x
    end
    img_prim_elem[i] = coeff
  end
  img = Kp(Qqx(img_prim_elem))

  u = uniformizer(P).elem_in_nf
  completion_map = CompletionMap(K, Kp, img, (gq_in_K, u), precision)
  completion_map.P = P

  Kp.def_poly = function(x::Int)
    all_f = collect(values(Kp.def_poly_cache))
    @assert all(x->parent(x) === parent(all_f[1]), all_f)
    old_pr = Hecke.precision_all(Kp)
    setprecision!(completion_map, e*x)
    setprecision_all!(Kp, old_pr)
    if haskey(Kp.def_poly_cache, x)
      return Kp.def_poly_cache[x]
    end
    k = sort(collect(keys(Kp.def_poly_cache)))
    p = searchsortedfirst(k, x)
    @assert p <= length(k)
    Kp.def_poly_cache[x] = setprecision(Kp.def_poly_cache[k[p]], x)
    @assert all(x->parent(x) === parent(all_f[1]), all_f)
    return Kp.def_poly_cache[x]
  end
  return Kp, completion_map
end

function _solve_internal(gq_in_K, P, precision, Zp, Qq)
  f = inertia_degree(P)
  K = parent(gq_in_K)
  e = ramification_index(P)
  precision += e - (precision % e)
  @assert precision % e == 0
  #problem/ feature:
  #the lin. alg is done in/over Zp or Qp, thus precision is measured in
  #block of length e (power of the prime number p, rather than powers of
  #pi, the prime element)
  #so it is a good idea to increase the precision to be divisible by e
  #thus the solution is valid. Otherwise, some coefficients in the solution
  #can be "half valid", ie a+O(pi^l) where l is not divisible by e
  #
  u = uniformizer(P).elem_in_nf

  pows_gq = powers(gq_in_K, f-1)
  els = Vector{AbsSimpleNumFieldElem}()
  el = one(K)
  for i = 1:e
    for j = 1:f
      push!(els, el*pows_gq[j])
    end
    mul!(el, el, u)
  end
  append!(els,  map(elem_in_nf, basis(P^(precision), copy = false)))
  MK = basis_matrix(els, FakeFmpqMat)
  bK = basis_matrix(AbsSimpleNumFieldElem[u^e, gen(K)], FakeFmpqMat)
  d = lcm(denominator(MK, copy = false), denominator(bK, copy = false))
  if d != denominator(MK, copy = false)
    mul!(MK.num, MK.num, divexact(d, denominator(MK, copy = false)))
  end
  if d != denominator(bK, copy = false)
    mul!(bK.num, bK.num, divexact(d, denominator(bK, copy = false)))
  end

  setprecision!(Zp, Hecke.precision(Zp) + valuation(Zp(denominator(MK))))

if true
  #snf is slower (possibly) but has optimal precision loss.
  #bad example is completion at prime over 2 in
  # x^8 - 12*x^7 + 44*x^6 - 24*x^5 - 132*x^4 + 120*x^3 + 208*x^2 - 528*x + 724
  # the can_solve... returns a precision of just 6 p-adic digits
  # the snf gets 16 (both for the default precision)
  # the det(M) has valuation 12, but the elem. divisors only 3
  #TODO: rewrite can_solve? look at Avi's stuff?
  # x M = b
  # u*M*v = s
  # x inv(u) u M v = b v
  # x inv(u)   s   = b v
  # x = b v inv(s) u
  #lets try:
  
  s, _u, v = snf_with_transform(MK.num)
  bv = bK.num * v
  
  bv = map_entries(Zp, bv)
  
#  sZ = solve(MK.num, bK.num; side = :left)
#   xZp = map_entries(Zp, sZ)
  for i=1:ncols(s)
    bv[1, i] = divexact(bv[1, i], Zp(s[i,i]))
    bv[2, i] = divexact(bv[2, i], Zp(s[i,i]))
  end
  xZp = bv * map_entries(Zp, _u[1:ncols(s), 1:ncols(s)])
else
  MZp = map_entries(Zp, MK.num)
  bZp = map_entries(Zp, bK.num)
  fl, xZp = can_solve_with_solution(MZp, bZp, side = :left)
  @assert fl
end
  coeffs_eisenstein = Vector{QadicFieldElem}(undef, e+1)
  gQq = gen(Qq)
  for i = 1:e
    coeff = zero(Qq)
    for j = 0:f-1
      coeff += (gQq^j)*xZp[1, j+1+(i-1)*f].x
    end
    coeffs_eisenstein[i] = -coeff
  end
  coeffs_eisenstein[e+1] = one(Qq)
  if iszero(coeffs_eisenstein[1])
    error("precision not high enough to obtain Esenstein polynomial")
  end
  return coeffs_eisenstein, xZp
end



function setprecision!(f::CompletionMap{LocalField{QadicFieldElem, EisensteinLocalField}, LocalFieldElem{QadicFieldElem, EisensteinLocalField}}, new_prec::Int)
  P = prime(f)
  OK = order(P)
  new_prec += valuation(denominator(basis_matrix(OK, copy = false)), P)

  new_prec == f.precision && return

  if new_prec < f.precision
    K = codomain(f)
    e = ramification_index(P)
    pr = div(new_prec+e-1, e)
    v = sort(collect(keys(K.def_poly_cache)))
    i = searchsortedfirst(v, pr)
    K.def_poly_cache[pr] = setprecision(K.def_poly_cache[v[i]], pr)
    setprecision!(K, new_prec)
    setprecision!(base_field(K), pr)
    @assert new_prec <= precision(f.prim_img)
#    setprecision!(f.prim_img, new_prec)
  else
    #I need to increase the precision of the data
    Kp = codomain(f)
    _f = inertia_degree(P)
    e = ramification_index(P)
    if new_prec >= e*maximum(keys(Kp.def_poly_cache))
      new_prec += e - new_prec % e
      @assert new_prec % e == 0
      asked = new_prec
      new_prec = max(new_prec, 2*e*maximum(keys(Kp.def_poly_cache))) 
      #to not do this too frequently
      gq, u = f.inv_img
      ex = div(new_prec+e-1, e)
      Zx = polynomial_ring(ZZ, "x", cached = false)[1]
      pol_gq = map_coefficients(x -> lift(ZZ, x), defining_polynomial(base_field(Kp)), cached = false)
      gq = _increase_precision(gq, pol_gq, div(f.precision+e-1, e), ex, P)
  #    @show valuation(pol_gq(gq), P), ex
      f.inv_img = (gq, f.inv_img[2])

      Zp = maximal_order(absolute_base_field(Kp))
      Qq = base_field(Kp)

      setprecision!(Qq, ex)
      setprecision!(Zp, ex)
      gQq = gen(Qq)

      coeffs_eisenstein, xZp = _solve_internal(gq, P, new_prec, Zp, Qq)

      Qqx = parent(first(values(Kp.def_poly_cache)))
#      @show coeffs_eisenstein
#      @show xZp

      pol_gen = Qqx(coeffs_eisenstein)
      Kp.def_poly_cache[div(new_prec + e -1, e)] = pol_gen
      img_prim_elem = Vector{QadicFieldElem}(undef, e)
      for i = 1:e
        coeff = Qq()
        for j = 0:_f-1
          coeff += (gQq^j)*xZp[2, j+1+(i-1)*_f].x
        end
        img_prim_elem[i] = coeff
      end
      setprecision!(Kp, new_prec)
      f.prim_img = Kp(Qqx(img_prim_elem))
#      @show f.prim_img, new_prec
      f.precision = new_prec
      if asked < new_prec
        setprecision!(Kp, asked)
        setprecision!(base_field(Kp), div(asked+e-1, e)+1)
        return 
      end
    else
#      f.precision = max(new_prec, f.precision)
      v = sort(collect(keys(Kp.def_poly_cache)))
      i = searchsortedfirst(v, div(new_prec, e))
      Kp.def_poly_cache[new_prec] = setprecision(Kp.def_poly_cache[v[i]], new_prec)
      setprecision!(Kp, new_prec)
      setprecision!(base_field(Kp), div(new_prec, e)+1)
    end
  end
  return nothing
end

################################################################################
#
#   Totally ramified case
#
################################################################################

@doc raw"""
    totally_ramified_completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int) -> LocalField, CompletionMap

The completion of $K$ wrt to the topology induced by the valuation at a totally ramified prime ideal $P$,
presented as a Eisenstein extension of $Q_p$.
The map giving the embedding of $K$ into the completion, admits a pointwise pre-image to obtain a lift.
Note, that the map is not well defined by this data: $K$ will have $\deg P$ many embeddings.
"""
function totally_ramified_completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int = 64)
  @assert precision > 0
  OK = order(P)
  @assert is_prime(P)
  @assert nf(OK) == K
  @assert isone(degree(P))
  e = ramification_index(P)
  Qp = padic_field(minimum(P), precision = precision)
  Zp = maximal_order(Qp)
  Zx = ZZ["x"][1]
  Qpx = polynomial_ring(Qp, "x")[1]
  u = uniformizer(P).elem_in_nf
  pows_u = powers(u, e-1)
  bK = basis_matrix(AbsSimpleNumFieldElem[u*pows_u[end], gen(K)], FakeFmpqMat)
  append!(pows_u, map(elem_in_nf, basis(P^precision, copy = false)))
  MK = basis_matrix(pows_u, FakeFmpqMat)
  d = lcm(denominator(MK, copy = false), denominator(bK, copy = false))
  if d != denominator(MK, copy = false)
    mul!(MK.num, mK.num, divexact(d, denominator(MK, copy = false)))
  end
  if d != denominator(bK, copy = false)
    mul!(bK.num, bK.num, divexact(d, denominator(bK, copy = false)))
  end
  MZp = map_entries(Zp, MK.num)
  bZp = map_entries(Zp, bK.num)
  fl, xZp = can_solve_with_solution(MZp, bZp, side = :left)
  @assert fl
  coeffs_eisenstein = Vector{PadicFieldElem}(undef, e+1)
  for i = 1:e
    coeffs_eisenstein[i] = -xZp[1, i].x
  end
  coeffs_eisenstein[e+1] = one(Qp)
  pol_gen = Qpx(coeffs_eisenstein)
  Kp, gKp = eisenstein_extension(pol_gen, "a")
  img_prim_elem = Vector{PadicFieldElem}(undef, e)
  for i = 1:e
    img_prim_elem[i] = xZp[2, i].x
  end
  img = Kp(Qpx(img_prim_elem))
  if Nemo.precision(img) < Nemo.precision(Kp)
    img = newton_lift(Zx(defining_polynomial(K)), img, Nemo.precision(img), Nemo.precision(Kp))
  end
  completion_map = CompletionMap(K, Kp, img, u, precision)
  completion_map.P = P
  return Kp, completion_map
end


function setprecision!(f::CompletionMap{LocalField{PadicFieldElem, EisensteinLocalField}, LocalFieldElem{PadicFieldElem, EisensteinLocalField}}, new_prec::Int)
  Kp = codomain(f)
  if new_prec <= maximum(keys(Kp.def_poly_cache))
    setprecision!(Kp, new_prec)
    setprecision!(base_field(Kp), new_prec)
#    @show new_prec, precision(f.prim_img)
    @assert precision(f.prim_img) >= new_prec
#    setprecision!(f.prim_img, new_prec)
    f.precision = new_prec
  else
    K = domain(f)
    #I need to increase the precision of the data
    P = prime(f)
    e = ramification_index(P)
    u = f.inv_img[2]
    Kp = codomain(f)
    @assert !(new_prec in keys(Kp.def_poly_cache))
    ex, r = divrem(new_prec, ramification_index(P))
    if r > 0
      ex += 1
    end
    Qp = padic_field(prime(Kp), precision = div(new_prec, e) + 1)
    Zp = maximal_order(Qp)
#    @show Zp, precision(Zp)
    Qpx, _ = polynomial_ring(Qp, "x")
    pows_u = powers(u, e-1)
    bK = basis_matrix(AbsSimpleNumFieldElem[u*pows_u[end], gen(K)])
    append!(pows_u, map(elem_in_nf, basis(P^new_prec, copy = false)))
    MK = basis_matrix(pows_u)
    cMK = content(MK)
#    @show content(MK), valuation(Qp(content(MK)))
    divexact!(MK, MK, cMK)
    divexact!(bK, bK, cMK)
    MZp = map_entries(Zp, MK)
#    @show map_entries(precision, MZp)
#    @show elementary_divisors(MZp)
    bZp = map_entries(Zp, bK)
#    global last_mat = (MZp, bZp)
    fl, xZp = can_solve_with_solution(MZp, bZp, side = :left)
#    @show map_entries(precision, xZp)
    @assert fl
    coeffs_eisenstein = Vector{PadicFieldElem}(undef, e+1)
    for i = 1:e
      coeffs_eisenstein[i] = -xZp[1, i].x
    end
    coeffs_eisenstein[e+1] = one(Qp)
    pol_gen = Qpx(coeffs_eisenstein)
    Kp.def_poly_cache[new_prec] = pol_gen
    setprecision!(Kp, new_prec * ramification_index(Kp))
    #Should I update the traces too?
    img_prim_elem = Vector{PadicFieldElem}(undef, e)
    for i = 1:e
      img_prim_elem[i] = xZp[2, i].x
    end
#    @show map(precision, img_prim_elem)
    img = Kp(Qpx(img_prim_elem))
    f.prim_img = img
#    @show precision(img), new_prec
    f.precision = new_prec
  end
  return nothing
end


################################################################################
#
#  Unramified case
#
################################################################################

@doc raw"""
    unramified_completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int) -> QadicField, CompletionMap

The completion of $K$ wrt to the topology induced by the valuation at an unramified prime ideal $P$, presented
as a QadicField.
The map giving the embedding of $K$ into the completion, admits a pointwise pre-image to obtain a lift.
Note, that the map is not well defined by this data: $K$ will have $\deg P$ many embeddings.
"""
function unramified_completion(K::AbsSimpleNumField, P::AbsNumFieldOrderIdeal{AbsSimpleNumField, AbsSimpleNumFieldElem}, precision::Int = 64)
  OK = order(P)
  @assert is_prime(P)
  @assert nf(OK) == K
  @assert isone(ramification_index(P))
  f = degree(P)
  p = minimum(P)
  Qq, gQq = qadic_field(p, f, precision = precision)
  Qp = padic_field(p, precision = precision)
  Zp = maximal_order(Qp)
  q, mq = residue_field(Qq)
  F, mF = residue_field(OK, P)
  mp = find_morphism(q, F)
  g = gen(q)
  gq_in_K = (mF\(mp(g))).elem_in_nf
  Zx = polynomial_ring(ZZ, "x")[1]
  pol_gq = lift(Zx, defining_polynomial(q))
  gq_in_K = _lift(gq_in_K, pol_gq, precision, P)
  #To compute the image of the primitive element, we use linear algebra if p is an index divisor
  #Hensel lifting otherwise
  if !is_defining_polynomial_nice(K) || is_index_divisor(OK, minimum(P))
    els = powers(gq_in_K, f-1)
    append!(els, map(elem_in_nf, basis(P^precision)))
    MK = basis_matrix(els, FakeFmpqMat)
    bK = basis_matrix(AbsSimpleNumFieldElem[gen(K)], FakeFmpqMat)
    d = lcm(denominator(MK, copy = false), denominator(bK, copy = false))
    if d != denominator(MK, copy = false)
      mul!(MK.num, mK.num, divexact(d, denominator(MK, copy = false)))
    end
    if d != denominator(bK, copy = false)
      mul!(bK.num, bK.num, divexact(d, denominator(bK, copy = false)))
    end
    MZp = map_entries(Zp, MK.num)
    bZp = map_entries(Zp, bK.num)
    fl, xZp = can_solve_with_solution(MZp, bZp, side = :left)
    @assert fl
    img = Qq()
    for j = 0:f-1
      img += (gQq^j)*xZp[1, j+1].x
    end
  else
    el = mq\(mp\(mF(OK(gen(K)))))
    img = newton_lift(Zx(K.pol), el)
  end
  completion_map = CompletionMap(K, Qq, img, gq_in_K, precision)
  completion_map.P = P
  return Qq, completion_map
end

function setprecision!(f::CompletionMap{QadicField, QadicFieldElem}, new_prec::Int)
  if new_prec == f.precision
    return
  end
  Kp = codomain(f)
  setprecision!(Kp, new_prec)
  if new_prec < f.precision
    @assert precision(f.prim_img) >= new_prec
#    setprecision!(f.prim_img, new_prec)
  else
    P = prime(f)
    gq, u = f.inv_img
    Zx = polynomial_ring(ZZ, "x")[1]
    q, mq = residue_field(Kp)
    pol_gq = lift(Zx, defining_polynomial(q))
    gq = _increase_precision(gq, pol_gq, f.precision, new_prec, P)
    f.inv_img = (gq, u)
    setprecision!(Kp, new_prec)
    #To increase the precision of the image of the primitive element, I use Hensel lifting
    f.prim_img = newton_lift(Zx(defining_polynomial(domain(f))), f.prim_img, new_prec, precision(f.prim_img))
  end
  f.precision = new_prec
  return nothing
end

#

# at the moment only internal, since ideally we also return an appropriate map
function _is_locally_isomorphic(K::AbsSimpleNumField, L::AbsSimpleNumField, p::IntegerUnion)
  @req is_normal(K) && is_normal(L) "Not implemented for non-normal extensions (yet)"
  OK = maximal_order(K)
  OL = maximal_order(L)
  if prime_decomposition_type(OK, p) != prime_decomposition_type(OL, p)
    return false
  end
  P, = prime_ideals_over(OK, p)
  Q, = prime_ideals_over(OL, p)
  CP, mCP = completion(K, P)
  CQ, mCQ = completion(L, Q)
  fl, = is_isomorphic(CP, CQ)
  return fl
end
