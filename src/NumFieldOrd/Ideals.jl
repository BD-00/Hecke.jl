################################################################################
#
#   Absolute basis
#
################################################################################

function absolute_basis(I::T) where T <: Union{NfAbsOrdIdl, NfAbsOrdFracIdl}
  return basis(I)
end

function absolute_basis(I::T) where T <: Union{NfRelOrdIdl, NfRelOrdFracIdl}
  res = elem_type(nf(order(I)))[]
  pb = pseudo_basis(I)
  pbb = pseudo_basis(order(I))
  for i in 1:length(pb)
    (e, I) = pb[i]
    for b in absolute_basis(I)
      push!(res, e * b)
    end
  end
  return res
end

################################################################################
#
#   Absolute Minimum
#
################################################################################

@doc Markdown.doc"""
    absolute_minimum(I::NumFieldOrdIdl) -> fmpz

Given an ideal $I$, returns a generator of the ideal $I \cap \mathbb Z$.
"""
absolute_minimum(::NumFieldOrdIdl)


function absolute_minimum(I::NfAbsOrdIdl)
  return minimum(I)
end

function absolute_minimum(I::NfRelOrdIdl)
  return absolute_minimum(minimum(I))::fmpz
end

################################################################################
#
#   Absolute norm
#
################################################################################

@doc Markdown.doc"""
    absolute_norm(I::NumFieldOrdIdl) -> fmpz

Given an ideal $I$, returns its norm over $\mathbb Q$.
"""
absolute_norm(::NumFieldOrdIdl)

function absolute_norm(x::NfAbsOrdIdl)
  return norm(x)
end

function absolute_norm(a::NfRelOrdIdl)
  return norm(a, FlintQQ)
end

################################################################################
#
#   Absolute anti uniformizer
#
################################################################################

@doc Markdown.doc"""
    absolute_anti_uniformizer(P::NumFieldOrdIdl) -> NumFieldElem

Given a prime ideal $P$, this function returns an element $x$ with valuation(x, P) = -1$,
valuation(x, Q) = 0$ for every ideal Q conjugate to $P$ and non-negative valuation
at any other prime ideal.
"""
absolute_anti_uniformizer(::NumFieldOrdIdl)

function absolute_anti_uniformizer(P::NfAbsOrdIdl)
  return anti_uniformizer(P)
end

function absolute_anti_uniformizer(P::NfRelOrdIdl)
  OL = order(P)
  L = nf(OL)
  A = absolute_basis(OL)
  d = absolute_degree(nf(OL))
  OLmat = zero_matrix(FlintQQ, d, d)
  Lbas = absolute_basis(L)
  for i in 1:d
    c = elem_in_nf(A[i], copy = false)
    coords = absolute_coordinates(c)
    for j in 1:d
      OLmat[i, j] = coords[j]
    end
  end

  OLmatinv = inv(OLmat)

  u = elem_in_nf(p_uniformizer(P))

  @show isintegral(u)

  umat = zero_matrix(FlintQQ, d, d)

  for i in 1:d
    c = u * Lbas[i]
    coordsc = absolute_coordinates(c)
    for j in 1:d
      umat[i, j] = coordsc[j]
    end
  end

  N = OLmat * umat * OLmatinv

  p = absolute_minimum(P)

  z = zero_matrix(GF(p, cached = false), d, d)

  for i in 1:d
    for j in 1:d
      z[i, j] = FlintZZ(N[i, j])
    end
  end

  K = left_kernel_basis(z)

  k = K[1]
  return inv(L(p)) * elem_in_nf(sum(elem_type(OL)[A[i] * lift(k[i]) for i in 1:d]))
end

################################################################################
#
#   Support
#
################################################################################

function support(I::T) where T <: Union{NumFieldOrdIdl, NumFieldOrdFracIdl}
  lp = factor(I)
  return collect(keys(lp))
end

################################################################################
#
#   Is integral
#
################################################################################

isintegral(I::NumFieldOrdIdl) = true

function isintegral(I::NfOrdFracIdl)
  @assert ismaximal(order(I))
  simplify(I)
  return denominator(I) == 1
end

function isintegral(a::NfRelOrdFracIdl) 
  @assert ismaximal(order(a))
  return defines_ideal(order(a), basis_pmatrix(a, copy = false))
end

################################################################################
#
#   Trace ideal
#
################################################################################

function tr(I::NfAbsOrdIdl)
  E = nf(order(I))
  K = base_field(E)
  return gcd(fmpz[tr(x) for x in basis(I)])
end


function tr(I::NfAbsOrdFracIdl)
  E = nf(order(I))
  K = base_field(E)
  traces = fmpq[trace(b) for b in basis(I)]
  #TODO: This is deeply wrong.
  return reduce(gcd, traces; init = fmpq(0))
end

function tr(I::T) where T <: Union{NfRelOrdIdl, NfRelOrdFracIdl}
  E = nf(order(I))
  K = base_field(E)
  return fractional_ideal(maximal_order(K), elem_type(K)[trace(b) for b in absolute_basis(I)])
end

################################################################################
#
#   Gens
#
################################################################################

gens(I::NumFieldOrdIdl) = small_generating_set(I)

function gens(I::NumFieldOrdFracIdl)
  K = nf(order(I))
  nI = numerator(I)
  dI = denominator(I)
  gnI = gens(nI)
  return elem_type(K)[elem_in_nf(x)//dI for x in gnI]
end

function small_generating_set(I::NfAbsOrdIdl)
  OK = order(I)
  if isone(I)
    return elem_type(OK)[one(OK)]
  end
  if has_2_elem(I)
    return elem_type(OK)[OK(I.gen_one), OK(I.gen_two)]
  end
  if ismaximal_known_and_maximal(OK)
    _assure_weakly_normal_presentation(I)
    return elem_type(OK)[OK(I.gen_one), OK(I.gen_two)]
  end
  id_gen = zero_matrix(FlintZZ, 2*n, n)
  m = minimum(I, copy = false)
  B = basis(I, copy = false)
  gens = NfOrdElem[]
  for i = 1:length(B)
    if i != 1
      c = matrix(FlintZZ, 1, n, coordinates(B[i]))
      reduce_mod_hnf_ll!(c, id_gen)
      if iszero(c)
        continue
      end
    end
    M = representation_matrix_mod(B[i], modu)
    _copy_matrix_into_matrix(id_gen, 1, 1, M)
    hnf_modular_eldiv!(id_gen, m, :lowerleft)
    push!(gens, B[i])
    if view(id_gen, n+1:2*n, 1:n) == basis_matrix(a, copy = false)
      break
    end
  end
  return gens
end

function small_generating_set(I::NfRelOrdIdl)
  OK = order(I)
  K = nf(OK)
  B = pseudo_basis(I, copy = false)
  starting_gens = elem_type(OK)[]
  for i = 1:length(B)
    gensI = small_generating_set(numerator(B[i][2], copy = false))
    for x in gensI
      push!(starting_gens, OK(divexact(elem_in_nf(x, copy = false)*B[i][1], denominator(B[i][2], copy = false))))
    end
  end
  #Now, I have a set of generators as a OK-module.
  #Let's discard the non relevant elements
  indices = Int[]
  Id = ideal(OK, 0)
  id_gen = pseudo_matrix(zero_matrix(base_field(K), 0, degree(OK)))
  for i = 1:length(starting_gens)
    if i != 1
      if starting_gens[i] in Id
        continue
      end
    end
    Id = Id + ideal(OK, starting_gens[i])
    push!(indices, i)
    if Id == I
      break
    end
  end
  return starting_gens[indices]
end

function isramified(O::NumFieldOrd, P::NumFieldOrdIdl)
  OK = order(P)
  d = discriminant(O, nf(OK))
  return !iscoprime(P, d)
end
