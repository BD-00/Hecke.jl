
#maximal divisor reduction with (x)_\infty
function maximal_reduction(D::Divisor)
  @req !iszero(D) "Divisor is zero."

  F = function_field(D)
  n = degree(F)
  
  A = pole_divisor(Hecke.separating_element(F))

  #start of riemann roch space computation to get d_i
  J_fin, J_inf = inv.(ideals(D))
  B_fin = _coordinate_matrix(J_fin)
  B_inf = _coordinate_matrix(J_inf)
  dM, d_deg = _riemann_roch_common_setup(B_fin, B_inf)

  # weak Popov reduction of dM (no denominators)
  T, U = _weak_popov_with_transform!(dM)

  #Let v_i be the basis generators in the RR computation.
  #Choose 'r' maximal s.th. v_i *x^r in RR(D) for some i.
  d_min, idx = findmin(maximum(degree, T[i, 1:n]) for i in 1:n)
  r = d_deg - d_min

  #'a' is first basis generator v_i s.th. v_i * x^r in RR(D),
  #so 'a' in RR(D-r*(x)_\infty) (not necessarily as a generator).
  a = divisor((U[idx:idx, :]*basis(J_fin))[1])

  D_red = D - r*A + a

  #test assertions:
  @assert D_red == D - r*A + a
  @assert is_effective(D_red)
  @assert is_principal(a)
  @assert dimension(D_red-A) == 0

  return D_red, r, a
end