#TODO: move to respective place later

#compute mod(f^e, I) using square and multiply
#inspired by powermod in GenOrd/GenOrd.jl
function Hecke.powermod(a::Hecke.GenOrdElem, e::ZZRingElem, I::Hecke.GenOrdIdl)
  r = one(parent(a))
  e == 0 && return r
  if e > 0#negative exponents not needed for the moment
    for i = bits(e)
      r *= r
      if i
        r *= a
      end
      r = mod(r, I)
    end
    return r
  else #e < 0
    return powermod(invmod(a, I), -e, I)
  end
end

function Hecke.invmod(x::GenOrdElem, I::GenOrdIdl)
  O = I.order
  n = degree(O)
  Fx = base_ring(O)
  
  u = zeros(Fx, n)
  u[1] = Fx(1)
  Mx = representation_matrix(x)
  MI = basis_matrix(I)
  A = vcat(Mx, MI)
  y_coord = solve(A, u)[1:n]
  y = mod(O(y_coord), I)
  return y
end