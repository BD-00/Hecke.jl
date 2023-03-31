using Plots, CSV, DataFrames

Ps = []
LPs = []
I = collect(5:0.5:20)
for i in I
 start = fmpz(ceil(10^i))
 P = PrimesSet(start, start*10)
 for p in P
  if isprime(div(p-1,2))
   push!(Ps, p)
   push!(LPs, Base.log(p)/Base.log(10))
   break
  end
 end
end

T1 = []
T2 = []
B1 = []
B2 = []
LP = []
TC = []
BC = []

Qp = Ps[21:22]
for p in Qp
  o = cryptoprime(7)
  G = GF(o)
  aG = Hecke.primitive_element(G)
  bG = G(100)
  push!(LP, log(p)/log(10))
  F = GF(p)
  a = Hecke.primitive_element(GF(p))
  b = F(123456789)
  @timed safeprime_dl(aG, bG, o)
  t1 = @timed safeprime_dl(a, b, p)
  @timed IdxCalc(aG, bG)
  t2 = @timed IdxCalc(a, b)
  if t1.time<t2.time
   push!(TC,1)
  else
   push!(TC,2)
  end
  if t1.bytes<t2.bytes
   push!(BC,1)
  else
   push!(BC,2)
  end
  push!(T1, t1.time)
  push!(B1, t1.bytes)
  push!(T2, t2.time)
  push!(B2, t2.bytes)
end

p1 = plot(LP, T1, title = "time", label = "safeprime_dl")
plot!(LP, T2, label = "IdxCalc")
p2 = plot(LP, B1, title = "bytes", label = "safeprime_dl")
plot!(LP, B2, label = "IdxCalc")
p3 = scatter(LP, TC, title = "less time", xlabel = "1 is ph, 2 is IC",legend = false)
p4 = scatter(LP, BC, title = "less bytes", xlabel = "1 is ph, 2 is IC",legend = false)
p = plot(p1, p2, p3, p4, layout = (2, 2))
savefig("safeprimes.pdf")
savefig("safeprimes.png")
#plot(table(header_values=["log(p)", "time_ph", "time_IC", "bytes_ph", "bytes_IC"],cells_values=[LP, T1, T2, B1, B2]))
df = DataFrame(log_p=LP, time_ph = T1, time_IC = T2, bytes_ph = B1, bytes_IC = B2)
CSV.write("safeprimes.csv", df)






q = cryptoprime(5)
p = div(q-1,2)
F = GF(q)
set_attribute!(F, :rest=>p)
a = Hecke.primitive_element(F)
b = rand(F)
a2 = a^2 
b2 = b^2
@time g2 = disc_log_rest(a2, b2, F)
a2^g2 == b2


Rest = []
LRest = []
I = collect(15:0.5:25)
for i in I
 start = fmpz(ceil(10^i))
 P = PrimesSet(start, start+1000)
 for p in P
  if isprime(2*p+1)
   push!(Rest, p)
   push!(LRest, log(p)/log(10))
   break
  end
 end
end

#Starte mit 5 Stellen
rest = cryptoprime(12)
Q = []
LQ = []
for i in [fmpz(10)^j for j in collect(13:1:40)] #change start
 P = PrimesSet(i,10000*i,rest, fmpz(1))
 q = first(P)
 push!(Q, q)
 push!(LQ, log(q)/log(10))
end
T1 = []
T2 = []
B1 = []
B2 = []
LP = []
TC = []
BC = []

Qp = Q
K = GF(11)

for p in Qp
  o = cryptoprime(7)
  G = GF(o)
  aG = Hecke.primitive_element(G)
  set_attribute!(G, :rest=>div(o-1,2))
  bG = G(100)
  push!(LP, log(p)/log(10))
  F = GF(p)
  a = Hecke.primitive_element(GF(p))
  b = F(123456789)
  x = div(p-1,rest)
  a2 = a^x
  b2 = b^x
  K = GF(11)
  @timed disc_log_ph(K(8), K(5), fmpz(10), 1)
  t1 = @timed disc_log_ph(a2, b2, rest, 1)
  a2^t1.value==b2
  set_attribute!(F, :rest=>rest)
  #=
  @timed disc_log_rest(aG^2, bG^2, G)
  t2 = @timed disc_log_rest(a2, b2, F)
  a2^t2.value == b2
  if t1.time<t2.time
   push!(TC,1)
  else
   push!(TC,2)
  end
  if t1.bytes<t2.bytes
   push!(BC,1)
  else
   push!(BC,2)
  end
  =#
  push!(T1, t1.time)
  push!(B1, t1.bytes)
  #push!(T2, t2.time)
  #push!(B2, t2.bytes)
end

p1 = plot(LP, T1, title = "time", label = "dl_ph", legend=:topleft)
plot!(LP, T2, label = "dl_rest", legend=:topleft)
p2 = plot(LP, B1, title = "bytes", label = "dl_ph", legend=:topleft)
plot!(LP, B2, label = "dl_rest", legend=:left)
p3 = scatter(LP, TC, title = "less time", xlabel = "1 is ph, 2 is IC",legend = false)
p4 = scatter(LP, BC, title = "less bytes", xlabel = "1 is ph, 2 is IC",legend = false)
p = plot(p1, p2, p3, p4, layout = (2, 2))
savefig("18_2_p=316227766016838947.png")
savefig("18_2_p=316227766016838947.pdf")
#plot(table(header_values=["log(p)", "time_ph", "time_IC", "bytes_ph", "bytes_IC"],cells_values=[LP, T1, T2, B1, B2]))
df = DataFrame(log_p=LP, time_ph = T1, time_IC = T2, bytes_ph = B1, bytes_IC = B2)
CSV.write("18_2_p=316227766016838947.csv", df)

io = open("lists.txt", "w")
write(io, "rest: $p1 \n")
write(io, "length of rest: $(log(p1)/log(10)) \n")
write(io, "X: $X \n")
write(io, "LP: $LP \n")
write(io, "T1: $T1 \n")
write(io, "T2: $T2 \n")
write(io, "B1: $B1 \n")
write(io, "B2: $B2 \n")
close(io)

write(io, "LENC: $LENC \n")
write(io, "LENTC: $LENTC \n")
write(io, "LENC2: $LENC2 \n")
write(io, "LENTC2: $LENTC2 \n")




###SERVER###
##Prep##
#cd("/net/nascip132/users/cip/users/dieterle/Dokumente/Sparse/")

using Hecke, Nemo, Random, Markdown#, Plots, CSV, DataFrames
import Base.log
import AbstractAlgebra.Ring

include("Preprocessing.jl")
include("Wiedemann.jl")
include("IndexCalculus.jl")
include("DiscLog.jl")

#Matrix
@doc Markdown.doc"""
  delete_row!(A::SMat{T}, i::Int) -> SMat{T}

Deletes $i$-th row of $A$ in place.
"""
function delete_row!(A::SMat{T}, i::Int) where T
  non_zeros = length(A[i].pos)
  deleteat!(A.rows, i)
  A.r-=1
  A.nnz-=non_zeros
  return A
end

@doc Markdown.doc"""
  delete_rows!(A::SMat{T}, I, sorted=true)

Deletes rows in set of indices $I$ of $A$ in place.
"""
function delete_rows!(A::SMat{T}, I, sorted=true) where T #elements in I need to be ascending
  if !sorted
    sort(I)
  end
  for i in length(I):-1:1
    delete_row!(A, I[i])
  end
  return A
end

@doc Markdown.doc"""
  delete_zero_rows!(A::SMat{T}, s=1)

Deletes zero rows of $A$ in place.
"""
function delete_zero_rows!(A::SMat{T}, s=1) where T #where s denotes the first row where we wanna start
  for i=A.r:-1:s
    if isempty(A[i].pos)
      deleteat!(A.rows, i); A.r-=1
    end
  end
  return A
end

@doc Markdown.doc"""
    empty_col!(A::SMat{T}, TA::SMat{T}, j::Int, changeTA=false) -> SMat{T}/Tuple{SMat{T}, SMat{T}}

Deletes non-zero entries in $j$-th column of $A$ in place using the transpose $TA$ of $A$. Output $A$ doesn't match $TA$ unless changeTA = true.
"""
function empty_col!(A::SMat{T}, TA::SMat{T}, j::Int, changeTA=false) where T #only deletes entries in column j, output same size as input
  @assert 1<=j<=TA.r
  length(TA[j].pos)==0 && return A
  for row in TA[j].pos #not empty
    i = searchsortedfirst(A[row].pos, j)
    if i == length(A[row].pos)+1
      A.nnz+=1 #fixes the nnz problem if TA!=transpose(A)
      continue
    end
    deleteat!(A[row].pos, i) ; deleteat!(A[row].values, i)
  end
  A.nnz -=length(TA[j].pos)
  if changeTA
    TA.nnz -= length(TA[j].pos)
    empty!(TA[j].pos); empty!(TA[j].values)
    return A, TA
  end
  return A
end

@doc Markdown.doc"""
    empty_cols!(A::SMat{T}, TA::SMat{T}, J, changeTA=false) -> SMat{T}/Tuple{SMat{T}, SMat{T}}

Deletes non-zero entries in columns with indices in $J$ of $A$ in place using the transpose $TA$ of $A$. Output $A$ doesn't match $TA$ unless changeTA = true.
"""
function empty_cols!(A::SMat{T}, TA::SMat{T}, J, changeTA=false) where T
  for j in J
    empty_col!(A, TA, j, changeTA)
  end
  changeTA && return A, TA
  return A
end

################################################################################
#
#  Row/Col operations in matrix
#
################################################################################
@doc Markdown.doc"""
    function scale_col!(A::SMat{T}, TA::SMat{T}, j, c) -> SMat{T}

Returns $A$ after scaling $j$-th column in place using the transpose $TA$ of $A$.
"""
function scale_col!(A::SMat{T}, TA::SMat{T}, j, c) where T #A[_j]->c*A[_,j]
  for i in TA[j].pos
    idx_j = searchsortedfirst(A[i].pos, j)
    A[i].values[idx_j]*=c
    if A[i].values[idx_j]==0
      deleteat!(A[i].pos, idx_j); deleteat!(A[i].values, idx_j)
      A.nnz-=1
    end
  end
  return A
end

@doc Markdown.doc"""
    add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) -> SMat{T}

Returns $A$ after add_scaled_row!(Ai::SRow{T}, Aj::SRow{T}, c::T) in $A$.
"""
function add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) where T
  A.nnz = A.nnz - length(A[j])
  add_scaled_row!(A[i], A[j], c)
  A.nnz = A.nnz + length(A[j])
  return A
end

@doc Markdown.doc"""
    add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T) -> SMat{T}

As add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) but with columns of $A$.
"""
function add_scaled_col!(A::SMat{T}, i::Int, j::Int, c::T) where T 
  @assert c != 0
  @assert 1 <= i <= ncols(A) && 1 <= j <= ncols(A)  
  for r in A.rows
    if i in r.pos
      i_i = searchsortedfirst(r.pos, i) #changed
      if j in r.pos
        i_j = searchsortedfirst(r.pos, j) #changed
        r.values[i_j] += c*r.values[i_i]
        if r.values[i_j] == 0
          deleteat!(r.pos, i_j);deleteat!(r.values, i_j)
          A.nnz-=1
        end
      else
        k = searchsortedfirst(r.pos, j)
        v = c*r.values[i_i]
        if v != 0
          insert!(r.pos, k, j)
          insert!(r.values, k, v)
          A.nnz+=1 #necessary in matrices
        end
      end
    end
  end
  return A
end

@doc Markdown.doc"""
    add_scaled_col!(A::SMat{T}, TA::SMat{T}, i::Int, j::Int, c::T) -> SMat{T}

As add_scaled_row!(A::SMat{T}, i::Int, j::Int, c::T) but with columns of $A$.
"""
function add_scaled_col!(A::SMat{T}, TA::SMat{T}, i::Int, j::Int, c::T) where T  #A[_j]->c*A[_,i]+A[_j]
  @assert c != 0
  @assert 1 <= i <= TA.r && 1 <= j <= TA.r

  for idx in TA[i].pos 
    idx_i = searchsortedfirst(A[idx].pos, i) 
    if idx in TA[j].pos
      idx_j = searchsortedfirst(A[idx].pos, j) 
      A[idx].values[idx_j] += c*A[idx].values[idx_i]
      if A[idx].values[idx_j] == 0
       deleteat!(A[idx].pos, idx_j);deleteat!(A[idx].values, idx_j)
       A.nnz-=1
     end
    else
      k = searchsortedfirst(A[idx].pos, j)
        v = c*A[idx].values[idx_i]
        if v != 0
          insert!(A[idx].pos, k, j)
          insert!(A[idx].values, k, v)
          A.nnz+=1 #necessary in matrices
        end
    end
  end
  #add_scaled_row!(TA, i, j, c)
  return A, TA
end

#Row
@doc Markdown.doc"""
    add_scaled_row(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Returns the row $c A + B$.
"""
add_scaled_row(a::SRow{T}, b::SRow{T}, c::T) where {T} = add_scaled_row!(a, deepcopy(b), c)

@doc Markdown.doc"""
    add_scaled_row!(A::SRow{T}, B::SRow{T}, c::T) -> SRow{T}

Returns the row $c A + B$ by changing $B$ in place.
"""
function add_scaled_row!(a::SRow{T}, b::SRow{T}, c::T) where T
  @assert a !== b
  i = 1
  j = 1
  t = base_ring(a)()
  while i <= length(a) && j <= length(b)
    if a.pos[i] < b.pos[j]
      insert!(b.pos, j, a.pos[i])
      insert!(b.values, j, c*a.values[i])
      i += 1
      j += 1
    elseif a.pos[i] > b.pos[j]
      j += 1
    else
      t = mul!(t, c, a.values[i])
      b.values[j] = addeq!(b.values[j], t)

      if iszero(b.values[j])
        deleteat!(b.values, j)
        deleteat!(b.pos, j)
      else
        j += 1
      end
      i += 1
    end
  end
  while i <= length(a)
    push!(b.pos, a.pos[i])
    push!(b.values, c*a.values[i])
    i += 1
  end
  return b
end

function add_scaled_row(Ai::SRow{fmpz}, Aj::SRow{fmpz}, c::fmpz)
  sr = sparse_row(FlintZZ)
  pi = 1
  pj = 1
  @assert c != 0
  n = fmpz()
  nb = 0
  while pi <= length(Ai.pos) && pj <= length(Aj.pos)
    if Ai.pos[pi] < Aj.pos[pj]
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, c*Ai.values[pi])
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, Aj.values[pj])
      pj += 1
    else
      n = mul!(n, c, Ai.values[pi])
      n = add!(n, n, Aj.values[pj])

#      n = c*Ai.values[pi] + Aj.values[pj]
      if !iszero(n)
        nb = max(nb, nbits(n))
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, n)
        n = fmpz()
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    push!(sr.pos, Ai.pos[pi])
    push!(sr.values, c*Ai.values[pi])
    pi += 1
  end
  while pj <= length(Aj.pos)
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, Aj.values[pj])
    pj += 1
  end
#  @show nb
  return sr
end

function add_scaled_row!(Ai::SRow{fmpz}, Aj::SRow{fmpz}, c::fmpz)
  sr = sparse_row(FlintZZ)
  pi = 1
  pj = 1
  @assert c != 0
  n = fmpz()
  nb = 0
  while pi <= length(Ai.pos) && pj <= length(Aj.pos)
    if Ai.pos[pi] < Aj.pos[pj]
      push!(sr.pos, Ai.pos[pi])
      push!(sr.values, c*Ai.values[pi])
      pi += 1
    elseif Ai.pos[pi] > Aj.pos[pj]
      push!(sr.pos, Aj.pos[pj])
      push!(sr.values, Aj.values[pj])
      pj += 1
    else
      n = mul!(n, c, Ai.values[pi])
      n = add!(n, n, Aj.values[pj])

#      n = c*Ai.values[pi] + Aj.values[pj]
      if !iszero(n)
        nb = max(nb, nbits(n))
        push!(sr.pos, Ai.pos[pi])
        push!(sr.values, n)
        n = fmpz()
      end
      pi += 1
      pj += 1
    end
  end
  while pi <= length(Ai.pos)
    push!(sr.pos, Ai.pos[pi])
    push!(sr.values, c*Ai.values[pi])
    pi += 1
  end
  while pj <= length(Aj.pos)
    push!(sr.pos, Aj.pos[pj])
    push!(sr.values, Aj.values[pj])
    pj += 1
  end
#  @show nb
  Aj.pos = sr.pos
  Aj.values = sr.values
  return sr
end


function cryptoprime(N)
#return a Prime p with N digits. s.t (p-1)/2 is prime
  p = rand(fmpz(10)^(N-1):fmpz(10)^N)
  while true
    p = next_prime(p+1)
    !isprime(div(p-1,2)) || return p
  end 
end 

function cryptoprime_to_base_n(N, n)
#return a Prime p with N digits. s.t (p-1)/2 is prime
  p = rand(fmpz(n)^(N-1):fmpz(n)^N)
  while true
    p = next_prime(p+1)
    !isprime(div(p-1,2)) || return p
  end 
end 

function rand_dec_prime(N) #returns prime numer of decimal length N
  lower = fmpz(10)^(N-1)
  upper = fmpz(10)^N
  p = rand(lower:upper)
  p = next_prime(p)
  if p >= upper
    return next_prime(lower)
  end
  return p
end

function rdp_to_base_n(N, n) #returns prime numer of decimal length N
  lower = fmpz(N)^(N-1)
  upper = fmpz(n)^N
  p = rand(lower:upper)
  p = next_prime(p)
  if p >= upper
    return next_prime(lower)
  end
  return p
end

##Test##

Ps = []
LPs = []
I = collect(5:0.5:20)
for i in I
 s = fmpz(ceil(10^i))
 P = PrimesSet(s, s*10)
 for p in P
  if isprime(div(p-1,2))
   push!(Ps, p)
   push!(LPs, Base.log(p)/Base.log(10))
   break
  end
 end
end
rest = Ps[16]
Q = []
LQ = []
for i in [fmpz(10)^j for j in collect(13:1:20)] #change start
 P = PrimesSet(i,10000*i,rest, fmpz(1))
 q = first(P)
 push!(Q, q)
 push!(LQ, Base.log(q)/Base.log(10))
end
T1 = []
T2 = []
B1 = []
B2 = []
LP = []
TC = []
BC = []

Qp = Q[8:9]

for p in Qp
 o = cryptoprime(7)
 G = GF(o)
 aG = Hecke.primitive_element(G)
 set_attribute!(G, :rest=>div(o-1,2))
 bG = G(100)
 push!(LP, log(p)/log(10))
 F = GF(p)
 a = Hecke.primitive_element(GF(p))
 b = F(123456789)
 x = div(p-1,rest)
 a2 = a^x
 b2 = b^x
 K = GF(11)
 @timed disc_log_ph(K(8), K(5), fmpz(10), 1)
 t1 = @timed disc_log_ph(a2, b2, rest, 1)
 a2^t1.value==b2
 set_attribute!(F, :rest=>rest)
 @timed disc_log_rest(aG^2, bG^2, G)
 t2 = @timed disc_log_rest(a2, b2, F)
 a2^t2.value == b2
 if t1.time<t2.time
  push!(TC,1)
 else
  push!(TC,2)
 end
 if t1.bytes<t2.bytes
  push!(BC,1)
 else
  push!(BC,2)
 end
 push!(T1, t1.time)
 push!(B1, t1.bytes)
 push!(T2, t2.time)
 push!(B2, t2.bytes)
end

io = open("Zeitanalyse.txt", "a")
write(io, "rest= $rest \n")
write(io, "length of rest=$(log(rest)/log(10)) \n")
write(io, "Q= $Q \n")
write(io, "LQ= $LQ \n")
write(io, "LP= $LP \n")
write(io, "T1=$T1 \n")
write(io, "T2= $T2 \n")
write(io, "B1= $B1 \n")
write(io, "B2= $B2 \n")
write(io, "TC= $TC \n")
write(io, "BC= $BC \n")
close(io)

#include("server_test.jl")