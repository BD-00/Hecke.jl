using Hecke, Nemo, Random, Markdown
import Base.log

add_verbose_scope(:StructGauss)
add_assert_scope(:StructGauss)

set_assert_level(:StructGauss, 3)
set_verbose_level(:StructGauss, 0)

#kleines Beispiel ohne Error
p = fmpz(47)
F = GF(p)
a = F(20)
set_attribute!(F, :a=>a)

#mittleres Beispiel ohne Error
p = fmpz(3808986227)
F  = GF(p)
a = GF(2964180501)
set_attribute!(F, :a=>a)

#großes Beispiel ohne Error
p = fmpz(28305054749008327163)
F = GF(p)
a = F(6879064112033849389)
set_attribute!(F, :a=>a)

#Beispiel AssertionError: c != best_c in 382
p = fmpz(9048192719)
F = GF(p)
a = F(4313590289)
set_attribute!(F, :a=>a)

#von hier an für alle Beispiele gleich

sieve(F, sieve_params(characteristic(F),0.02,1.01))

A = get_attribute(F, :RelMat)
l = get_attribute(F, :fb_length)
#STRUCTURED GAUSS USING TA 
bound_limit = 2^31 #oder mod?
base = 1 #indices +1
single_row_limit = 1
light_weight = [length(A[i]) for i in 1:A.r]

over_Z = true
over_field = false

NEW = true
REDUCE_IC_RELS_EXTRA=30000

R = base_ring(A)
if R == ZZ || R == zz
 over_Z = true
end
M = div(p-1,2)
#M2

#429-466
for i = 1:A.r
  len = length(A[i])
  if len == 0
    delete_row!(A, i)
  elseif len == 1
    @assert single_row_limit <=i
    if i != single_row_limit
      swap_rows_perm(A, i, single_row_limit, col_list_perm, col_list_permi)
    end
    single_row_limit +=1
  end
end #single_row_limit = 1

TA = transpose(A)
col_list = []; col_count = []
for j = 1:A.c
 push!(col_list, TA[j].pos)
 push!(col_count, length(TA[j]))
end
#480: Mark all coloums light initially

is_light_col = fill(true, A.c)
is_single_col = fill(false, A.c)
single_col = fill(-2, A.r) #single_col[i] = c >= 0 if row i has entry in col c alone

nlight = A.c #number of light cols
nsingle = 0 #number of single elem cols
matrix_nentries = A.nnz

#501: Initialize column list permutations and column lists.
col_list_perm = [i for i = 1:A.r]  #perm gives new ordering of original A[i] via their indices
col_list_permi = [i for i = 1:A.r] #A[permi[i]]=A[i] before permutation = list of sigma(i)


#505-528  
abs_row_bounds = []
for i = 1:A.r
  push!(abs_row_bounds, maximum(abs, A[i].values))
end

re_verb = true
R = base_ring(A)
Y = sparse_matrix(R)
Y.c = A.c

counter = 0
#544-1127
while nlight > 0 && base <= A.r #&& det_sign
 counter +=1
 col_consider_o = [c for c in 1:A.c]
 col_consider_len_o = A.c + 1
 First = true
 nzero = 0
 #558-635
 while col_consider_len_o > 1 
  col_consider_n = []
  #562-630
  while col_consider_len_o > 1
    col_consider_len_o-=1
    c = col_consider_o[col_consider_len_o]
    if !is_light_col[c]
     continue
    end
    if First && col_count[c] == 0
      nzero+=1
    #570-629  
    elseif col_count[c] == 1
      L = col_list[c]
      @assert(length(L)==1)
      L_row = first(L) #index of row with entry in col c
      i = col_list_permi[L_row]
      #Column c has only one non-zero at row i. Move row i into base.
      #599-607
      for cc in A[i].pos
        if is_light_col[cc]
         @assert col_count[cc]>0 
        end
        col_count[cc]-=1
        if col_count[cc]== 1
          push!(col_consider_n, cc)
        end
        if is_light_col[cc]
          deleteat!(col_list[cc],findfirst(isequal(L_row), col_list[cc]))
        end
      end
      matrix_nentries -= length(A[i])
      is_light_col[c] = false
      is_single_col[c] = true
      nlight-=1
      nsingle+=1

      single_col[i] = c

      if i < single_row_limit
        swap_rows_perm(A, i, base, col_list_perm, col_list_permi)
      else
        if i != single_row_limit 
         swap_rows_perm(A, base, single_row_limit, col_list_perm, col_list_permi)
        end
        single_row_limit +=1
        swap_rows_perm(A, base, i, col_list_perm, col_list_permi)
      end
      base +=1
    end
  end
  col_consider_o = col_consider_n
  col_consider_len_o = length(col_consider_o)+1
  First = false
 end
 if (nlight == 0 || base == A.r)
  break
 end

 best_i = -1
 best_c = NaN
 best_x = NaN
 best_len = -1
 best_is_one = false
	best_fill = 1e10
 Nrows = A.r - base + 1
 scols = A.c - nsingle - nzero
 #664-811
 for i = base:single_row_limit-1  #here not the case in first loop
  @vprint :StructGauss 3 "i: $i"
  len = length(A[i])
  w = light_weight[i]
  @assert w == 1
  c = find_light_entry(A[i].pos, is_light_col)
  @assert c>=1
  x = A[i, c]
  @assert col_count[c] >= 1
	 @assert col_count[c] > 1 #which???
  if (M !=0 && !iscoprime(x, M))
   continue
  end
  #784-809
  is_one = over_field||isone(x)||isone(-x)
  if best_i < 0
   best_i = i
   best_c = c
   best_len = len
   best_is_one = is_one
   best_x = x
  elseif !best_is_one && is_one
   best_i = i
   best_c = c
   best_len = len
   best_is_one = true
   best_x = x
  elseif (is_one == best_is_one && len < best_len)
   best_i = i
   best_c = c
   best_len = len
   best_is_one = is_one
   best_x = x
  end
 end
 #831-907
 if best_i < 0
  # find hext heavies light_cols by col_count (heavy extension)
  hext = max(div(nlight,100),1)
  nheavy = A.c - (nlight + nsingle)
  if nheavy == 0
   hext = max(div(nlight,20),1)
  else
   hext = max(div(nlight,1000),1)
  end
  harray = fill(-1, hext) #indices (descending order for same length)
  hc = fill(-1, hext)#length of cols in harray (ascending)
  for i = A.c:-1:1
   if is_light_col[i]
    c = col_count[i]
    if c > hc[1]
     if hext == 1
      harray[1] = i #why not c>=???
      hc[1] = c
     else
     #jk = hext
      for j = hext:-1:2  #falsche Schleifen, für hext = 1 
       if c >= hc[j]  
        for k = 1:j-1
         harray[k] = harray[k + 1]
         hc[k] = hc[k + 1]
        end
        harray[j] = i
        hc[j] = c
        break
       end 
      end
     end
    end
   end
  end
  #864-903
  for j = 1:hext
   c = harray[j]
   if c<0
    continue
   end
   is_light_col[c] = false
   L = col_list[c]
   L_len = length(L)
   #873 - 902
   for k = 1:L_len
    L_row = L[k]
    i = col_list_permi[L_row]
    v = A[i]
    @assert light_weight[i] > 0
    light_weight[i]-=1
    w = light_weight[i]
    @vprint :StructGauss 3 "i: $i, w: $w"
    alpha = length(findall(x->is_light_col[x], A[i].pos))
    @vprint :StructGauss 3 "w_Lrow: $alpha"
    if w == 0
     if i < single_row_limit
      swap_rows_perm(A, i, base, col_list_perm, col_list_permi)
     else
      if i != single_row_limit
       swap_rows_perm(A, base, single_row_limit, col_list_perm, col_list_permi)
      end
      single_row_limit+=1
      swap_rows_perm(A, base, i, col_list_perm, col_list_permi)
     end
     single_col[base] = -1
     #A, Y, single_col, col_count = move_into_Y(Y,A, base)
     push!(Y, deepcopy(A[base]))
     for cc_ in A[base].pos
      @assert !is_light_col[cc_]
      @assert col_count[cc_] > 0
      col_count[cc_]-=1
     end
     A.nnz-=length(A[base])
     empty!(A[base].pos), empty!(A[base].values)
     base+=1
    elseif w == 1
     if i > single_row_limit
      swap_rows_perm(A, i, single_row_limit, col_list_perm, col_list_permi)
     end
     single_row_limit += 1
    end
   end
  end
  nlight -= hext
  continue
 end

 @assert best_i!=-1
 best_v = A[best_i]#!!! search prob?
 best_len = length(best_v)
 @assert best_len > 0
 @assert light_weight[best_i] == 1
 best_c = find_light_entry(best_v.pos, is_light_col)
 @assert is_light_col[best_c]
 best_x = A[best_i, best_c]
 @assert col_count[best_c]>=1 #or SMAT_PRIM_CTX
 #if over_field
 L = col_list[best_c]
 @assert length(L) == col_count[best_c]
 #944-1126
 L_row=0
 while length(L) > 1
  i = 0
  for k = length(L):-1:1
   L_row = L[k]
   i = col_list_permi[L_row]
   if A[i] == best_v
    continue
   end
   if i < base
    continue
   end
   break #make sure that i is saved after loop
  end
  v = A[i]
  vlen = length(v)
  #969-1125
  while true
   @assert best_c in v.pos
   x = A[i, best_c]
   if !over_field && over_Z
    g = gcd(x, best_x)
    xg = div(x, g)
    best_xg = div(best_x, g)
   else
    xg = x
    best_xg = best_x
   end
   for j = 1:vlen
    c = v.pos[j]
    @assert col_count[c] > 0
    col_count[c]-=1
    if (!NEW && is_light_col[c]) #never the case?
     L_row_idx = findirst(isequal(L_row),col_list[c])#wo kommt L_row her???
     deleteat!(col_list[c], L_row_idx)
    end
    if !over_field
     v.values[j] *= best_xg
    end
   end
   if NEW
    L_row_idx = findfirst(isequal(L_row),col_list[best_c])
    deleteat!(col_list[best_c], L_row_idx)
   end
   matrix_nentries -= vlen
   #SVEC_ASSURE_SIZE(tvec, m_svecp_len(v) + best_len)
   add_scaled_row!(A, best_i, i, -xg)#Reihenfolge richtig???
   if (M!=0)
    v = A[i]
    light_weight[i] = 0
    #svec_integer_mod_symmetric(vec[i], M, M2)
   end
   #1060: Update new columns from counts and weight.
   v = A[i]
   vlen = length(A[i])
   e = v.pos
   w = 0
   bound = -1
   for j = 1:vlen
    c = e[j]
    @assert c != best_c
    col_count[c]+=1
    if (!NEW && is_light_col[c])
     index = searchsortedfirst(col_list[c], L_row)
     insert!(col_list[c] ,index, L_row)
    end
    if is_light_col[c]
     w+=1
    end
    #TODO bound = 1079
   end
   light_weight[i] = w
   #SVEC_CHECK(vec[i], use_fp)
   matrix_nentries += vlen
   #CAREFUL IF BEST_I == BASE!!! or: I == BEST_I
   if (w == 0)
    if i < single_row_limit
     swap_rows_perm(A, i, base, col_list_perm, col_list_permi)
    else
     if (i != single_row_limit)
      swap_rows_perm(A, base, single_row_limit, col_list_perm, col_list_permi)
     end
    single_row_limit += 1
    swap_rows_perm(A, base, i, col_list_perm, col_list_permi)
    end
    single_col[base] -= 1
    #A, Y, single_col, col_count = move_into_Y(Y,A, base)
    push!(Y, deepcopy(A[base]))
    for cc_ in A[base].pos
     @assert !is_light_col[cc_]
     @assert col_count[cc_] > 0
     col_count[cc_]-=1
    end
    A.nnz-=length(A[base])
    empty!(A[base].pos), empty!(A[base].values)
    base +=1
   else
    if w == 1
     if i > single_row_limit
      swap_rows_perm(A, i, single_row_limit, col_list_perm, col_list_permi)
     end
     single_row_limit+=1
    end
   end
   break
  end
 end
end#1127

#=
if M!=0
 for i = 1:A.c
  if is_light_col[i] && col_count[i]!=0
   is_light_col[i] = false
   nlight -= 1
  end
 end
end

#delete M2
nlight = length(findall(isequal(true),is_light_col))#as long as nlight doesn't count properly ???

nheavy = A.c - nlight - nsingle #???  nlight =-451, nsingle = 161
heavy_map = fill(-1, A.c)
heavy_mapi = []

j=1
for i = 1:A.c
 if !is_light_col[i] && !is_single_col[i]
  heavy_map[i] = j
  push!(heavy_mapi, i)
  j+=1
 else
  heavy_map[i]=-1
 end
end
@assert j == nheavy+1 
S = sparse_matrix(R)# size A.r x nheavy
S.c = nheavy
r = 1 #use push instead of r since no size f S initialized

for i =1:Y.r
 light_weight[i] = length(Y[i])
end
#sort!(Y.rows, by = x->length(x))#???change to light_weight 1206
for i = 1:Y.r
 for j = 1:length(Y[i])
  c = Y[i].pos[j]
  x = Y[i].values[j]
  @assert(heavy_map[c]>=1)
  #=
  smat_set_entry_pc(
		    SMAT_PRIM_CTX, S, r, heavy_map[c],
		    (*primitives->elt_incref)(ctx, x), vlen
		)???=#
 end
 r+=1
 if r>nheavy + REDUCE_IC_RELS_EXTRA
  break
 end
end

S_sol = smat_solve_mod(S, nheavy, norm_col, M_list, ic) #1756 ???
sol = []
for i = 1:A.c
 if is_light_col[i]
  push!(sol, 0)
 else
  j = heavy_map[i]
  if j>=0
   @assert(0<=S_sol[j]<M)
   sol[i] = S_sol[j]
  else
   sol[i] = -1
  end
 end
end

if S.r == 0 && S.c == 0
 sol[norm_col] = 1 #??? what is norm_col
end

nfail = 0

for i = base:-1:1 #1791
 c = single_col[i]
 if c>=0
  y = 0
  x = NaN
  for j = 1:length(A[i])
   cc = A[i].pos[j]
   xx = A[].values[j]
   if cc == c
    x = xx
   elseif sol[cc] >= 0
    y += xx*sol[cc]#???
   else
    break
   end
  end
  if j < vlen #wo kommt j her?!
   nfail+=1
  else
   y = y%M
   @assert x != NaN && x != 0
   x = x%M
   x = invmod(x, M)
   y = -mulmod(x,y,M)#???nagate = *(-1)?
   y = y%M
   sol[c] = y
  end
 end
end
if sol[norm_col]!=-1
 x = invmod(sol[norm_col], M)
 if x !=0 #always, since inv not 0???
  for i = 1:A.c
   if sol[i]!=-1
    sol[i] = mulmod(sol[i], x, M)
   end
  end
 end
end
=#

function swap_rows_perm(A, i, j, col_list_perm, col_list_permi)
 if i != j
  swap_rows!(A, i, j)
  swap_entries(single_col, i, j)
  swap_entries(col_list_perm, i, j)
  swap_entries(col_list_permi, col_list_perm[i], col_list_perm[j])
  swap_entries(light_weight, i, j)
 end
end 

function swap_entries(v, i,j) #swaps entries v[i], v[j]
 v[i],v[j] = v[j],v[i]
end

function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 for j in position_array[end:-1:1]
  if is_light_col[j]
   return j #smallest index necessary???
  end
 end
end


###aktuelles Sieb###

function primitive_elem(F::FinField,first::Bool) 
 p = length(F)
 Fact = prime_divisors(fmpz(p-1))
 while true # alpha exists
   for y in F
     if !first y = rand(F) end
     if isprime(lift(y))
       if !(any(i->isone(y^divexact(fmpz(p-1),i)), Fact))
         return y
       end
     end
   end
 end
end

@doc Markdown.doc"""
   sieve_params(p,eps::Float64,ratio::Float64) -> Tuple{Int64, Int64, Float64, Tuple{Int64, Int64}}

Returns parameters for sieve.
"""
function sieve_params(p,eps::Float64,ratio::Float64)
 # assymptotic bounds by Coppersmith, Odlyzko, and Schroeppel L[p,1/2,1/2]# L[n,\alpha ,c]=e^{(c+o(1))(\ln n)^{\alpha }(\ln \ln n)^{1-\alpha }}}   for c=1
 qlimit = exp((0.5* sqrt(Base.log(p)*Base.log(Base.log(p)))))
 qlimit *= Base.log(qlimit) # since aproximately    #primes
 climit = exp((0.5+eps)*sqrt(Base.log(p)*Base.log(Base.log(p))))

 qlimit = Int64(ceil(0.5*max(qlimit,30)))
 climit = Int64(ceil(max(climit,35)))
 inc = (Int64(100),Int64(100))
 return qlimit,climit,ratio,inc
end

@doc Markdown.doc"""
   sieve(F::Nemo.GaloisFmpzField,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nothing

Computes coefficient matrix of factorbase logarithms and saves corresponding attributes on $F$.
"""
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.GaloisFmpzField} #F with primitive element as attribute, p at most 35 decimals
p = characteristic(F)
set_attribute!(F, :p=>p)
a = get_attribute(F, :a)
H_fmpz = floor(root(p,2))+1
H1 = H_fmpz +1
H = Int(H_fmpz)
J = Int(H_fmpz^2 - p)
qlimit, climit, ratio, inc = SP
(lift(a) <= qlimit&&isprime(lift(a))) || (a = primitive_elem(F, true)) 
set_attribute!(F, :primitive_elem=>a)

# factorbase up to qlimit
fb_primes = Hecke.primes_up_to(qlimit)
indx = searchsortedfirst(fb_primes, lift(a))
FB = vcat([fmpz(lift(a))],deleteat!(fb_primes,indx))::Vector{fmpz} # swap a[1] = a[2] , a[2] = [1] array
# use shift! / unshift! here...
log2 = Base.log(2.0);
logqs = Float64[Base.log(Int(q))/log2 for q in FB] #real logarithms for sieve 
set_attribute!(F, :FBs=>FactorBase(FB))
FBs = get_attribute(F, :FBs)
l = length(FB)
set_attribute!(F, :fb_length=>l)
Indx = Dict(zip(FB,[i for i=1:l]))::Dict{fmpz, Int} #Index in a dictionary
A = sparse_matrix(zz)
len = []
rel = fmpz(1)
#IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
##########################################################################################################################################
# Sieve for ci
for c1 = 1:climit
  nrows(A)/length(FB) < ratio || break
  Sieve = zeros(climit)
  Hc1 = H + c1;                # denominator of relation
  #num = -(J + c1*H)            # numerator
  for i=1:length(fb_primes)
    q = fb_primes[i]
    qpow = Int(q)
    nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
    logq = logqs[i]
    while qpow < qlimit      # qlimit-smooth
      den_int = Hc1%qpow
      den_int != 0 || break
      num_int = ((-J)%qpow - (c1 %qpow)*(H%qpow))%qpow
      c2 = num_int * invmod(den_int, qpow)  % qpow ###
      (c2 != 0) || (c2 = qpow)
      nextqpow = qpow*q    #increase q_power
      while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
        c2+=qpow
      end
      while c2 <= length(Sieve)
          Sieve[c2] += logq
          if nextqpow > qlimit
              prod1 = J + c1*c2
              prod2 = c1+c2
              nextp = nextqpow
              while (prod1%nextp + (prod2%nextp)*(H%nextp))%nextp == 0
                  Sieve[c2] += logq
                  nextp = nextp*q
              end
          end
          c2 += qpow
      end
      qpow = nextqpow
    end
  end

  #include relations / check sieve for full factorizations.
  mul!(rel, Hc1, H1)

  n = fmpz(1)
  for c2 in 1:length(Sieve)
    if rel > p
      sub!(n, rel, p)
      if n > p
        n = rel %p
      end
    else
      n = p
    end
    nbn = nbits(n)-1
    if abs(Sieve[c2] - nbn) < 1 
      #generate Factorbase based on FBs with new c_i�s
      if issmooth(FBs,n)
        dict_factors = Hecke.factor(FBs,fmpz(n))
        #Include each H + c_i in extended factor basis.
        r = length(Indx)+1
        if !((Hc1) in keys(Indx))
          push!(FB,Hc1)
          push!(Indx, Hc1 => r)
        end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
        r = length(Indx)+1
        Hc2 = H + c2
        if !((Hc2) in keys(Indx))
          push!(FB,Hc2)
          push!(Indx,(Hc2) => r)
        end#(FB = vcat(FB,[H + c2]))
        #Include relation (H + c1)*(H + c2) = fact.
        #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
        J1 = Vector{Int64}([])
        V = Vector{Int64}([])
        for (prime,power) in dict_factors
          if !(power == 0)
            push!(J1,Indx[prime])
            push!(V,Int(power))
          end
        end
        if c1 == c2
          push!(J1,Indx[Hc1])
          push!(V,-2)
        else
          push!(J1,Indx[Hc1])
          push!(J1,Indx[Hc2])
          push!(V,-1)
          push!(V,-1)
        end
        push!(A,sparse_row(zz, J1, V))
        push!(len, length(J1))
      end
    end
    add!(rel, rel, Hc1)
  end
end
#increase Sieve 
if nrows(A)/length(FB) < ratio
  qlimit += inc[1]
  climit += inc[2]
  return sieve(F,(qlimit, climit, ratio, inc))
end
return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :len=>len)
end