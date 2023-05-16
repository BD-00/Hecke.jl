using Oscar, TimerOutputs

include("module-StructuredGauss.jl")
using .StructuredGauss

Hecke.add_verbosity_scope(:StructGauss)
Hecke.add_assertion_scope(:StructGauss)

Hecke.set_assertion_level(:StructGauss, 0)
Hecke.set_verbosity_level(:StructGauss, 0)

function swap_rows_perm(A, i, j, col_list_perm, col_list_permi)
 if i != j
  swap_rows!(A, i, j) #swap!(A[i],A[j]) throws error later???
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

#A,i,base,single_row_limit,col_list_perm, col_list_permi
function swap_i_into_base(i,base,single_row_limit)
 if i < single_row_limit
  swap_rows_perm(A, i, base, col_list_perm, col_list_permi)
 else
   if i != single_row_limit 
    swap_rows_perm(A, base, single_row_limit, col_list_perm, col_list_permi)
   end
   single_row_limit +=1
   swap_rows_perm(A, base, i, col_list_perm, col_list_permi)
 end
 return single_row_limit
end

#c light col with only one entry, L_row original row index of entry, i position of A_l_row now
#iterate over col_idx cc of entries in i, decrement their col_count
#add cc to col_consider, if only one other left
#delete L_row in light cc cols
#c now heavy but single_col, move i into base 
function work_with_single_cols(c, matrix_nentries, nlight, nsingle, base, single_row_limit, col_consider_n, col_count)#why col_consider_n necessary???
 @assert c <= length(col_list)
 L = col_list[c]
 @assert(length(L)==1)
 L_row = first(L) #index of row with entry in col c
 i = col_list_permi[L_row]
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

 single_row_limit = swap_i_into_base(i,base,single_row_limit)
 return base+1, single_row_limit, nlight, nsingle, matrix_nentries
end


#i over single_rows not in base (can be empty)
#c idx of last light col entry in row i 
#start with best_i = i...
#compare with following rows i
#prioritize: x=A[i,c] = +-1, minimal length(A[i]) to find best_i
function find_best_i(over_field, len, i, c, x, best_i, best_len, best_is_one)
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
 return best_i
end 


#used if no single_rows after base

#1:go over light cols from right to left
# find hext many heaviest light_cols by col_count (heavy extension)
#if c >hc[1] compare col_count c of col i with element in hc starting left. 
#if c >= hc[j], insert at position j, delete first col in both arrays:
#within block of same col_count: indices descending
#col_count should be increasing
#in general: harray contains light cols with most entries and lowest indices for min col_count in there

#2: iterate over col idces c in harray (and turn them to heavy cols)
#set light_col to false
#iterate over rows L_row (now i) in c
#decrement light_weight[i]
#if light _weight == 0, i to base, then A[base] into Y
#decrement col_count for cols in base, empty A[base] 
#if light_weight == 1, swap i in single_row part after base
function heavy_ext(nlight, nsingle, base, single_row_limit)
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
     for j = hext:-1:2 
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
   if w == 0
    single_row_limit = swap_i_into_base(i,base,single_row_limit)
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
 return base, single_row_limit, nlight
end



function update_zero_weight_row(base, single_row_limit, i, best_i)
 if i < single_row_limit
  swap_rows_perm(A, i, base, col_list_perm, col_list_permi)
  best_i == base && (best_i = deepcopy(i))
 else
  if (i != single_row_limit)
   swap_rows_perm(A, base, single_row_limit, col_list_perm, col_list_permi)
  end
 single_row_limit += 1
 swap_rows_perm(A, base, i, col_list_perm, col_list_permi)
 best_i == base  && (best_i = deepcopy(i))
 end
 single_col[base] -= 1
 #A, Y, single_col, col_count = move_into_Y(Y,A, base)
 push!(Y, deepcopy(A[base]))
 for cc_ in A[base].pos
  @assert !is_light_col[cc_]
  @assert col_count[cc_] > 0
  col_count[cc_]-=1
 end
 @assert length(A[best_i]) > 0
 A.nnz-=length(A[base])
 empty!(A[base].pos), empty!(A[base].values)
 return base+1, single_row_limit, i, best_i
end

#return is_light_col, light_weight, single_col, base, single_row_limit, Y, A, col_count, nlight
#=
#kleines Beispiel ohne Error
p = ZZRingElem(47)
F = GF(p)
a = F(20)
set_attribute!(F, :a=>a)

#mittleres Beispiel ohne Error
p = ZZRingElem(3808986227)
F  = GF(p)
a = GF(2964180501)
set_attribute!(F, :a=>a)

#gro�es Beispiel ohne Error
p = ZZRingElem(28305054749008327163)
F = GF(p)
a = F(6879064112033849389)
set_attribute!(F, :a=>a)
=#

#Beispiel AssertionError: c != best_c in 382
#p = ZZRingElem(9048192719) 
const to = TimerOutput()


p = cryptoprime(35)
F = GF(p)
#a = F(4313590289)
a = Hecke.primitive_element(F)
set_attribute!(F, :a=>a)

#von hier an f�r alle Beispiele gleich

sieve(F, sieve_params(characteristic(F),0.02,1.01))
A = get_attribute(F, :RelMat)
l = get_attribute(F, :fb_length)
TA = delete_zero_rows!(transpose(A), l)
A = transpose(TA)

@timeit to "p = $p" begin
#function StructGauss(p, A, TA)
 #STRUCTURED GAUSS USING TA 
 bound_limit = 2^31 #oder mod?
 base = 1 #indices +1
 single_row_limit = 1
 light_weight = [length(A[i]) for i in 1:A.r]

 over_Z = true
 over_field = false
 norm_col = 1

 NEW = true
 REDUCE_IC_RELS_EXTRA=30000

 R = base_ring(A)
 if R == ZZ #|| R == zz
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

 RR = ResidueRing(ZZ, M)
 B = change_base_ring(RR, deepcopy(A)) #right base_ring???
 #d2, kern = kernel(matrix(B))
 #@assert d2==1
 col_list = []; col_count = []
 for j = 1:A.c
  push!(col_list, TA[j].pos)
  push!(col_count, length(TA[j]))
 end
 #print("$(length(col_list)), ")
 #=
 for i = 1:A.r
  col_list_perm[i] = i; col_list_permi[i] = i
  for j in A[i].pos
   =#

 #480: Mark all coloums light initially

 is_light_col = fill(true, A.c)
 is_single_col = fill(false, A.c)
 single_col = fill(-2, A.r) #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position

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
  global counter, matrix_nentries, nlight, nsingle, single_row_limit, base
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
      #print("c: $c, $(length(col_list)), ")
      base, single_row_limit, nlight, nsingle, matrix_nentries = work_with_single_cols(c, matrix_nentries, nlight, nsingle, base, single_row_limit, col_consider_n, col_count)
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
   best_i = find_best_i(over_field, len, i, c, x, best_i, best_len, best_is_one)
  end
  #831-907
  if best_i < 0
   # find hext many heaviest light_cols by col_count (heavy extension)
   base, single_row_limit, nlight = heavy_ext(nlight, nsingle, base, single_row_limit)
   continue
  end

  @assert best_i!=-1
  @assert length(A[best_i]) > 0 
  best_v = A[best_i]#!!! search prob?
  best_len = length(best_v)
  @assert best_len > 0
  @assert light_weight[best_i] == 1
  best_c = find_light_entry(best_v.pos, is_light_col)
  @assert is_light_col[best_c]
  best_x = A[best_i, best_c]
  @assert best_x != 0
  @assert col_count[best_c]>=1 #or SMAT_PRIM_CTX
  #if over_field
  L = col_list[best_c]
  @assert length(L) == col_count[best_c]
  #944-1126
  L_row=0
  @assert length(A[best_i]) > 0
  while length(L) > 1
   @assert length(A[best_i]) > 0
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
   @assert i >= base && i!=best_i
   v = A[i]
   vlen = length(v)
   #969-1125
   @assert length(A[best_i]) > 0
   while true
    @assert best_c in v.pos
    x = A[i, best_c]
    @assert x!=0
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
    #@show A[i], A[best_i], xg, best_c
    Hecke.add_scaled_row!(A, best_i, i, -xg)#Reihenfolge richtig???
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
    if (w == 0)
     base, single_row_limit, i, best_i = update_zero_weight_row(base, single_row_limit, i, best_i)
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
 #A: 279x276
 #Y: 41x276
 #eine leere Spalte in A
 #239 leere Spalten in Y
 #nach col_count 276 empty
 #238 single_col
 if M!=0
  for i = 1:A.c
   if is_light_col[i] && col_count[i]!=0
    is_light_col[i] = false
    nlight -= 1
   end
  end
 end

 #delete M2
 # = length(findall(isequal(true),is_light_col))#as long as nlight doesn't count properly ???

 nheavy = A.c - nlight - nsingle #???  nlight =-451, nsingle = 161
 heavy_map = fill(-1, A.c) #index in mapi of heavy col else -1
 heavy_mapi = [] #indices of heavy cols <

 j=1
 for i = 1:A.c
  if !is_light_col[i] && !is_single_col[i] #heavy col
   heavy_map[i] = j
   push!(heavy_mapi, i)
   j+=1
  end
 end
 @assert j == nheavy+1 
 S = sparse_matrix(R)# size A.r x nheavy
 S.c = nheavy #use push instead of r since no size f S initialized

 Y_light_weight = [length(y) for y in Y.rows]
 for i =1:Y.r
  Y_light_weight[i] = length(Y[i])
 end

 #sort!(Y.rows, by = x->length(x))#???change to light_weight 1206
 for i = 1:Y.r
  Srow_pos = Vector{Int64}([])
  Srow_val = Vector{ZZRingElem}([])
  for j in Y[i].pos 
   @assert(heavy_map[j]>=0)
   push!(Srow_pos, heavy_map[j])
   push!(Srow_val,Y[i,j])
  end
  sp_row = sparse_row(R, Srow_pos, Srow_val)
  push!(S, sp_row)
 end

 d, S_sol = kernel(change_base_ring(RR, matrix(S)))
 #right now entries of sol integers 
 d == 1 || return d, []
 sol = Vector{ZZRingElem}([])
 for i = 1:A.c
  if is_light_col[i]
   push!(sol, 0)
  else
   j = heavy_map[i]
   if j>=1
    @assert(0<=lift(S_sol[j])<M)
    push!(sol,lift(S_sol[j]))
   else
    push!(sol,-1)
   end
  end
 end

 if S.r == 0 && S.c == 0
  sol[norm_col] = 1 #??? what is norm_col
 end

 nfail = 0

 for i = base-1:-1:1 #1791 #base-1???
  c = single_col[i]
  if c>=0
   y = 0
   x = NaN
   j = 1
   while j<= length(A[i])
    cc = A[i].pos[j]
    xx = A[i].values[j]
    if cc == c
     x = xx
    elseif sol[cc] >= 0
     y += xx*sol[cc]#???
    else
     break
    end
    j+=1
   end
   if j < length(A[i]) #wo kommt j her?!
    nfail+=1
   else
    y = y%M
    #@assert x != NaN && x != 0
    x = x%M
    x = invmod(x, M)

    y = -mulmod(x,y,M)#???negate = *(-1)?
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
 return d, sol
#end

end#time

show(to)


kern = lift(kern)

for i = 1:l
 if sol[i]!=kern[i]
 print("$i, ")
 end 
 end
#10x10 5x5 dichter Teil 