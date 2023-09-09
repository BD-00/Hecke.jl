#=
using Oscar
include("module-StructuredGauss.jl")
using .StructuredGauss
=#

mutable struct data_StructGauss
 A
 Y
 single_row_limit
 base
 nlight
 nsingle
 light_weight
 col_list
 col_count
 col_list_perm 
 col_list_permi
 is_light_col
 is_single_col
 single_col
 heavy_ext
 heavy_col_idx
 heavy_col_len
end


function my_StructGauss_1(A, TA)
 #initialize all arrays (and constants)
 over_field = false #more cases are tested this way
 single_row_limit = 1
 base = 1
 nlight = A.c #number of light cols
 nsingle = 0
 light_weight = [deepcopy(length(A[i])) for i in 1:A.r]
 col_list = []; col_count = []
 for j = 1:A.c
  Pos = deepcopy(TA[j].pos)
  push!(col_list, Pos)
  push!(col_count, length(Pos))
 end
 col_list_perm = collect(1:A.r)  #perm gives new ordering of original A[i] via their indices
 col_list_permi = collect(1:A.r) #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col = fill(true, A.c)
 is_single_col = fill(false, A.c)
 single_col = fill(-2, A.r) #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
 Y = sparse_matrix(base_ring(A))
 Y.c = A.c
 SG = data_StructGauss(A,Y,single_row_limit,base,nlight,nsingle,light_weight,col_list,col_count,col_list_perm ,col_list_permi,is_light_col,is_single_col,single_col, 0, [], [])
 #delete empty rows and swap those with only one variable to top
 for i = 1:A.r
  len = length(A[i])
  if len == 0
   delete_row!(A, i)
  elseif len == 1
   @assert SG.single_row_limit <=i
   if i != SG.single_row_limit
    swap_rows_perm(i, SG.single_row_limit, SG)
   end
   SG.single_row_limit +=1
  end
 end 
 while SG.nlight > 0 && SG.base <= SG.A.r
#move rows to SINGLETON COLS to the top
  1 in SG.col_count ? still_singletons = true : still_singletons = false
  while still_singletons
   still_singletons = false
   for j = SG.A.c:-1:1
    if SG.col_count[j]==1 && SG.is_light_col[j]
     @assert length(SG.col_list[j])==1
     still_singletons = true
     singleton_row_origin = first(SG.col_list[j])
     singleton_row_idx = SG.col_list_permi[singleton_row_origin]
     for jj in A[singleton_row_idx].pos
      SG.col_count[jj]-=1
      if SG.is_light_col[jj]
       @assert singleton_row_origin in SG.col_list[jj]
       j_idx = findfirst(isequal(singleton_row_origin), SG.col_list[jj])
       deleteat!(SG.col_list[jj],j_idx)
      end
     end
     SG.is_light_col[j] = false
     SG.is_single_col[j] = true
     SG.single_col[singleton_row_idx] = j
     SG.nlight-=1
     #SG.nlight<0 && print("nlight < 0 singleton case")
     SG.nsingle+=1
     swap_i_into_base(singleton_row_idx, SG)
     SG.base+=1
    end
   end
   #(SG.nlight == 0 || SG.base == SG.A.r) && break
  end
  for i = 1:A.c
   SG.is_light_col[i] && @assert SG.col_count[i] != 1
  end
  (SG.nlight == 0 || SG.base > SG.A.r) && break

  #Find best row which is single (having only one light entry)
  best_single_row = -1
  best_col = NaN
  best_val = NaN
  best_len = -1
  best_is_one = false
  best_fill = 1e10
  for i = SG.base:SG.single_row_limit-1  #here not the case in first loop
   single_row = SG.A[i]
   single_row_len = length(single_row)
   w = SG.light_weight[i]
   @assert w == 1
   j_light = find_light_entry(single_row.pos, SG.is_light_col)
   @assert SG.col_count[j_light]>=1
   single_row_val = SG.A[i, j_light]
   @assert SG.col_count[j_light] > 1 # >= ???
   #=
   if (M !=0 && !iscoprime(single_row_val, M))
    continue
   end
   =#
   best_single_row = find_best_i(over_field, single_row_len, i, j_light, single_row_val, best_single_row, best_len, best_is_one)
  end
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  #no best_i found:
  if best_single_row < 0
   heavy_ext_p1(SG)
   heavy_ext_p2(SG)
   #@show(findall(x->SG.is_light_col[x], 1:SG.A.c))
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end
  #@show(best_single_row)
  @assert best_single_row != 0
  best_row = deepcopy(SG.A[best_single_row])
  best_len = length(best_row)
  best_col = find_light_entry(best_row.pos, SG.is_light_col)
  best_val = deepcopy(SG.A[best_single_row, best_col])
  @assert SG.col_count[best_col] > 1
  best_col_idces = SG.col_list[best_col]
  @assert SG.col_count[best_col] == length(best_col_idces)
  row_idx = 0
  while length(best_col_idces) > 1
   for L_row in best_col_idces[end:-1:1] #right??? breaking condition missing?
    row_idx = SG.col_list_permi[L_row]
    SG.A[row_idx] == best_row && continue
    row_idx < base && continue
    break
   end
   row_len = length(SG.A[row_idx])
   #L_row < 1 && break when can this be the case???
   @assert row_idx > 0
   #@show SG.A[row_idx]
   L_row = SG.col_list_perm[row_idx]#hopefully right
   while true#!!!
    val = SG.A[row_idx, best_col] 
    @assert !iszero(val)
    #case !over_field && over_Z:
    g = gcd(lift(val), lift(best_val))
    val_red = divexact(val, g)
    best_val_red = divexact(best_val, g)
    @assert L_row in SG.col_list[best_col]
    for c in SG.A[row_idx].pos
     @assert SG.col_count[c] > 0
     SG.col_count[c] -= 1
     if SG.is_light_col[c]
      jj = findfirst(isequal(L_row), SG.col_list[c])
      deleteat!(SG.col_list[c], jj)
     end
    end
    scale_row!(SG.A, row_idx, best_val_red)
    #jj = findfirst(isequal(L_row), SG.col_list[best_col]) 
    #deleteat!(SG.col_list[best_col], jj)
    add_scaled_row!(best_row, SG.A[row_idx], -val_red)
    @assert iszero(SG.A[row_idx, best_col])
    SG.light_weight[row_idx] = 0
    for c in SG.A[row_idx].pos
     @assert c != best_col
     SG.col_count[c] += 1
     #but not new:???
     if SG.is_light_col[c]
      sort!(push!(col_list[c], L_row)) 
     end
     SG.is_light_col[c] && (SG.light_weight[row_idx]+=1)
    end
    if SG.light_weight[row_idx] == 0
     swap_i_into_base(row_idx, SG)
     SG.single_col[SG.base] = -1
     #@show SG.col_list_perm[SG.base]
     move_into_Y(SG.base, SG)
     SG.base += 1
    else
     if SG.light_weight[row_idx] == 1
      row_idx > SG.single_row_limit && swap_rows_perm(row_idx, SG.single_row_limit, SG)
      SG.single_row_limit += 1
     end
    end
    #test_Y(SG)
    #test_permutation(SG)
    #test_base_part(SG)
    #test_light_weight(SG)
    #test_col_count(SG)
    #test_if_zeros_listed(SG)
    #test_col_list(SG)
    break #while true
   end
  end
 end
 return SG
end

function my_StructGauss_2(SG)
 for i = 1:SG.A.c
  if SG.is_light_col[i] && SG.col_count[i]>0
   SG.is_light_col[i] = false
   SG.nlight -= 1
  end
 end
 @assert SG.nlight > -1
 nheavy = SG.A.c - SG.nlight - SG.nsingle
 #@show(nheavy)
 heavy_map = fill(-1, SG.A.c)
 heavy_mapi = []
 j = 1
 for i = 1:SG.A.c
  if !SG.is_light_col[i] && !SG.is_single_col[i]
   heavy_map[i] = j
   push!(heavy_mapi,i)  
   j+=1
  end
 end
 @show(heavy_mapi)
 @assert length(heavy_mapi)==nheavy
 #@show(heavy_mapi)
 ST = sparse_matrix(base_ring(SG.A))
 ST.c = SG.Y.r
 YT = transpose(SG.Y)
 for j in heavy_mapi
  push!(ST, YT[j])
 end
 S = transpose(ST)
 #@show(matrix(S))
 d, S_kern = kernel(matrix(S))
 #@show(d)
 #@show(S_kern)
 #@assert d==1
 #eigentlichen Kern zusammensetzen:
 R = base_ring(SG.A)
 kern = fill(zero(R), SG.A.c)
 single_part = []
 #@show(kern)
 for i = 1:SG.A.c
  if SG.is_light_col[i]
   kern[i]=zero(R)
  else
   j = heavy_map[i]
   if j>0
    kern[i] = S_kern[j,1]
   else
    push!(single_part, i)
   end
  end
 end 
 #@show(single_part)
 #single_col Lösungen zusammensetzen
 nfail = 0
 failure = []
 for i=SG.base-1:-1:1
  c = SG.single_col[i]
  if c>0
   y = 0
   x = NaN
   j=1
   while j <= length(SG.A[i])
    cc = A[i].pos[j]
    xx = A[i].values[j]
    if cc==c
     x = xx
     j+=1
    elseif !(cc in single_part)
     y += (xx*kern[cc])
     j+=1
    else
     break
    end
   end
   if j <= length(SG.A[i])
    nfail +=1
    push!(failure, i)
   else
    kern[c]=-y*inv(x)
   end
  end
 end 
 @show(nfail)
 return kern, failure
end



function heavy_ext_p1(SG)
 nheavy = SG.A.c - (SG.nlight + SG.nsingle)
 nheavy == 0 ? SG.heavy_ext = max(div(SG.nlight,20),1) : SG.heavy_ext = max(div(SG.nlight,100),1)
 SG.heavy_col_idx = fill(-1, SG.heavy_ext) #indices (descending order for same length)
 SG.heavy_col_len = fill(-1, SG.heavy_ext)#length of cols in heavy_idcs (ascending)
 light_cols = findall(x->SG.is_light_col[x], 1:SG.A.c)
 #@show(light_cols)
 for i = A.c:-1:1
  if SG.is_light_col[i]
   col_len = SG.col_count[i]
   if col_len > SG.heavy_col_len[1]
    if SG.heavy_ext == 1
     SG.heavy_col_idx[1] = i 
     SG.heavy_col_len[1] = col_len
    else
    #jk = SG.heavy_ext
     for j = SG.heavy_ext:-1:2 
      if col_len >= SG.heavy_col_len[j]  
       for k = 1:j-1
        SG.heavy_col_idx[k] = SG.heavy_col_idx[k + 1]#replace by delete and insert!!!
        SG.heavy_col_len[k] = SG.heavy_col_len[k + 1]
       end
       SG.heavy_col_idx[j] = i
       SG.heavy_col_len[j] = col_len
       break
      end 
     end
    end
   end
  end
 end
 @assert light_cols == findall(x->SG.is_light_col[x], 1:SG.A.c)
end

function heavy_ext_p2(SG)
 for j = 1:SG.heavy_ext
  c = SG.heavy_col_idx[j]
  if c<0
   continue
  end
  SG.is_light_col[c] = false
  lt2hvy_col = SG.col_list[c]
  lt2hvy_len = length(lt2hvy_col)
  @assert lt2hvy_len == SG.col_count[c]
  for k = 1:lt2hvy_len
   i_origin = lt2hvy_col[k]
   i_now = SG.col_list_permi[i_origin]
   @assert SG.light_weight[i_now] > 0
   SG.light_weight[i_now]-=1
   w = SG.light_weight[i_now]
   if w == 0
    swap_i_into_base(i_now,SG)
    SG.single_col[SG.base] = -1
    #@show SG.col_list_perm[SG.base]
    move_into_Y(SG.base, SG)
    SG.base+=1
   elseif w == 1
    if i_now > SG.single_row_limit
     swap_rows_perm(i_now, SG.single_row_limit, SG)
    end
    SG.single_row_limit += 1
   end
   #test_Y(SG)
  end
 end
 SG.nlight -= SG.heavy_ext
 #SG.nlight<0 && print("nlight < 0 extension case")
end

function swap_rows_perm(i, j, SG)
 if i != j
  swap_rows!(SG.A, i, j) #swap!(A[i],A[j]) throws error later???
  swap_entries(SG.single_col, i, j)
  swap_entries(SG.col_list_perm, i, j)
  swap_entries(SG.col_list_permi, SG.col_list_perm[i], SG.col_list_perm[j])
  swap_entries(SG.light_weight, i, j)
 end
end 

function swap_entries(v, i,j) #swaps entries v[i], v[j]
 v[i],v[j] = v[j],v[i]
end

function swap_i_into_base(i, SG::data_StructGauss)
 if i < SG.single_row_limit
  swap_rows_perm(i, SG.base, SG)
 else
   if i != SG.single_row_limit 
    swap_rows_perm(SG.base, SG.single_row_limit, SG)
   end
   SG.single_row_limit +=1
   swap_rows_perm(SG.base, i, SG)
 end
end

function find_light_entry(position_array::Vector{Int64}, is_light_col::Vector{Bool})::Int64
 for j in position_array[end:-1:1]
  if is_light_col[j]
   return j
  end
 end
end

#is_one first, then length
function find_best_i(over_field, single_row_len, i, j_light, single_row_val, best_single_row, best_len, best_is_one)
 is_one = over_field||isone(single_row_val)||isone(-single_row_val)
 if best_single_row < 0
  best_single_row = i
  best_col = j_light
  best_len = single_row_len
  best_is_one = is_one
  best_val = single_row_val
 elseif !best_is_one && is_one
  best_single_row = i
  best_col = j_light
  best_len = single_row_len
  best_is_one = true
  best_val = single_row_val
 elseif (is_one == best_is_one && single_row_len < best_len)
  best_single_row = i
  best_col = j_light
  best_len = single_row_len
  best_is_one = is_one
  best_val = single_row_val
 end
 return best_single_row
end 

function move_into_Y(i, SG::data_StructGauss)
 @assert i == SG.base
 push!(SG.Y, deepcopy(SG.A[SG.base]))
 for base_c in SG.A[SG.base].pos
  @assert !SG.is_light_col[base_c]
  @assert SG.col_count[base_c] > 0
  SG.col_count[base_c]-=1
 end
 SG.A.nnz-=length(A[SG.base])
 empty!(SG.A[SG.base].pos), empty!(SG.A[SG.base].values)
end


#Some test functions

function test_base_part(SG)
 for i = 1:SG.base-1
  sc = SG.single_col[i]
  sc < 0 && @assert isempty(SG.A[i].pos)
  if sc > 0
   @assert SG.col_count[sc] == 0
   @assert length(SG.col_list[sc]) == 0
   @assert SG.is_single_col[sc]
   @assert !SG.is_light_col[sc]
  #@assert length(filter(x->SG.is_light_col[x], SG.A[i].pos)) == 0
  end
 end
 #SG.single_row_limit<SG.base && print("srl<base")
 println("base part seems fine")
end

function test_single_rows(SG)
 if SG.single_row_limit>SG.base
  for i = SG.base:SG.single_row_limit-1
   @assert SG.light_weight[i] == 1
  end
 end
 println("single rows seem fine")
end

function test_permutation(SG)
 for i = 1:length(SG.col_list_perm)
  @assert SG.col_list_perm[SG.col_list_permi[i]] == i
 end
 println("permutation seems fine")
end


#not the case
function test_light_weight(SG)
 for i = SG.base:length(SG.light_weight)
  #@show i
  @assert SG.light_weight[i]==length(filter(x->SG.is_light_col[x], SG.A[i].pos))
 end
 println("light weight seems fine")
end
#teste, ob Sachen für immer in base und weight dort egal

function test_col_count(SG)
 for i = 1:SG.A.c
  SG.is_light_col[i] && @assert length(SG.col_list[i]) == SG.col_count[i]
 end
 println("col count seems fine")
end

function test_if_zeros_listed(SG)
 TA = transpose(SG.A)
 for i = 1:SG.A.c
  if SG.is_light_col[i]
   for j in SG.col_list[i]
    @assert !iszero(SG.A[SG.col_list_permi[j],i])
   end
  end
 end
 println("no zeros listed")
end

function test_col_list(SG)
 TA = transpose(SG.A)
 for i = 1:SG.A.c
  if SG.is_light_col[i]
   first(SG.col_list[i]) >= SG.base || @show 0, SG.col_list[i]
   col_len = length(SG.col_list[i])
   col_len == length(TA[i].pos) || @show 1, TA[i], SG.col_list[i]
   for j = 1:col_len
    if SG.col_list[i][j]>=SG.base
     TA[i].pos[j] == SG.col_list_permi[SG.col_list[i][j]] || @show 2, TA[i], SG.col_list[i]
    end
   end
  end
 end
end

function test_Y(SG)
 for i = 1:SG.Y.r
  for j in SG.Y[i].pos
   @assert !SG.is_light_col[j]
  end
 end
 println("Y is heavy")
end

function test_A(SG) #after ma_StructGauss_1
 @assert length(findall(x->length(SG.A[x])==0, 1:SG.A.r)) == SG.Y.r
 println("$(Y.r) many empty rows in A")
end

function count_nnz(A=SG.A)
 l = 0
 for i = 1:A.r
  l+=length(A[i])
 end
 return l
end
