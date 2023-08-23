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
 col_list_perm #perm gives new ordering of original A[i] via their indices
 col_list_permi #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col
 is_single_col
 single_col #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position
 heavy_ext
 heavy_col_idx
 heavy_col_len
 heavy_mapi

 function data_StructGauss(A)
  Y = sparse_matrix(base_ring(A), 0, ncols(A))
  col_list = _col_list(A)
  return new(A,
  Y,
  1,
  1,
  ncols(A),
  0,
  [length(A[i]) for i in 1:nrows(A)],
  col_list,
  collect(1:nrows(A)),
  collect(1:nrows(A)),
  fill(true, ncols(A)),
  fill(false, ncols(A)),
  fill(-2, nrows(A)),
  0,
  Int[],
  Int[],
  Int[])
 end
end


function part_echolonize(A)
 over_field = false #more cases are tested this way
 A = delete_zero_rows!(A)
 n = nrows(A)
 m = ncols(A)
 SG = data_StructGauss(A)
 single_rows_to_top!(SG)

 while SG.nlight > 0 && SG.base <= n
  build_part_ref!(SG)
  for i = 1:m
   SG.is_light_col[i] && @assert length(SG.col_list[i]) != 1
  end
  (SG.nlight == 0 || SG.base > n) && break
  best_single_row = find_best_single_row(SG, over_field)
  best_single_row < 0 && @assert(SG.base == SG.single_row_limit)
  
  if best_single_row < 0
   find_dense_cols(SG)
   turn_heavy(SG)
   continue #while SG.nlight > 0 && SG.base <= SG.A.r
  end

  eliminate_and_update(best_single_row, SG)
 end
 return SG
end

function compute_kernel(SG)
 m = ncols(SG.A)
 update_light_cols(SG)
 @assert SG.nlight > -1
 heavy_map = collect_dense_cols(SG)
 d, _dense_kernel = dense_kernel(heavy_map, SG)
 _kernel, single_part = init_kernel(_dense_kernel, heavy_map, SG)
 return compose_kernel(_kernel, single_part, SG)
end

function structured_gauss(A)
 SG = part_echolonize(A)
 _kernel, _ = compute_kernel(SG)
 return _kernel
end

function only_dense_kernel(SG, F)
 m = ncols(SG.A)
 for i = 1:m
  if SG.is_light_col[i] && !isempty(SG.col_list[i])
   SG.is_light_col[i] = false
   SG.nlight -= 1
  end
 end
 @assert SG.nlight > -1
 nheavy = m - SG.nlight - SG.nsingle
 heavy_map = fill(-1, m)
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_single_col[i]
   heavy_map[i] = j
   push!(SG.heavy_mapi,i)  
   j+=1
  end
 end
 @assert length(SG.heavy_mapi)==nheavy

 ST = sparse_matrix(base_ring(SG.A))
 ST.c = SG.Y.r
 YT = transpose(SG.Y)
 for j in SG.heavy_mapi
  push!(ST, YT[j])
 end
 S = transpose(ST)
 #@show(matrix(S))
 d, S_kernel = kernel(matrix(S))
 l = get_attribute(F, :fb_length)
 R = base_ring(SG.A)
 kern = fill(zero(R), l)
 for idx = 1:length(SG.heavy_mapi)
  dense_col = SG.heavy_mapi[idx]
  if SG.heavy_mapi[idx]>l
   break
  else
   kern[dense_col] = S_kernel[idx]
  end
 end
 return kern
end


function small_logs(F, kern)
 kern = inv(kern[1]).*kern
 FB = get_attribute(F, :FB_array)
 l = get_attribute(F, :fb_length)
 
 a1 = F(FB[1])
 M = div(p-1,2)
 Q,L = Array{ZZRingElem}([]),Array{ZZRingElem}([])
 
 for i = 1:l
  c0 = crt(lift(kern[i]), ZZ(M), ZZ(0), ZZ(2))
  if lift(a1^c0)  == FB[i]
   push!(Q,FB[i])
   push!(L, c0)
  else
   c1 = crt(lift(kern[i]), ZZ(M), ZZ(1), ZZ(2))
   if lift(a1^c1)  == FB[i]
    push!(Q,FB[i])
    push!(L, c1)
   end
  end
 end
 
 Logdict = Dict(zip(Q,L))
 set_attribute!(F, :Logdict=>Logdict, :kern=>kern, :Q=>FactorBase(Q))
end

function find_dense_cols(SG)
 m = ncols(SG.A)
 nheavy = m - (SG.nlight + SG.nsingle)
 nheavy == 0 ? SG.heavy_ext = max(div(SG.nlight,20),1) : SG.heavy_ext = max(div(SG.nlight,100),1)
 SG.heavy_col_idx = fill(-1, SG.heavy_ext) #indices (descending order for same length)
 SG.heavy_col_len = fill(-1, SG.heavy_ext)#length of cols in heavy_idcs (ascending)
 light_cols = findall(x->SG.is_light_col[x], 1:m)
 #@show(light_cols)
 for i = m:-1:1
  if SG.is_light_col[i]
   col_len = length(SG.col_list[i])
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
 @assert light_cols == findall(x->SG.is_light_col[x], 1:m)
end

function turn_heavy(SG)
 for j = 1:SG.heavy_ext
  c = SG.heavy_col_idx[j]
  if c<0
   continue
  end
  SG.is_light_col[c] = false
  lt2hvy_col = SG.col_list[c]
  lt2hvy_len = length(lt2hvy_col)
  @assert lt2hvy_len == length(SG.col_list[c])
  for k = 1:lt2hvy_len
   i_origin = lt2hvy_col[k]
   i_now = SG.col_list_permi[i_origin]
   @assert SG.light_weight[i_now] > 0
   SG.light_weight[i_now]-=1
   handle_new_light_weight(i_now, SG)
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
 @show col_list_perm, :Hi
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
function find_best_single_row(SG, over_field)
 best_single_row = -1
 best_col = NaN
 best_val = NaN
 best_len = -1
 best_is_one = false
 for i = SG.base:SG.single_row_limit-1  #here not the case in first loop
  single_row = SG.A[i]
  single_row_len = length(single_row)
  w = SG.light_weight[i]
  @assert w == 1
  j_light = find_light_entry(single_row.pos, SG.is_light_col)
  single_row_val = SG.A[i, j_light]
  @assert length(SG.col_list[j_light]) > 1
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
 end
 return best_single_row
end 

function move_into_Y(i, SG::data_StructGauss)
 @assert i == SG.base
 push!(SG.Y, deepcopy(SG.A[SG.base]))
 for base_c in SG.A[SG.base].pos
  @assert !SG.is_light_col[base_c]
  @assert !isempty(SG.col_list[base_c])
 end
 SG.A.nnz-=length(SG.A[SG.base])
 empty!(SG.A[SG.base].pos), empty!(SG.A[SG.base].values)
end

function _col_list(A)
 n = nrows(A)
 m = ncols(A)
 col_list = [Array{Int64}([]) for i = 1:m]
 for i in 1:n
  for c in A[i].pos
   col = col_list[c]
   push!(col, i)
  end
 end
 return col_list
end

function single_rows_to_top!(SG)
 for i = 1:nrows(SG.A)
  len = length(SG.A[i])
  @assert !iszero(len)
  if len == 1
   @assert SG.single_row_limit <=i
   if i != SG.single_row_limit
    swap_rows_perm(i, SG.single_row_limit, SG)
   end
   SG.single_row_limit +=1
  end
 end
 return SG
end

function build_part_ref!(SG)
 queue = collect(ncols(SG.A):-1:1)
 while !isempty(queue)
  queue_new = Int[]
  for j in queue
   if length(SG.col_list[j])==1 && SG.is_light_col[j]
    singleton_row_origin = only(SG.col_list[j])
    singleton_row_idx = SG.col_list_permi[singleton_row_origin]
    for jj in SG.A[singleton_row_idx].pos
     if SG.is_light_col[jj]
      @assert singleton_row_origin in SG.col_list[jj]
      j_idx = findfirst(isequal(singleton_row_origin), SG.col_list[jj])
      deleteat!(SG.col_list[jj],j_idx)
      length(SG.col_list[jj]) == 1 && push!(queue_new, jj)
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
  queue = queue_new
 end
end

function find_row_to_add_on(best_row, best_col_idces::Vector{Int64}, SG::data_StructGauss)
 for L_row in best_col_idces[end:-1:1] #right??? breaking condition missing?
  row_idx = SG.col_list_permi[L_row]
  SG.A[row_idx] == best_row && continue
  row_idx < SG.base && continue
  return row_idx
 end
end

function add_to_eliminate(L_row, row_idx, best_row, best_col, best_val, SG)
 @assert L_row in SG.col_list[best_col]
 @assert !(0 in SG.A[row_idx].values)
 val = SG.A[row_idx, best_col] 
 @assert !iszero(val)
 #case !over_field && over_Z:
 g = gcd(lift(val), lift(best_val))
 val_red = divexact(val, g)
 best_val_red = divexact(best_val, g)
 @assert L_row in SG.col_list[best_col]
 for c in SG.A[row_idx].pos
  @assert !isempty(SG.col_list[c])
  if SG.is_light_col[c]
   jj = findfirst(isequal(L_row), SG.col_list[c])
   deleteat!(SG.col_list[c], jj)
  end
 end
 scale_row!(SG.A, row_idx, best_val_red)
 @assert !(0 in SG.A[row_idx].values)
 add_scaled_row!(best_row, SG.A[row_idx], -val_red)
 @assert iszero(SG.A[row_idx, best_col])
 return SG
end

function update_after_addition(L_row, row_idx::Int, best_col, SG::data_StructGauss)
 SG.light_weight[row_idx] = 0
 for c in SG.A[row_idx].pos
  @assert c != best_col
  SG.is_light_col[c] && sort!(push!(SG.col_list[c], L_row)) 
  SG.is_light_col[c] && (SG.light_weight[row_idx]+=1)
 end
 return SG
end

function handle_new_light_weight(i, SG)
 w = SG.light_weight[i]
 if w == 0
  swap_i_into_base(i, SG)
  SG.single_col[SG.base] = -1
  #@show SG.col_list_perm[SG.base]
  move_into_Y(SG.base, SG)
  SG.base+=1
 elseif w == 1
  if i > SG.single_row_limit
   swap_rows_perm(i, SG.single_row_limit, SG)
  end
  SG.single_row_limit += 1
 end
 return SG
end

function eliminate_and_update(best_single_row, SG)
 @assert best_single_row != 0
 best_row = deepcopy(SG.A[best_single_row])
 best_col = find_light_entry(best_row.pos, SG.is_light_col)
 @assert length(SG.col_list[best_col]) > 1
 best_val = SG.A[best_single_row, best_col]
 @assert !iszero(best_val)
 best_col_idces = SG.col_list[best_col]
 row_idx = 0
 while length(best_col_idces) > 1
  row_idx = find_row_to_add_on(best_row, best_col_idces, SG)
  @assert best_col_idces == SG.col_list[best_col]
  @assert SG.col_list_perm[row_idx] in SG.col_list[best_col]
  @assert row_idx > 0
  L_row = SG.col_list_perm[row_idx]
  add_to_eliminate(L_row, row_idx, best_row, best_col, best_val, SG)
  update_after_addition(L_row, row_idx, best_col, SG)
  handle_new_light_weight(row_idx, SG)
 end
 return SG
end

function update_light_cols(SG)
 for i = 1:ncols(SG.A)
  if SG.is_light_col[i] && !isempty(SG.col_list[i])
   SG.is_light_col[i] = false
   SG.nlight -= 1
  end
 end
end

function collect_dense_cols(SG)
 m = ncols(SG.A)
 nheavy = m - SG.nlight - SG.nsingle
 heavy_map = fill(-1, m)
 j = 1
 for i = 1:m
  if !SG.is_light_col[i] && !SG.is_single_col[i]
   heavy_map[i] = j
   push!(SG.heavy_mapi,i)  
   j+=1
  end
 end
 @assert length(SG.heavy_mapi)==nheavy
 return heavy_map
end

function dense_kernel(heavy_map, SG)
 ST = sparse_matrix(base_ring(SG.A), 0, SG.Y.r)
 YT = transpose(SG.Y)
 for j in SG.heavy_mapi
  push!(ST, YT[j])
 end
 S = transpose(ST)
 d, _dense_kernel = kernel(matrix(S))
 return d, _dense_kernel
end

function init_kernel(_dense_kernel, heavy_map, SG)
 m = ncols(SG.A)
 R = base_ring(SG.A)
 _kernel = fill(zero(R), m)
 single_part = []
 #@show(kern)
 for i = 1:m
  if SG.is_light_col[i]
   _kernel[i]=zero(R)
  else
   j = heavy_map[i]
   if j>0
    _kernel[i] = _dense_kernel[j,1]
   else
    push!(single_part, i)
   end
  end
 end 
 return _kernel, single_part
end

function compose_kernel(_kernel, single_part, SG)
 nfail = 0
 failure = []
 for i=SG.base-1:-1:1
  c = SG.single_col[i]
  if c>0
   y = 0
   x = NaN
   j=1
   while j <= length(SG.A[i])
    cc = SG.A[i].pos[j]
    xx = SG.A[i].values[j]
    if cc==c
     x = xx
     j+=1
    elseif !(cc in single_part)
     y += (xx*_kernel[cc])
     j+=1
    else
     break
    end
   end
   if j <= length(SG.A[i])
    nfail +=1
    push!(failure, i)
   else
    _kernel[c]=-y*inv(x)
   end
  end
 end 
 return _kernel, failure
end

function test_base_part(SG)
 for i = 1:SG.base-1
  sc = SG.single_col[i]
  sc < 0 && @assert isempty(SG.A[i].pos)
  if sc > 0
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

function test_if_zeros_listed(SG)
 TA = transpose(SG.A)
 for i = 1:ncols(SG.A)
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
 for i = 1:ncols(SG.A)
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

function test_A(SG) #after part_echolonize
 @assert length(findall(x->length(SG.A[x])==0, 1:nrows(SG.A))) == SG.Y.r
 println("$(Y.r) many empty rows in A")
end

function count_nnz(A=SG.A)
 l = 0
 for i = 1:nrows(A)
  l+=length(A[i])
 end
 return l
end

function fb_and_dense(SG)
 l_FB = get_attribute(F, :fb_length)
 return filter(x->x<=l_FB, SG.heavy_mapi)
end
