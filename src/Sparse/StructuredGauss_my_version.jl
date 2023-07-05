#=
using Oscar
include("module-StructuredGauss.jl")
using .StructuredGauss
=#

function my_StructGauss(A, TA, p, SG)
 #initialize all arrays (and constants)
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
 col_list_perm = [i for i = 1:A.r]  #perm gives new ordering of original A[i] via their indices
 col_list_permi = [i for i = 1:A.r] #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col = fill(true, A.c)
 is_single_col = fill(false, A.c)
 single_col = fill(-2, A.r) #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position

 #delete empty rows and swap those with only one variable to top
 for i = 1:A.r
  len = length(A[i])
  if len == 0
   delete_row!(A, i)
  elseif len == 1
   @assert single_row_limit <=i
   if i != single_row_limit
    swap_rows_perm(A, i, single_row_limit, col_list_perm, col_list_permi, light_weight)
   end
   single_row_limit +=1
  end
 end 
 
#move rows to SINGLETON COLS to the top
 1 in col_count ? still_singletons = true : still_singletons = false
 while still_singletons
  still_singletons = false
  for j = A.c:-1:1
   if col_count[j]==1 && is_light_col[j]
    @assert length(col_list[j])==1
    still_singletons = true
    singleton_row_origin = first(col_list[j])
    singleton_row_idx = col_list_permi[singleton_row_origin]
    for jj in A[singleton_row_idx].pos
     if is_light_col[jj]
      j_idx = findfirst(isequal(singleton_row_idx), col_list[jj])
      col_count[jj]-=1
      deleteat!(col_list[jj],j_idx)
     end
    end
    is_light_col[j] = false
    is_single_col[j] = true
    nlight-=1
    nsingle+=1
    @show col_list_perm
    single_row_limit = swap_i_into_base(A, singleton_row_idx, base, single_row_limit, col_list_perm, col_list_permi, light_weight)
    @show col_list_perm
    single_col[base] = j
    base+=1
   end
  end
 end
 @assert !(1 in col_count)
 return base, single_row_limit, nsingle, nlight, single_col, col_list_perm, col_list_permi, light_weight
end


function swap_rows_perm(A, i, j, col_list_perm, col_list_permi, light_weight)
 if i != j
  swap_rows!(A, i, j) #swap!(A[i],A[j]) throws error later???
  #swap_entries(single_col, i, j)
  swap_entries(col_list_perm, i, j)
  swap_entries(col_list_permi, col_list_perm[i], col_list_perm[j])
  swap_entries(light_weight, i, j)
 end
 @show col_list_perm, :Hi
end 

function swap_entries(v, i,j) #swaps entries v[i], v[j]
 v[i],v[j] = v[j],v[i]
end

function swap_i_into_base(A, i, j, single_row_limit, col_list_perm, col_list_permi, light_weight)
 if i < single_row_limit
  swap_rows_perm(A, i, j, col_list_perm, col_list_permi, light_weight)
 else
   if i != single_row_limit 
    swap_rows_perm(A, i, j, col_list_perm, col_list_permi, light_weight)
   end
   single_row_limit +=1
   swap_rows_perm(A, i, j, col_list_perm, col_list_permi, light_weight)
 end
 @show col_list_perm, i, j
 return single_row_limit
end


#Some test functions
function test_base_part(single_row_limit, base)
 for i = 1:base-1
  sc = single_col[i]
  @assert col_count[sc] == 0
  @assert length(col_list[sc]) == 0
  @assert is_single_col[sc]
  @assert !is_light_col[sc]
 end
 single_row_limit<base && print("srl<base")
 if single_row_limit>base
  for i = base:single_row_limit-1
   @assert light_weight[i] == 1
  end
 end
end

function test_permutation()
 for i = 1:length(col_list_perm)
  @assert col_list_perm[col_list_permi[i]] == i
 end
end

function test_light_weight()
 for i = 1:length(light_weight)
  @assert light_weight[i]==length(filter(x->is_light_col[x], A[i].pos))
 end
end

#=
@doc raw"""
    swap_cols!(TA, A, i1, i2) -> SMat

Used in Structured Gauss to swap cols i1, i2 in TA before swapping rows A[i1], A[i2] in A.
"""

function swap_cols!(TA, A, i1, i2)
 l1 = length(A[i1])
 l2 = length(A[i2])
 i1_pos_idx = 1
 i2_pos_idx = 1
 Pos1 = A[i1].pos
 Pos2 = A[i2].pos
 Val1 = A[i1].values
 Val2 = A[i2].values
 while i1_pos_idx<=l1 && i2_pos_idx<=l2
  j1 = Pos1[i1_pos_idx]
  j2 = Pos2[i2_pos_idx]
  if j1 == j2
   j1_pos_idx = findfirst(isequal(i1), TA[j1].pos) 
   j2_pos_idx = findfirst(isequal(i2), TA[j2].pos)
   TA[j1].values[j1_pos_idx], TA[j1].values[j2_pos_idx] = TA[j1].values[j2_pos_idx], TA[j1].values[j1_pos_idx]
   i1_pos_idx += 1
   i2_pos_idx += 1
  elseif j1 < j2
   j1_pos_idx = findfirst(isequal(i1), TA[j1].pos) 
   v1 = TA[j1].values[j1_pos_idx]
   deleteat!(TA[j1].pos, j1_pos_idx)
   deleteat!(TA[j1].values, j1_pos_idx)
   j2_pos_idx = findfirst(>(i2), TA[j1].pos) 
   if typeof(j2_pos_idx) == Nothing
    push!(TA[j1].pos, i2)
    push!(TA[j1].values, v1)
   else 
    j2_pos_idx += 1
    insert!(TA[j1].pos, j2_pos_idx, i2)
    insert!(TA[j1].values, j2_pos_idx, v1)
   end
   i1_pos_idx+=1
  else
   j2_pos_idx = findfirst(isequal(i2), TA[j2].pos) 
   v2 = TA[j2].values[j2_pos_idx]
   deleteat!(TA[j2].pos, j2_pos_idx)
   deleteat!(TA[j2].values, j2_pos_idx)
   j1_pos_idx = findfirst(>(i1), TA[j2].pos) 
   if typeof(j1_pos_idx) == Nothing
    push!(TA[j2].pos, i1)
    push!(TA[j2].values, v2)
   else 
    j1_pos_idx += 1
    insert!(TA[j2].pos, j1_pos_idx, i1)
    insert!(TA[j2].values, j1_pos_idx, v2)
   end
   i2_pos_idx+=1
  end
 end
 while i1_pos_idx<=l1
  j1 = Pos1[i1_pos_idx]
  j1_pos_idx = findfirst(isequal(i1), TA[j1].pos) 
  v1 = TA[j1].values[j1_pos_idx]
  deleteat!(TA[j1].pos, j1_pos_idx)
  deleteat!(TA[j1].values, j1_pos_idx)
  j2_pos_idx = findfirst(>(i2), TA[j1].pos) 
  if typeof(j2_pos_idx) == Nothing
   push!(TA[j1].pos, i2)
   push!(TA[j1].values, v1)
  else 
   j2_pos_idx += 1
   insert!(TA[j1].pos, j2_pos_idx, i2)
   insert!(TA[j1].values, j2_pos_idx, v1)
  end
  i1_pos_idx+=1
 end
 while i2_pos_idx<=l2
  j2 = Pos2[i2_pos_idx]
  j2_pos_idx = findfirst(isequal(i2), TA[j2].pos) 
  v2 = TA[j2].values[j2_pos_idx]
  deleteat!(TA[j2].pos, j2_pos_idx)
  deleteat!(TA[j2].values, j2_pos_idx)
  j1_pos_idx = findfirst(>(i1), TA[j2].pos) 
  if typeof(j1_pos_idx) == Nothing
   push!(TA[j2].pos, i1)
   push!(TA[j2].values, v2)
  else 
   j1_pos_idx += 1
   insert!(TA[j2].pos, j1_pos_idx, i1)
   insert!(TA[j2].values, j1_pos_idx, v2)
  end
  i2_pos_idx+=1
 end
 return TA
end
=#

mutable struct SG
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
end