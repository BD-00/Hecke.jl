using Oscar

include("module-StructuredGauss.jl")
using .StructuredGauss

p = ZZRingElem(47)
F = GF(p)
a = F(20)
set_attribute!(F, :a=>a)
sieve(F, sieve_params(characteristic(F),0.02,1.1))
a = get_attribute(F, :primitive_elem)
modulus = div(p-1,2)
RelMat = get_attribute(F, :RelMat)
d1, kern_RelMat = kernel(matrix(RelMat))
R = ResidueRing(ZZ, modulus)
A = change_base_ring(R, RelMat)
d2, kernel_original_A = kernel(matrix(A))
TA = transpose(A)


function my_StructGauss(A, TA, F, p)
 #initialize all arrays (and constants)
 single_row_limit = 1
 light_weight = [length(A[i]) for i in 1:A.r]
 base = 1
 col_list = []; col_count = []
 for j = 1:A.c
  push!(col_list, TA[j].pos)
  push!(col_count, length(TA[j]))
 end
 col_list_perm = [i for i = 1:A.r]  #perm gives new ordering of original A[i] via their indices
 col_list_permi = [i for i = 1:A.r] #A[permi[i]]=A[i] before permutation = list of sigma(i) (recent position of former A[i])
 is_light_col = fill(true, A.c)
 is_single_col = fill(false, A.c)
 single_col = fill(-2, A.r) #single_col[i] = c >= 0 if col c has its only entry in row i, i always recent position

 nlight = A.c #number of light cols
 nsingle = 0
 #delete empty rows and swap those with only one variable to top
 for i = 1:A.r
  len = length(A[i])
  if len == 0
   delete_row!(A, i)
  elseif len == 1
   @assert single_row_limit <=i
   if i != single_row_limit
    swap_rows_perm(A, i, single_row_limit, single_col, col_list_perm, col_list_permi, light_weight)
   end
   single_row_limit +=1
  end
 end 
 
#move rows to singleton cols to the top
 1 in col_count ? still_singletons = true : still_singletons = false
 #iter = 0
 while still_singletons
  still_singletons = false
  #iter +=1
  for j = A.c:-1:1
   if col_count[j]==1
    still_singletons = true
    singleton_row = first(col_list[j])
    for jj in A[singleton_row].pos
     col_count[jj]-=1
     delete!(col_list[jj],1)
    end
    if singleton_row < single_row_limit
     swap_rows_perm(A, singleton_row, base, single_col, col_list_perm, col_list_permi, light_weight)
    else
      if singleton_row != single_row_limit 
       swap_rows_perm(A, base, single_row_limit, single_col, col_list_perm, col_list_permi, light_weight)
      end
      single_row_limit +=1
      swap_rows_perm(A, base, singleton_row, single_col, col_list_perm, col_list_permi, light_weight)
    end
    base+=1
   end
  end
 end
 return base, col_count
end

base, col_count =  my_StructGauss(A, TA, F, p)

function swap_rows_perm(A, i, j, single_col, col_list_perm, col_list_permi, light_weight)
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