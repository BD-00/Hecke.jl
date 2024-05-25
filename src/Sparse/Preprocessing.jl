###############################################################################
#
#   PREPROCESSING FOR SPARSE MATRICES
#
###############################################################################

function smat_prepro(A, l = 0)
 R = base_ring(A)
 n = nrows(A)
 m = ncols(A)
 col_list = [Array{Int64}([]) for i = 1:m]
 for i in 1:n
  for c in A[i].pos
   col = col_list[c]
   push!(col, i)
  end
 end
 col_count = [length(col_list[i]) for i = 1:m]

 consider_cols = [i for i = m:-1:l+1] #singleton col candidates
 two_elem_cols = Array{Int64}([]) #2-elem col candidates
 while !isempty(consider_cols)
  #go over singletons
  consider_cols_c = Array{Int64}([])
  for i in consider_cols
   i>l && col_count[i] == 2 && push!(two_elem_cols, i)
   if col_count[i] == 1
    r = first(col_list[i])
    for idx in A[r].pos
     del_idx = searchsortedfirst(col_list[idx], r)
     deleteat!(col_list[idx], del_idx)
     col_count[idx]-=1
     idx>l && col_count[idx] == 1 && push!(consider_cols_c, idx)
     idx>l && col_count[idx] == 2 && push!(two_elem_cols, idx)
    end
    #delete_row!(A, r)
    A.nnz -=length(A[r])
    empty!(A[r].pos)
    empty!(A[r].values)
   end
  end
  consider_cols, consider_cols_c = consider_cols_c, Array{Int64}([])
  two_elem_cols_c = Array{Int64}([])
  for i in two_elem_cols
   if col_count[i] == 2
    fir, sec = col_list[i][1], col_list[i][2]
    if length(A[fir]) <= length(A[sec])  
     piv = fir; r = sec
    else
     piv = sec; r = fir
    end 
    i_piv = searchsortedfirst(A[piv].pos, i)
    i_r = searchsortedfirst(A[r].pos, i)
    v_piv = A[piv].values[i_piv]
    v_r = A[r].values[i_r]
    if R == ZZ || !isprime(modulus(R)) #TODO: more general over_field or not. check what can be a field
     g = gcd(v_piv, v_r)
     scale_row2!(A, r, -div(v_piv, g), col_list, col_count, consider_cols, two_elem_cols_c)#Null hier aus col_list nehmen  
     add_scaled_row!(A, piv, r,  div(v_r, g))
    elseif isprime(modulus(R))
     scale_row!(A, piv, inv(v_piv))
     add_scaled_row!(A, piv, r, -v_r)
    end
    for piv_idx in A[piv].pos
     piv_c = col_list[piv_idx]
     r_idx = findfirst(x->x>=r,piv_c)
     if iszero(A[r, piv_idx]) #when?
      deleteat!(piv_c, r_idx) #make sure that exists
      col_count[piv_idx]-=1
     elseif isnothing(r_idx)
      push!(piv_c, r)
     elseif piv_c[r_idx] != r
      insert!(piv_c, r_idx, r)
      col_count[piv_idx]+=1
     end 
     d = searchsortedfirst(piv_c, piv)
     deleteat!(piv_c, d)
     col_count[piv_idx]-=1
     piv_idx>l && col_count[piv_idx] == 1 && push!(consider_cols, piv_idx)
     piv_idx>l && col_count[piv_idx] == 2 && push!(two_elem_cols_c, piv_idx)
    end
    #delete_row!(A, piv)
    A.nnz-=length(A[piv])
    empty!(A[piv].pos)
    empty!(A[piv].values)
   end
  end
  two_elem_cols, two_elem_cols_c = two_elem_cols_c, Array{Int64}([])
 end
 for i in 1:length(col_count)
  col_count[i]==1 && @show(1, i, col_list[i], consider_cols)
  col_count[i]==2 && @show(2, i, col_list[i], two_elem_cols)
 end
 @assert !(1 in col_count[l+1:end]) && !(2 in col_count[l+1:end])
 return(A)
end

#TODO arrays verwalten mit neuen Spalten und zweites Array jeweils plus Reihenfolge 

###############################################################################
#
#   PREPROCESSING (FOR WIEDEMANN)
#
###############################################################################

function sp_prepro_1(A::SMat{T}, TA::SMat{T}, l) where T
  n,m = A.r, TA.r
  done = false
  while !done
    done = true
    for j = l+1:m
      if length(TA[j])==1 
        done = false
        i = TA[j].pos[1]           
        empty_col!(TA,A,i)
        A.nnz-=length(A[i])
        empty!(A[i].pos); empty!(A[i].values)
      end
    end
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))
  return A, TA
end

########## mods ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k, forbidden_cols) where T <: Union{ZZModRingElem, zzModRingElem, fpFieldElem, FpFieldElem} #prepro for cols with k>1
  @assert k > 1
  m = TA.r
  done = false
  while !done
    done = true
    for j = l+1:m
      if length(TA[j]) == k
        forbidden = false
        S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]))
        (p,u) = S[1]
        for idx in A[p].pos
          if idx in forbidden_cols
            forbidden = true
            break
          end
        end
        if !forbidden
          done = false
          for i in 2:k
            add_scaled_col!(TA, A, p, S[i][1], -divexact(S[i][2],u)) #add P to Q -> Q = Q - v/u *P
          end
          empty_col!(TA, A, p)
          for i in 2:k
            add_scaled_row!(A, p, S[i][1], -divexact(S[i][2],u))
          end
          A.nnz-=length(A[p]) 
          empty!(A[p].pos); empty!(A[p].values)
        end
      end
    end 
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))      
  return A, TA
end

########## Integers ##########
function sp_prepro_k(A::SMat{T}, TA::SMat{T}, l, k, forbidden_cols) where T <: Union{ZZRingElem, Integer}
  @assert k > 1
  m = TA.r
  done = false
  while !done
    done = true
    for j = m:-1:l+1
      if length(TA[j]) == k
        forbidden = false
        S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]))
        (p,u) = S[1]
        for idx in A[p].pos
          if idx in forbidden_cols
            forbidden = true
            break
          end
        end
        if !forbidden
          done = false
          for i in 2:k
            scale_col!(TA, A, S[i][1], u)
            add_scaled_col!(TA, A, p, S[i][1], -S[i][2]) #add P to Q -> Q = Q - v *P
          end
          empty_col!(TA, A, p)
          for i in 2:k
            scale_row!(A, S[i][1], u)
            add_scaled_row!(A, p, S[i][1], -S[i][2])
          end
          A.nnz-=length(A[p]) 
          empty!(A[p].pos); empty!(A[p].values)
        end
      end
    end 
  end
  A = delete_zero_rows!(A)
  TA = transpose(A)
  A = transpose(delete_zero_rows!(TA,l+1))      
  return A, TA
end 

########## preprocessing ##########
function sp_prepro(A::SMat{T}, TA::SMat{T}, l, iter=2, forbidden_cols=[]) where T
  A, TA = sp_prepro_1(A, TA, l)
  for k in 2:iter
    A, TA = sp_prepro_k(A, TA, l, k, forbidden_cols)
  end
  return A, TA
end

###############################################################################
#
#   STRUCTURED GAUSS
#
###############################################################################
function eliminate_dense_rows(A::SMat, density_row=0.2)
  n = A.r
  bound = density_row*n
  for i = 1:n
    l = length(A[i])
    if l > bound
      A.nnz-=l
      empty!(A[i].pos); empty!(A[i].values)
    end
  end
  delete_zero_rows!(A)
end



function struct_gauss_k(A::SMat{T}, TA::SMat{T}, l, k, density_col) where T <: Union{ZZModRingElem, zzModRingElem, fpFieldElem, FpFieldElem} #prepro for cols with k>1
 @assert k > 1
 m = TA.r
 bound = m*density_col
 done = false
 while !done
   done = true
   for j = l+1:m
     if length(TA[j]) == k
       S = sort([(TA[j].pos[i],TA[j].values[i]) for i=1:k], by=x->length(A[x[1]]))
       (p,u) = S[1]
       dense = false
       for idx in A[p].pos
         if length(TA[idx])+k > bound
           dense = true
           break
         end
       end
       if dense
         continue
       else
         done = false
         for i in 2:k
           add_scaled_col!(TA, A, p, S[i][1], -divexact(S[i][2],u)) #add P to Q -> Q = Q - v/u *P
         end
         empty_col!(TA, A, p)
         for i in 2:k
           add_scaled_row!(A, p, S[i][1], -divexact(S[i][2],u))
         end
         A.nnz-=length(A[p]) 
         empty!(A[p].pos); empty!(A[p].values)
       end
     end
   end 
 end
 A = delete_zero_rows!(A)
 TA = transpose(A)
 A = transpose(delete_zero_rows!(TA,l+1))      
 return A, TA
end

function struct_gauss(A::SMat{T}, TA::SMat{T}, l, iter=5, density_col = 0.1, density_row=0.1) where T
 A, TA = struct_gauss_1(A, TA, l)
 for k in 2:iter
   eliminate_dense_rows(A, density_row)
   TA = transpose(A)
   A, TA = struct_gauss_k(A, TA, l, k, density_col)
 end
 return A, TA
end

###structured gaussian elimination without deletion###
function gauss_elim(A::SMat, TA::SMat,l)
  right_place = []
  rest_cols = []
  for j = 1:nrows(TA)
    if length(TA[j])==1
      i = TA[j].pos[1]
      if i in right_place
        push!(rest_cols, j)
      else
        push!(right_place, j)
        swap_rows!(A, i, j)
        TA = transpose(A)
      end
      #swap_cols!(TA, i, j) #wichtig da sonst i falsch
    end
  end 
  return A, TA, right_place, rest_cols
end

function gauss_pivoting(A::SMat,TA::SMat, l, lower, upper)
  m = TA.r
  pivots = Dict()
  for j = l+1:m
    len = length(TA[j])
    if lower<=len<=upper
      Rows = sort([TA[j].pos[i] for i=1:len], by=x->length(A[x[1]]))
        p = Rows[1]
        if haskey(pivots, p)
          push!(pivots[p],(len,j))
        else 
          push!(pivots, p => [(len,j)])
        end
    end
  end
  return pivots
end

#=
function change_base_ring(R::Ring, A::SMat{T}) where T<: Integer
 z = sparse_matrix(R)
 z.c = A.c
 for r in A
   rz = change_base_ring(R, r)
   push!(z, rz)
 end
 return z
end

function change_base_ring(R::S, A::SRow{T}) where {T <: Integer, S <: Ring}
  z = sparse_row(R)
  for (i, v) in A
    nv = R(v)
    if iszero(nv)
      continue
    else
      push!(z.pos, i)
      push!(z.values, nv)
    end
  end
  return z
end

function change_base_ring(R::ZZRing, A::SRow{T}) where T
  z = sparse_row(R)
  for (i, v) in A
    nv = lift(v)
    if iszero(nv)
      continue
    else
      push!(z.pos, i)
      push!(z.values, nv)
    end
  end
  return z
end

function change_base_ring(R::ZZRing, A::SMat{T}) where T
  z = sparse_matrix(R)
  z.c = A.c
  for r in A
    rz = change_base_ring2(R, r)
    push!(z, rz)
  end
  return z
end
=#

function scale_row2!(A::SMat{T}, i::Int, c::T, col_list, col_count, consider_cols, two_elem_cols_c) where T
 for j=1:length(A[i].pos)
  A[i].values[j] *= c
  if iszero(A[i].values[j])
   A.nnz -= 1
   d = col_list[j]
   idx = searchsortedfirst(d, i)
   deleteat!(d, idx)
   deleteat!(A[i].pos, j)
   deleteat!(A[i].values, j)
   col_count[j]-=1
   col_count[j] == 1 && push!(consider_cols, j)
   col_count[j] == 2 && push!(two_elem_cols_c, j)
  end
 end
end 
