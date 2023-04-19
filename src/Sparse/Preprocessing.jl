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
function sp_prepro(A::SMat{T}, TA::SMat{T}, l, iter=5, forbidden_cols=[]) where T
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