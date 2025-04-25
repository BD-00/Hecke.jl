function profile_dense(F, n)
 for i = 1:n
  c, m, n, M = Hecke.class_group_dense(F)
 end
end

function profile_sparse(F, n)
 for i = 1:n
  c, m, n, M = Hecke.class_group_naive(F)
 end
end