function read_dd_matrix(filename)
 f = open(filename)
 firstline = readline(f)
 dimensions = split(firstline, " ")
 rows = parse(Int64, dimensions[1])
 columns = parse(Int64, dimensions[2])
 A = sparse_matrix(QQ, rows, columns)
 for line in eachline(f)
     parts = map(z -> parse(Int64, z), split(line, " "))
     row = parts[1]
     column = parts[2]
     entry = parts[3]
     if row == 0 && column == 0 && entry == 0
      break
     end
     push!(A[row].pos, column)
     push!(A[row].values, entry)
     A.nnz+=1
 end
 close(f)
 return A
end

A = read_dd_matrix("dd_8.txt")
B = deepcopy(A)
l, K = Hecke.structured_gauss_field(A)

C = read_dd_matrix("structured_gauss_bug_matrix.txt")
D = deepcopy(C)
l2, K2 = Hecke.structured_gauss_field(C)
