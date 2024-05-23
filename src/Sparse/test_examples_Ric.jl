#using TimerOutputs
#const to = TimerOutput()
using Hecke
include("module-StructuredGauss.jl")
using .StructuredGauss
include("StructuredGauss.jl")

function read_dd_matrix(filename)
 f = open(filename)
 firstline = readline(f)
 dimensions = split(firstline, " ")
 rows = parse(Int64, dimensions[1])
 columns = parse(Int64, dimensions[2])
 A = sparse_matrix(ZZ, rows, columns)#QQ before
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

function dd_preprocessing(A)
 for i = 1:nrows(A)
  scale_row!(A, i, 1//gcd(A[i].values))
 end
end

B = read_dd_matrix("dd_10.txt")
#@timeit to "dd_8" kern_B, _, _ = gen_StructGauss(B)
#@show(@time kern_B, _, _ = gen_StructGauss(B))
#show(to)
A = read_dd_matrix("dd_11.txt")
#@timeit to "dd_11" kern_A, _, _ = gen_StructGauss(A)
#@show(@time kern_A, _, _ = gen_StructGauss(A))
#=
d, k = kernel(matrix(A))
d_norm = inv(k[1])*k

kern_osc = [d_norm[i] for i in 1:length(d_norm)]
=#

#kern_norm = inv(kern_A[1])*kern_A
#kern = [kern_norm[i] for i in 1:length(kern_norm)]
#diff = kern_osc - kern

#length(filter(iszero, diff))

#=
open("kernel_dd_11.txt", "w") do file
 for i in kern_A
  write(file, "$i,\n")
 end
end
=#
C = read_dd_matrix("dd_10.txt")

p = next_prime(2^59)
R = ResidueRing(ZZ, p)
B_p = change_base_ring(R, B)
A_p = change_base_ring(R, A)
C_p = change_base_ring(R, C)

SGB = part_echolonize_field!(B_p)
SGC = part_echolonize_field!(C_p)