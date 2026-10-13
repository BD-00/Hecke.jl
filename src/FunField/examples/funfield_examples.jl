#Examples Hess S.82 ff.
#analogously for magma under murrumesh:Magma/funfield_examples.m

# (1) g = 3
k1 = GF(3)
kt1, t1 = rational_function_field(k1, "t")
ktx1, x1 = polynomial_ring(kt1, "x")
F1, a1 = function_field(x1^3 + (2*t1 + 1)*x1^2 + (2*t1^3 + t1^2 + t1 + 1)*x1 + t1^2 + 2)

# (2) g = 2
k2 = GF(3)
kt2, t2 = rational_function_field(k2, "t")
ktx2, x2 = polynomial_ring(kt2, "x")
F2, a2 = function_field(x2^3 + (t2^2 + 2)*x2^2 + (2*t2^2 + 2)*x2 + 2)

# (3) g = 1
k3 = GF(5)
kt3, t3 = rational_function_field(k3, "t")
ktx3, x3 = polynomial_ring(kt3, "x")
F3, a3 = function_field(x3^3 + (t3^2 + 2*t3 + 2)*x3^2 + (t3 + 2)*x3 + 2)

# (4) g = 0
k4 = GF(25)
kt4, t4 = rational_function_field(k4, "t")
ktx4, x4 = polynomial_ring(kt4, "x")
F4, a4 = function_field(x4^3 + (3*t4 + 4)*x4^2 + 2*x4 + 1)

# (5) g = 0
k5 = GF(7)
kt5, t5 = rational_function_field(k5, "t")
ktx5, x5 = polynomial_ring(kt5, "x")
F5, a5 = function_field(x5^3 + (2*t5 + 3)*x5^2 + 1)

# (6) g = 2
k6 = GF(49)
kt6, t6 = rational_function_field(k6, "t")
ktx6, x6 = polynomial_ring(kt6, "x")
F6, a6 = function_field(x6^4 + 2*x6^3 + (2*t6^2 + 3*t6 + 4)*x6 + 1)

# (7) g = 2
k7 = GF(11)
kt7, t7 = rational_function_field(k7, "t")
ktx7, x7 = polynomial_ring(kt7, "x")
F7, a7 = function_field(x7^3 + (8*t7^2 + t7)*x7^2 + (6*t7^2 + 3*t7 + 3)*x7 + 8)

# (8) g = 1
k8 = GF(11)
kt8, t8 = rational_function_field(k8, "t")
ktx8, x8 = polynomial_ring(kt8, "x")
F8, a8 = function_field(x8^3 + (10*t8^2 + 7*t8 + 1)*x8^2 + (2*t8^2 + 8*t8 + 5)*x8 + 7)

# (9) g = 1
k9 = GF(17)
kt9, t9 = rational_function_field(k9, "t")
ktx9, x9 = polynomial_ring(kt9, "x")
F9, a9 = function_field(x9^3 + 2*x9^2 + (6*t9^2 + 14*t9 + 6)*x9 + 10*t9^2 + 10*t9 + 1)

# (10) g = 0
k10 = GF(9)
kt10, t10 = rational_function_field(k10, "t")
ktx10, x10 = polynomial_ring(kt10, "x")
F10, a10 = function_field(x10^4 + 2*x10^3 + (2*t10 + 1)*x10^2 + 2*x10 + 1)

# (11) g = 0
k11 = GF(5)
kt11, t11 = rational_function_field(k11, "t")
ktx11, x11 = polynomial_ring(kt11, "x")
F11, a11 = function_field(x11^4 + (2*t11 + 3)*x11^3 + x11^2 + (3*t11 + 2)*x11 + 1)

# (12) g = 0
k12 = GF(25)
kt12, t12 = rational_function_field(k12, "t")
ktx12, x12 = polynomial_ring(kt12, "x")
F12, a12 = function_field(x12^4 + 2*x12^3 + (3*t12 + 2)*x12^2 + x12 + 2)

# (13) g = 0
k13 = GF(25)
kt13, t13 = rational_function_field(k13, "t")
ktx13, x13 = polynomial_ring(kt13, "x")
F13, a13 = function_field(x13^4 + (2*t13 + 3)*x13^3 + x13^2 + 1)

# (14) g = 0
k14 = GF(25)
kt14, t14 = rational_function_field(k14, "t")
ktx14, x14 = polynomial_ring(kt14, "x")
F14, a14 = function_field(x14^4 + (2*t14 + 3)*x14^3 + (t14 + 1)*x14^2 + (4*t14 + 3)*x14 + 1)

# (15) g = 0
k15 = GF(49)
kt15, t15 = rational_function_field(k15, "t")
ktx15, x15 = polynomial_ring(kt15, "x")
F15, a15 = function_field(x15^4 + (2*t15 + 3)*x15^3 + (3*t15 + 2)*x15^2 + (4*t15 + 5)*x15 + 1)

# (16) g = 0
k16 = GF(5)
kt16, t16 = rational_function_field(k16, "t")
ktx16, x16 = polynomial_ring(kt16, "x")
F16, a16 = function_field(x16^5 + (2*t16 + 3)*x16^2 + 3*x16 + 1)

# (17) g = 10
k17 = GF(3)
kt17, t17 = rational_function_field(k17, "t")
ktx17, x17 = polynomial_ring(kt17, "x")
F17, a17 = function_field(x17^5 + t17*x17 + t17^6 + t17 + 1)

# (18) g = 6
k18 = GF(11)
kt18, t18 = rational_function_field(k18, "t")
ktx18, x18 = polynomial_ring(kt18, "x")
F18, a18 = function_field(x18^4 + t18^2*x18 + t18^5 + t18 + 1)

# (19) g = 7
k19 = GF(19)
kt19, t19 = rational_function_field(k19, "t")
ktx19, x19 = polynomial_ring(kt19, "x")
F19, a19 = function_field(x19^4 + x19^3 + t19^2*x19 + t19^6 + t19 + 1)

# (20) g = 6
k20 = GF(9)
kt20, t20 = rational_function_field(k20, "t")
ktx20, x20 = polynomial_ring(kt20, "x")
F20, a20 = function_field(x20^5 + t20*x20^3 + t20^5 + t20^2 + 1)


#p class group
k = GF(ZZ(5)^12)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^4-t^2x+3*t^18+2)

#examples from Claus for p-torsion part
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
f1 = x^2 + t^9 + t^7 + 2*t^6 + 2*t^4 + 2*t^2 + t
f2 = x^2 + t^9 + 2*t^8 + t^7 + t^6 + t^5 + t^4 + 2*t^3 + 2*t^2 + t
F1, a1 = function_field(f1)
F2, a2 = function_field(f2)

#function field with only infinite rational places:
k = GF(2)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field((x^2+x)*(t^4+t+1)-t^3-t-1)

#function field without rational places:
k = GF(2)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F, a = function_field(x^2+(t^3+t^2+1)*x+(t^6+t^5+1))

F, a = function_field(t^6 + t^5*x + t^5 + t^4 + t^3*x^3 + t^3*x^2 + t^3 + t^2*x^2 + t*x^5 + t*x^4 + t + x^6 + x^4 + x^3 + x^2)
t^6 + t^5*x + t^5 + t^4 + t^3*x^3 + t^3*x^2 + t^3 + t^2*x^2 + t*x^5 + t*x^4 + t + x^6 + x^4 + x^3 + x^2

#no places of degree <4:
k = GF(2)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
d = t^4 + t + 1
f = d^2 * x^5 + d^2 * x^3 + d^2 * (t^3 + t^2 + t) * x^2 + d * (t^7 + t^5 + t^4 + t^3 + t) * x + (t^13 + t^12 + t^8 + t^6 + t^2 + t + 1)
F, a = function_field(f)
#degree_list looks weird here

#examples from Jeroen to compute non-trivial p-torsion groups
k = GF(11)
kx, x = rational_function_field(k, "x")
kxy, y = polynomial_ring(kx, "y")
f1 = 7*x^8+7*x^7+5*x^6+9*x^5+x^4+9*x^3+7*x^2+10*x+10-y^2
F1, a = function_field(f1)
f2 = 8*x^8+4*x^7+9*x^6+8*x^5+10*x^4+7*x^3+6*x^2+2*x+7-y^2
F2, a = function_field(f2)
#=
F = F2:

julia> k
Prime field of characteristic 3

julia> V = vector_space(k, 4)
Vector space of dimension 4 over k

julia> RRCtx.RR_basis
4-element Vector{AbstractAlgebra.Generic.AbsSimpleFunctionFieldElem}:
 _a//(t^9 + 2*t^8 + t^7 + t^6 + t^5 + t^4 + 2*t^3 + 2*t^2 + t)
 _a//(t^8 + 2*t^7 + t^6 + t^5 + t^4 + t^3 + 2*t^2 + 2*t + 1)
 (t*_a)//(t^8 + 2*t^7 + t^6 + t^5 + t^4 + t^3 + 2*t^2 + 2*t + 1)
 (t^2*_a)//(t^8 + 2*t^7 + t^6 + t^5 + t^4 + t^3 + 2*t^2 + 2*t + 1)

julia> k
Prime field of characteristic 3

julia> V
Vector space of dimension 4 over k

julia> v = collect(V);

julia> k
Prime field of characteristic 3

julia> V = vector_space(k, 4)
Vector space of dimension 4 over k

W = [(v[i].v*RRCtx.gens)[1] for i in 1:length(v)]
=#