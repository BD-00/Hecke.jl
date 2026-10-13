#Examples Hess S.82 ff.

(1) #g=3
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F1, a = function_field(x^3+(2t+1)x^2+(2t^3+t^2+t+1)x+t^2+2)

(2) #g=2
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F2, a = function_field(x^3+(t^2+2)x^2+(2t^2+2)x+2)

(3) #g=1
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F3, a = function_field(x^3+(t^2+2t+2)x^2+(t+2)x+2)

(4) #g=0
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F4, a = function_field(x^3+(3t+4)x^2+2x+1)

(5) #g=0
k = GF(7)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F5, a = function_field(x^3+(2t+3)x^2+1)

(6) #g=2
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F6, a = function_field(x^4+2x^3+(2t^2+3t+4)x+1)

(7) #g=2
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F7, a = function_field(x^3+(8t^2+t)x^2+(6t^2+3t+3)x+8)

(8) #g=1
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F8, a = function_field(x^3+(10t^2+7t+1)x^2+(2t^2+8t+5)x+7)

(9) #g=1
k = GF(17)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F9, a = function_field(x^3+2x^2+(6t^2+14t+6)x+10t^2+10t+1)

(10) #g=0
k = GF(9)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F10, a = function_field(x^4+2x^3+(2t+1)x^2+2x+1)

(11) #g=0
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F11, a = function_field(x^4+(2t+3)x^3+x^2+(3t+2)x+1)

(12) #g=0
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F12, a = function_field(x^4+2x^3+(3t+2)x^2+x+2)

(13) #g=0
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F13, a = function_field(x^4+(2t+3)x^3+x^2+1)

(14) #g=0
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F14, a = function_field(x^4+(2t+3)x^3+(t+1)x^2+(4t+3)x+1)

(15) #g=0
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F15, a = function_field(x^4+(2t+3)x^3+(3t+2)x^2+(4t+5)x+1)

(16) #g=0
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F16, a = function_field(x^5+(2t+3)x^2+3x+1)

(17) #g=10
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F17, a = function_field(x^5+t*x+t^6+t+1)

(18) #g=6
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F18, a = function_field(x^4+t^2x+t^5+t+1)

(19) #g=7
k = GF(19)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F19, a = function_field(x^4+x^3+t^2x+t^6+t+1)

(20) #g=6
k = GF(9)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F20, a = function_field(x^5+t*x^3+t^5+t^2+1)

#=
```magma
// (1) g = 3
k1 := GF(3);
kt1<t1> := RationalFunctionField(k1);
ktx1<x1> := PolynomialRing(kt1);
F1<a1> := FunctionField(x1^3 + (2*t1 + 1)*x1^2 + (2*t1^3 + t1^2 + t1 + 1)*x1 + t1^2 + 2);

// (2) g = 2
k2 := GF(3);
kt2<t2> := RationalFunctionField(k2);
ktx2<x2> := PolynomialRing(kt2);
F2<a2> := FunctionField(x2^3 + (t2^2 + 2)*x2^2 + (2*t2^2 + 2)*x2 + 2);

// (3) g = 1
k3 := GF(5);
kt3<t3> := RationalFunctionField(k3);
ktx3<x3> := PolynomialRing(kt3);
F3<a3> := FunctionField(x3^3 + (t3^2 + 2*t3 + 2)*x3^2 + (t3 + 2)*x3 + 2);

// (4) g = 0
k4 := GF(25);
kt4<t4> := RationalFunctionField(k4);
ktx4<x4> := PolynomialRing(kt4);
F4<a4> := FunctionField(x4^3 + (3*t4 + 4)*x4^2 + 2*x4 + 1);

// (5) g = 0
k5 := GF(7);
kt5<t5> := RationalFunctionField(k5);
ktx5<x5> := PolynomialRing(kt5);
F5<a5> := FunctionField(x5^3 + (2*t5 + 3)*x5^2 + 1);

// (6) g = 2
k6 := GF(49);
kt6<t6> := RationalFunctionField(k6);
ktx6<x6> := PolynomialRing(kt6);
F6<a6> := FunctionField(x6^4 + 2*x6^3 + (2*t6^2 + 3*t6 + 4)*x6 + 1);

// (7) g = 2
k7 := GF(11);
kt7<t7> := RationalFunctionField(k7);
ktx7<x7> := PolynomialRing(kt7);
F7<a7> := FunctionField(x7^3 + (8*t7^2 + t7)*x7^2 + (6*t7^2 + 3*t7 + 3)*x7 + 8);

// (8) g = 1
k8 := GF(11);
kt8<t8> := RationalFunctionField(k8);
ktx8<x8> := PolynomialRing(kt8);
F8<a8> := FunctionField(x8^3 + (10*t8^2 + 7*t8 + 1)*x8^2 + (2*t8^2 + 8*t8 + 5)*x8 + 7);

// (9) g = 1
k9 := GF(17);
kt9<t9> := RationalFunctionField(k9);
ktx9<x9> := PolynomialRing(kt9);
F9<a9> := FunctionField(x9^3 + 2*x9^2 + (6*t9^2 + 14*t9 + 6)*x9 + 10*t9^2 + 10*t9 + 1);

// (10) g = 0
k10 := GF(9);
kt10<t10> := RationalFunctionField(k10);
ktx10<x10> := PolynomialRing(kt10);
F10<a10> := FunctionField(x10^4 + 2*x10^3 + (2*t10 + 1)*x10^2 + 2*x10 + 1);

// (11) g = 0
k11 := GF(5);
kt11<t11> := RationalFunctionField(k11);
ktx11<x11> := PolynomialRing(kt11);
F11<a11> := FunctionField(x11^4 + (2*t11 + 3)*x11^3 + x11^2 + (3*t11 + 2)*x11 + 1);

// (12) g = 0
k12 := GF(25);
kt12<t12> := RationalFunctionField(k12);
ktx12<x12> := PolynomialRing(kt12);
F12<a12> := FunctionField(x12^4 + 2*x12^3 + (3*t12 + 2)*x12^2 + x12 + 2);

// (13) g = 0
k13 := GF(25);
kt13<t13> := RationalFunctionField(k13);
ktx13<x13> := PolynomialRing(kt13);
F13<a13> := FunctionField(x13^4 + (2*t13 + 3)*x13^3 + x13^2 + 1);

// (14) g = 0
k14 := GF(25);
kt14<t14> := RationalFunctionField(k14);
ktx14<x14> := PolynomialRing(kt14);
F14<a14> := FunctionField(x14^4 + (2*t14 + 3)*x14^3 + (t14 + 1)*x14^2 + (4*t14 + 3)*x14 + 1);

// (15) g = 0
k15 := GF(49);
kt15<t15> := RationalFunctionField(k15);
ktx15<x15> := PolynomialRing(kt15);
F15<a15> := FunctionField(x15^4 + (2*t15 + 3)*x15^3 + (3*t15 + 2)*x15^2 + (4*t15 + 5)*x15 + 1);

// (16) g = 0
k16 := GF(5);
kt16<t16> := RationalFunctionField(k16);
ktx16<x16> := PolynomialRing(kt16);
F16<a16> := FunctionField(x16^5 + (2*t16 + 3)*x16^2 + 3*x16 + 1);

// (17) g = 10
k17 := GF(3);
kt17<t17> := RationalFunctionField(k17);
ktx17<x17> := PolynomialRing(kt17);
F17<a17> := FunctionField(x17^5 + t17*x17 + t17^6 + t17 + 1);

// (18) g = 6
k18 := GF(11);
kt18<t18> := RationalFunctionField(k18);
ktx18<x18> := PolynomialRing(kt18);
F18<a18> := FunctionField(x18^4 + t18^2*x18 + t18^5 + t18 + 1);

// (19) g = 7
k19 := GF(19);
kt19<t19> := RationalFunctionField(k19);
ktx19<x19> := PolynomialRing(kt19);
F19<a19> := FunctionField(x19^4 + x19^3 + t19^2*x19 + t19^6 + t19 + 1);

// (20) g = 6
k20 := GF(9);
kt20<t20> := RationalFunctionField(k20);
ktx20<x20> := PolynomialRing(kt20);
F20<a20> := FunctionField(x20^5 + t20*x20^3 + t20^5 + t20^2 + 1);
```
=#
