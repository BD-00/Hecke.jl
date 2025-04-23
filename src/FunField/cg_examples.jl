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
F17, a = function_field(x^5+tx+t^6+t+1)

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
F18, a = function_field(x^5+tx^3+t^5+t^2+1)