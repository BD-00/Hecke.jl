(1)
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F1, a = function_field(x^3+(2t+1)x^2+(2t^3+t^2+t+1)x+t^2+2)

(2)
k = GF(3)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F2, a = function_field(x^3+(t^2+2)x^2+(2t^2+2)x+2)

(3)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F3, a = function_field(x^3+(t^2+2t+2)x^2+(t+2)x+2)

(4)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F4, a = function_field(x^3+(3t+4)x^2+2x+1)

(5)
k = GF(7)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F5, a = function_field(x^3+(2t+3)x^2+1)
A = pole_divisor(F(t))

(6)
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F6, a = function_field(x^4+2x^3+(2t^2+3t+4)x+1)

(7)
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F7, a = function_field(x^3+(8t^2+t)x^2+(6t^2+3t+3)x+8)

(8)
k = GF(11)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F8, a = function_field(x^3+(10t^2+7t+1)x^2+(2t^2+8t+5)x+7)

(9)
k = GF(17)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F9, a = function_field(x^3+2x^2+(6t^2+14t+6)x+10t^2+10t+1)

(10)
k = GF(9)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F10, a = function_field(x^4+2x^3+(2t+1)x^2+2x+1)

(11)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F11, a = function_field(x^4+(2t+3)x^3+x^2+(3t+2)x+1)

(12)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F12, a = function_field(x^4+2x^3+(3t+2)x^2+x+2)

(13)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F13, a = function_field(x^4+(2t+3)x^3+x^2+1)

(14)
k = GF(25)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F14, a = function_field(x^4+(2t+3)x^3+(t+1)x^2+(4t+3)x+1)

(15)
k = GF(49)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F15, a = function_field(x^4+(2t+3)x^3+(3t+2)x^2+(4t+5)x+1)

(16)
k = GF(5)
kt, t = rational_function_field(k, "t")
ktx, x = polynomial_ring(kt, "x")
F16, a = function_field(x^5+(2t+3)x^2+3x+1)

fun = [F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16]

io = open("Hess16.txt", "a")
for j = 1:length(fun)
 F = fun[j]
 for k = 1:3
  counter, m, n, S = Hecke.class_group_naive(F)
  write(io, "field = F$j, counter = $counter, m = $m, n = $n \n")
  _str = ""

  for i = 1:size(S)[2]
   v = S[i,i]

   if isone(v)
    continue
   elseif iszero(v)
    if isempty(_str) 
     _str*= "Z"
    else
     _str*=" x Z"
    end
   else
    if isempty(_str)
     _str*= "$v"
    else
     _str*= " x $v"
    end
   end

  end
  write(io, "class group: $_str \n")
 end
 write(io, "\n \n")
end

close(io)