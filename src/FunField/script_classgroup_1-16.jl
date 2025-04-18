include("cg_examples.jl")

#fun = [F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16]
fun = [F12, F13, F14]
#killed at F6

io = open("test_12-14.txt", "a")
for j = 1:length(fun)
 @show j
 F = fun[j]
 #for k = 1:3
  counter, m, n, S = Hecke.class_group_sparse(F)
  write(io, "field = F$(j+6), counter = $counter, m = $m, n = $n \n")
  _str = ""

  for i = size(S)[2]:-1:1
   v = S[i,i]

   if isone(v)
    break
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
 #end
 write(io, "\n \n")
end

close(io)