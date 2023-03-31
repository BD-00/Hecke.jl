import Hecke.sparse_row

#move to ZZRow.jl
function sparse_row(R::ZZRing, pos::Vector{Int64}, val::Vector{<:Integer}; sort::Bool = true)
 return sparse_row(R, pos, map(ZZRingElem, val), sort = sort)
end

###############################################################################
#
#   SIEVE
#
###############################################################################

function primitive_elem(F::FinField,first::Bool) 
  p = length(F)
  Fact = prime_divisors(ZZRingElem(p-1))
  while true # alpha exists
    for y in F
      if !first y = rand(F) end
      if isprime(lift(y))
        if !(any(i->isone(y^divexact(ZZRingElem(p-1),i)), Fact))
          return y
        end
      end
    end
  end
end

@doc raw"""
    sieve_params(p,eps::Float64,ratio::Float64) -> Tuple{Int64, Int64, Float64, Tuple{Int64, Int64}}

Returns parameters for sieve.
"""
function sieve_params(p,eps::Float64,ratio::Float64)
  # assymptotic bounds by Coppersmith, Odlyzko, and Schroeppel L[p,1/2,1/2]# L[n,\alpha ,c]=e^{(c+o(1))(\ln n)^{\alpha }(\ln \ln n)^{1-\alpha }}}   for c=1
  qlimit = exp((0.5* sqrt(Base.log(p)*Base.log(Base.log(p)))))
  qlimit *= Base.log(qlimit) # since aproximately    #primes
  climit = exp((0.5+eps)*sqrt(Base.log(p)*Base.log(Base.log(p))))

  qlimit = Int64(ceil(0.5*max(qlimit,30)))
  climit = Int64(ceil(max(climit,35)))
  inc = (Int64(100),Int64(100))
  return qlimit,climit,ratio,inc
end

<<<<<<< HEAD
@doc raw"""
    sieve(F::Nemo.FpField,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nothing

Computes coefficient matrix of factorbase logarithms and saves corresponding attributes on $F$.
"""
<<<<<<< HEAD
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.FpField} #F with primitive element as attribute, p at most 35 decimals
 p = characteristic(F)
 set_attribute!(F, :p=>p)
 a = get_attribute(F, :a)
 H_fmpz = floor(iroot(p,2))+1
 H1 = H_fmpz +1
 H = Int(H_fmpz)
 J = Int(H_fmpz^2 - p)
 qlimit, climit, ratio, inc = SP
 (lift(a) <= qlimit&&isprime(lift(a))) || (a = primitive_elem(F, true)) 
 set_attribute!(F, :primitive_elem=>a)

 # factorbase up to qlimit
 fb_primes = Hecke.primes_up_to(qlimit)
 indx = searchsortedfirst(fb_primes, lift(a))
 FB = vcat([ZZRingElem(lift(a))],deleteat!(fb_primes,indx))::Vector{ZZRingElem} # swap a[1] = a[2] , a[2] = [1] array
 # use shift! / unshift! here...
 log2 = Base.log(2.0);
 logqs = Float64[Base.log(Int(q))/log2 for q in FB] #real logarithms for sieve 
 set_attribute!(F, :FBs=>FactorBase(FB))
 FBs = get_attribute(F, :FBs)
 l = length(FB)
 set_attribute!(F, :fb_length=>l)
 Indx = Dict(zip(FB,[i for i=1:l]))::Dict{ZZRingElem, Int} #Index in a dictionary
 A = sparse_matrix(ZZ) #zz
 len = []
 rel = ZZRingElem(1)
 #IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
 ##########################################################################################################################################
 # Sieve for ci
 for c1 = 1:climit
   nrows(A)/length(FB) < ratio || break
   Sieve = zeros(climit)
   Hc1 = H + c1;                # denominator of relation
   #num = -(J + c1*H)            # numerator
   for i=1:length(fb_primes)
     q = fb_primes[i]
     qpow = Int(q)
     nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
     logq = logqs[i]
     while qpow < qlimit      # qlimit-smooth
       den_int = Hc1%qpow
       den_int != 0 || break
       num_int = ((-J)%qpow - (c1 %qpow)*(H%qpow))%qpow
       c2 = num_int * invmod(den_int, qpow)  % qpow ###
       (c2 != 0) || (c2 = qpow)
       nextqpow = qpow*q    #increase q_power
       while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
         c2+=qpow
       end
       while c2 <= length(Sieve)
           Sieve[c2] += logq
           if nextqpow > qlimit
               prod1 = J + c1*c2
               prod2 = c1+c2
               nextp = nextqpow
               while (prod1%nextp + (prod2%nextp)*(H%nextp))%nextp == 0
                   Sieve[c2] += logq
                   nextp = nextp*q
               end
           end
           c2 += qpow
       end
       qpow = nextqpow
     end
   end

   #include relations / check sieve for full factorizations.
   mul!(rel, Hc1, H1)

   n = ZZRingElem(1)
   for c2 in 1:length(Sieve)
     if rel > p
       sub!(n, rel, p)
       if n > p
         n = rel %p
       end
     else
       n = p
     end
     nbn = nbits(n)-1
     if abs(Sieve[c2] - nbn) < 1 
       #generate Factorbase based on FBs with new c_i�s
       if issmooth(FBs,n)
         dict_factors = Hecke.factor(FBs,ZZRingElem(n))
         #Include each H + c_i in extended factor basis.
         r = length(Indx)+1
         if !((Hc1) in keys(Indx))
           push!(FB,Hc1)
           push!(Indx, Hc1 => r)
         end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
         r = length(Indx)+1
         Hc2 = H + c2
         if !((Hc2) in keys(Indx))
           push!(FB,Hc2)
           push!(Indx,(Hc2) => r)
         end#(FB = vcat(FB,[H + c2]))
         #Include relation (H + c1)*(H + c2) = fact.
         #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
         J1 = Vector{Int64}([])
         V = Vector{Int64}([])
         for (prime,power) in dict_factors
           if !(power == 0)
             push!(J1,Indx[prime])
             push!(V,Int(power))
           end
         end
         if c1 == c2
           push!(J1,Indx[Hc1])
           push!(V,-2)
         else
           push!(J1,Indx[Hc1])
           push!(J1,Indx[Hc2])
           push!(V,-1)
           push!(V,-1)
         end
         push!(A,sparse_row(ZZ, J1, V)) #zz
         push!(len, length(J1))
       end
     end
     add!(rel, rel, Hc1)
   end
 end
 #increase Sieve 
 if nrows(A)/length(FB) < ratio
   qlimit += inc[1]
   climit += inc[2]
   return sieve(F,(qlimit, climit, ratio, inc))
 end
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :len=>len)
end

@doc raw"""
    sieve(F::Nemo.fpField,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nothing

Computes coefficient matrix of factorbase logarithms and saves corresponding attributes on $F$.
"""
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.fpField} #F with primitive element as attribute
 p = Int(length(F))
 set_attribute!(F, :p=>p)
 a = get_attribute(F, :a)
 H = Int(floor(sqrt(p))+1)
 H1 = H+1
 J = H^2 - p
 qlimit, climit, ratio, inc = SP
 @hassert :DiscLog 1 (H+climit)^2>0
 (lift(a) <= qlimit&&isprime(lift(a))) || (a = primitive_elem(F, true)) 
 set_attribute!(F, :primitive_elem=>a)

 # factorbase up to qlimit
 fb_primes = Hecke.primes_up_to(qlimit)
 indx = searchsortedfirst(fb_primes, lift(a))
 FB = vcat([ZZRingElem(lift(a))],deleteat!(fb_primes,indx))::Vector{ZZRingElem} # swap a[1] = a[2] , a[2] = [1] array
 # use shift! / unshift! here...
 log2 = Base.log(2.0);
 logqs = Float64[Base.log(Int(q))/log2 for q in FB] #real logarithms for sieve 
 set_attribute!(F, :FBs=>FactorBase(FB))
 FBs = get_attribute(F, :FBs)
 l = length(FB)
 set_attribute!(F, :fb_length=>l)
 Indx = Dict(zip(FB,[i for i=1:l]))::Dict{ZZRingElem, Int} #Index in a dictionary
 A = sparse_matrix(ZZ) #zz
 len = []
 #IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
 ##########################################################################################################################################
 # Sieve for ci
 for c1 = 1:climit
   nrows(A)/length(FB) < ratio || break
   Sieve = zeros(climit)
   Hc1 = H + c1;                # denominator of relation
   #num = -(J + c1*H)            # numerator
   for i=1:length(fb_primes)
     q = fb_primes[i]
     qpow = Int(q)
     nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
     logq = logqs[i]
     while qpow < qlimit      # qlimit-smooth
       den_int = Hc1%qpow
       den_int != 0 || break
       num_int = ((-J)%qpow - (c1 %qpow)*(H%qpow))%qpow
       c2 = num_int * invmod(den_int, qpow)  % qpow ###
       (c2 != 0) || (c2 = qpow)
       nextqpow = qpow*q    #increase q_power
       while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
         c2+=qpow
       end
       while c2 <= length(Sieve)
           Sieve[c2] += logq
           if nextqpow > qlimit
               prod = (J + (c1 + c2)*H + c1*c2)  #< p for p with > 5 digits
               nextp = nextqpow
               while rem(prod,nextp) == 0
                   Sieve[c2] += logq
                   nextp = nextp*q
               end
           end
           c2 += qpow
       end
       qpow = nextqpow
     end
   end

   #include relations / check sieve for full factorizations.
   rel = Hc1*H1

   for c2 in 1:length(Sieve)
     n = rel%p
     nbn = nbits(n)-1
     if abs(Sieve[c2] - nbn) < 1 
       #generate Factorbase based on FBs with new c_i�s
       if issmooth(FBs,ZZRingElem(n))
         dict_factors = Hecke.factor(FBs,ZZRingElem(n))
         #Include each H + c_i in extended factor basis.
         r = length(Indx)+1
         if !((Hc1) in keys(Indx))
           push!(FB,Hc1)
           push!(Indx, Hc1 => r)
         end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
         r = length(Indx)+1
         Hc2 = H + c2
         if !((Hc2) in keys(Indx))
           push!(FB,Hc2)
           push!(Indx,(Hc2) => r)
         end#(FB = vcat(FB,[H + c2]))
         #Include relation (H + c1)*(H + c2) = fact.
         #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
         J1 = Vector{Int64}([])
         V = Vector{Int64}([])
         for (prime,power) in dict_factors
           if !(power == 0)
             push!(J1,Indx[prime])
             push!(V,Int(power))
           end
         end
         if c1 == c2
           push!(J1,Indx[Hc1])
           push!(V,-2)
         else
           push!(J1,Indx[Hc1])
           push!(J1,Indx[Hc2])
           push!(V,-1)
           push!(V,-1)
         end
         push!(A,sparse_row(ZZ, J1, V)) #zz
         push!(len, length(J1))
       end
     end
     rel+=Hc1
   end
 end
 #increase Sieve 
 if nrows(A)/length(FB) < ratio
   qlimit += inc[1]
   climit += inc[2]
   return sieve(F,(qlimit, climit, ratio, inc))
 end
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :len=>len)
=======
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField} #F with primitive element as attribute
=======
@doc Markdown.doc"""
    sieve(F::Nemo.GaloisFmpzField,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nothing

Computes coefficient matrix of factorbase logarithms and saves corresponding attributes on $F$.
"""
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.GaloisFmpzField} #F with primitive element as attribute, p at most 35 decimals
>>>>>>> 37ff6a677 (Sieve: values of size sqrt(p) have type Int now + extra sieve for Nemo.GaloisField)
 p = characteristic(F)
 set_attribute!(F, :p=>p)
 a = get_attribute(F, :a)
 H_fmpz = floor(root(p,2))+1
 H1 = H_fmpz +1
 H = Int(H_fmpz)
 J = Int(H_fmpz^2 - p)
 qlimit, climit, ratio, inc = SP
 (lift(a) <= qlimit&&isprime(lift(a))) || (a = primitive_elem(F, true)) 
 set_attribute!(F, :primitive_elem=>a)

 # factorbase up to qlimit
 fb_primes = Hecke.primes_up_to(qlimit)
 indx = searchsortedfirst(fb_primes, lift(a))
 FB = vcat([fmpz(lift(a))],deleteat!(fb_primes,indx))::Vector{fmpz} # swap a[1] = a[2] , a[2] = [1] array
 # use shift! / unshift! here...
 log2 = Base.log(2.0);
 logqs = Float64[Base.log(Int(q))/log2 for q in FB] #real logarithms for sieve 
 set_attribute!(F, :FBs=>FactorBase(FB))
 FBs = get_attribute(F, :FBs)
 l = length(FB)
 set_attribute!(F, :fb_length=>l)
 Indx = Dict(zip(FB,[i for i=1:l]))::Dict{fmpz, Int} #Index in a dictionary
 A = sparse_matrix(zz)
 len = []
 rel = fmpz(1)
 #IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
 ##########################################################################################################################################
 # Sieve for ci
 for c1 = 1:climit
   nrows(A)/length(FB) < ratio || break
   Sieve = zeros(climit)
   Hc1 = H + c1;                # denominator of relation
   #num = -(J + c1*H)            # numerator
   for i=1:length(fb_primes)
     q = fb_primes[i]
     qpow = Int(q)
     nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
     logq = logqs[i]
     while qpow < qlimit      # qlimit-smooth
       den_int = Hc1%qpow
       den_int != 0 || break
       num_int = ((-J)%qpow - (c1 %qpow)*(H%qpow))%qpow
       c2 = num_int * invmod(den_int, qpow)  % qpow ###
       (c2 != 0) || (c2 = qpow)
       nextqpow = qpow*q    #increase q_power
       while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
         c2+=qpow
       end
       while c2 <= length(Sieve)
           Sieve[c2] += logq
           if nextqpow > qlimit
               prod1 = J + c1*c2
               prod2 = c1+c2
               nextp = nextqpow
               while (prod1%nextp + (prod2%nextp)*(H%nextp))%nextp == 0
                   Sieve[c2] += logq
                   nextp = nextp*q
               end
           end
           c2 += qpow
       end
       qpow = nextqpow
     end
   end

<<<<<<< HEAD
    #include relations / check sieve for full factorizations.
    rel = den * (H + 1)
    relinc = H + c1       # add to relation to get next relation
    idx = 0
    for c2 in 1:length(Sieve)
      n = rel % p
      FBs = get_attribute(F, :FBs)
      if abs(Sieve[c2] - (nbits(n)-1)) < 1 
        #generate Factorbase based on FBs with new c_i´s
        if issmooth(FBs,fmpz(n))
          dict_factors = Hecke.factor(FBs,fmpz(n))
          #Include each H + c_i in extended factor basis.
          r = length(Indx)+1
          if !((H + c1) in keys(Indx))
            push!(FB,H + c1)
            push!(Indx,(H+c1) => r)
          end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
          r = length(Indx)+1
          if !((H + c2) in keys(Indx))
            push!(FB,H + c2)
            push!(Indx,(H+c2) => r)
          end#(FB = vcat(FB,[H + c2]))
          #Include relation (H + c1)*(H + c2) = fact.
          #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
          J1 = Vector{Int64}([])
          V = Vector{Int64}([])
          for (prime,power) in dict_factors
            if !(power == 0)
              push!(J1,Indx[prime])
              push!(V,Int(power))
            end
          end
          if c1 == c2
            push!(J1,Indx[H+c1])
            push!(V,-2)
          else
            push!(J1,Indx[H+c1])
            push!(J1,Indx[H+c2])
            push!(V,-1)
            push!(V,-1)
          end
          push!(A,sparse_row(ZZ, J1, V))
        end
      end
      rel += relinc
    end
  end
  sieve_counter = 1
  #increase Sieve 
  if nrows(A)/length(FB) < ratio
    sieve_counter +=1
    qlimit += inc[1]
    climit += inc[2]
    return sieve(F,(qlimit, climit, ratio, inc))
  end
<<<<<<< HEAD
  @vprint :DiscLog "sieve ran $sieve_counter times"
  return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :factorbase=>FBs, :fb_length=>l)
>>>>>>> 2b67bdc03 (new disc_log with new tests)
=======
  @vprint :DiscLog "sieve ran $sieve_counter times" #wrong
  return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :fb_length=>l)
>>>>>>> 5d158f27b (small fixes)
=======
   #include relations / check sieve for full factorizations.
   mul!(rel, Hc1, H1)

   n = fmpz(1)
   for c2 in 1:length(Sieve)
     if rel > p
       sub!(n, rel, p)
       if n > p
         n = rel %p
       end
     else
       n = p
     end
     nbn = nbits(n)-1
     if abs(Sieve[c2] - nbn) < 1 
       #generate Factorbase based on FBs with new c_i�s
       if issmooth(FBs,n)
         dict_factors = Hecke.factor(FBs,fmpz(n))
         #Include each H + c_i in extended factor basis.
         r = length(Indx)+1
         if !((Hc1) in keys(Indx))
           push!(FB,Hc1)
           push!(Indx, Hc1 => r)
         end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
         r = length(Indx)+1
         Hc2 = H + c2
         if !((Hc2) in keys(Indx))
           push!(FB,Hc2)
           push!(Indx,(Hc2) => r)
         end#(FB = vcat(FB,[H + c2]))
         #Include relation (H + c1)*(H + c2) = fact.
         #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
         J1 = Vector{Int64}([])
         V = Vector{Int64}([])
         for (prime,power) in dict_factors
           if !(power == 0)
             push!(J1,Indx[prime])
             push!(V,Int(power))
           end
         end
         if c1 == c2
           push!(J1,Indx[Hc1])
           push!(V,-2)
         else
           push!(J1,Indx[Hc1])
           push!(J1,Indx[Hc2])
           push!(V,-1)
           push!(V,-1)
         end
         push!(A,sparse_row(zz, J1, V))
         push!(len, length(J1))
       end
     end
     add!(rel, rel, Hc1)
   end
 end
 #increase Sieve 
 if nrows(A)/length(FB) < ratio
   qlimit += inc[1]
   climit += inc[2]
   return sieve(F,(qlimit, climit, ratio, inc))
 end
<<<<<<< HEAD
<<<<<<< HEAD
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :fb_length=>l)
>>>>>>> 1e3d19dbc (tests updated, sieve improved)
=======
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB)
=======
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :len=>len)
>>>>>>> 6f2458d06 (before script)
end

@doc Markdown.doc"""
    sieve(F::Nemo.GaloisField,SP = sieve_params(characteristic(F),0.02,1.1)) -> Nothing

Computes coefficient matrix of factorbase logarithms and saves corresponding attributes on $F$.
"""
function sieve(F::T,SP = sieve_params(characteristic(F),0.02,1.01)) where T<:Union{Nemo.GaloisField} #F with primitive element as attribute
 p = Int(length(F))
 set_attribute!(F, :p=>p)
 a = get_attribute(F, :a)
 H = Int(floor(sqrt(p))+1)
 H1 = H+1
 J = H^2 - p
 qlimit, climit, ratio, inc = SP
 @hassert :DiscLog 1 (H+climit)^2>0
 (lift(a) <= qlimit&&isprime(lift(a))) || (a = primitive_elem(F, true)) 
 set_attribute!(F, :primitive_elem=>a)

 # factorbase up to qlimit
 fb_primes = Hecke.primes_up_to(qlimit)
 indx = searchsortedfirst(fb_primes, lift(a))
 FB = vcat([fmpz(lift(a))],deleteat!(fb_primes,indx))::Vector{fmpz} # swap a[1] = a[2] , a[2] = [1] array
 # use shift! / unshift! here...
 log2 = Base.log(2.0);
 logqs = Float64[Base.log(Int(q))/log2 for q in FB] #real logarithms for sieve 
 set_attribute!(F, :FBs=>FactorBase(FB))
 FBs = get_attribute(F, :FBs)
 l = length(FB)
 set_attribute!(F, :fb_length=>l)
 Indx = Dict(zip(FB,[i for i=1:l]))::Dict{fmpz, Int} #Index in a dictionary
 A = sparse_matrix(zz)
 len = []
 #IDEA: dont add logs. add INT counter, then add cnt * log in the end. ??
 ##########################################################################################################################################
 # Sieve for ci
 for c1 = 1:climit
   nrows(A)/length(FB) < ratio || break
   Sieve = zeros(climit)
   Hc1 = H + c1;                # denominator of relation
   #num = -(J + c1*H)            # numerator
   for i=1:length(fb_primes)
     q = fb_primes[i]
     qpow = Int(q)
     nextqpow = qpow   #WARNING inserted, because of some error with nextqpow
     logq = logqs[i]
     while qpow < qlimit      # qlimit-smooth
       den_int = Hc1%qpow
       den_int != 0 || break
       num_int = ((-J)%qpow - (c1 %qpow)*(H%qpow))%qpow
       c2 = num_int * invmod(den_int, qpow)  % qpow ###
       (c2 != 0) || (c2 = qpow)
       nextqpow = qpow*q    #increase q_power
       while c2 < c1   #c2>=c1 to remove redundant relations of (c1,c2) tuples, just increase c2
         c2+=qpow
       end
       while c2 <= length(Sieve)
           Sieve[c2] += logq
           if nextqpow > qlimit
               prod = (J + (c1 + c2)*H + c1*c2)  #< p for p with > 5 digits
               nextp = nextqpow
               while rem(prod,nextp) == 0
                   Sieve[c2] += logq
                   nextp = nextp*q
               end
           end
           c2 += qpow
       end
       qpow = nextqpow
     end
   end

   #include relations / check sieve for full factorizations.
   rel = Hc1*H1

   for c2 in 1:length(Sieve)
     n = rel%p
     nbn = nbits(n)-1
     if abs(Sieve[c2] - nbn) < 1 
       #generate Factorbase based on FBs with new c_i�s
       if issmooth(FBs,fmpz(n))
         dict_factors = Hecke.factor(FBs,fmpz(n))
         #Include each H + c_i in extended factor basis.
         r = length(Indx)+1
         if !((Hc1) in keys(Indx))
           push!(FB,Hc1)
           push!(Indx, Hc1 => r)
         end#(FB = vcat(FB,[H + c1])) #push!(FB,wert)
         r = length(Indx)+1
         Hc2 = H + c2
         if !((Hc2) in keys(Indx))
           push!(FB,Hc2)
           push!(Indx,(Hc2) => r)
         end#(FB = vcat(FB,[H + c2]))
         #Include relation (H + c1)*(H + c2) = fact.
         #row = nrows(A) + 1 # insert new relation (new row)to sparse_matrix
         J1 = Vector{Int64}([])
         V = Vector{Int64}([])
         for (prime,power) in dict_factors
           if !(power == 0)
             push!(J1,Indx[prime])
             push!(V,Int(power))
           end
         end
         if c1 == c2
           push!(J1,Indx[Hc1])
           push!(V,-2)
         else
           push!(J1,Indx[Hc1])
           push!(J1,Indx[Hc2])
           push!(V,-1)
           push!(V,-1)
         end
         push!(A,sparse_row(zz, J1, V))
         push!(len, length(J1))
       end
     end
     rel+=Hc1
   end
 end
 #increase Sieve 
 if nrows(A)/length(FB) < ratio
   qlimit += inc[1]
   climit += inc[2]
   return sieve(F,(qlimit, climit, ratio, inc))
 end
<<<<<<< HEAD
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB)
>>>>>>> 37ff6a677 (Sieve: values of size sqrt(p) have type Int now + extra sieve for Nemo.GaloisField)
=======
 return set_attribute!(F, :qlimit=>qlimit, :climit=>climit, :ratio=>ratio, :inc=>inc, :RelMat=>A, :FB_array=>FB, :len=>len)
>>>>>>> 6f2458d06 (before script)
end

###############################################################################
#
#   Auxiliary Logs
#
###############################################################################

@doc raw"""
    log_dict(F::Nemo.Galois(Fmpz)Field, A::SMat, TA::SMat) -> Nemo.Galois(Fmpz)Field

Given a field $F$ with attributes from sieve, logs of factorbase are computed and added to $F$.
"""
<<<<<<< HEAD
function log_dict(F::T, A, TA, WIEDEMANN=true)where T<:Union{Nemo.fpField, Nemo.FpField}
=======
function log_dict(F::T, A, TA, WIEDEMANN=true)where T<:Union{Nemo.GaloisField, Nemo.GaloisFmpzField}
>>>>>>> 6f2458d06 (before script)
  p = get_attribute(F, :p)
  if WIEDEMANN
    cnt = 0
    if !wiedemann(A, TA)[1]
      @warn "wiedemann failed"
      return F
    end
    z = true 
    while z
      kern = wiedemann(A, TA)[2]
      cnt+=1
<<<<<<< HEAD
      cnt < 5 || return Dict{ZZRingElem, ZZRingElem}([]),Vector{ZZModRingElem}([]),FactorBase(ZZRingElem[])
=======
      cnt < 5 || return Dict{fmpz, fmpz}([]),Vector{fmpz_mod}([]),FactorBase(fmpz[])
>>>>>>> 6f2458d06 (before script)
      if !iszero(kern)
        z = false
      end
    end
  else
    dim, kern = kernel(matrix(A))
    @assert dim == 1
  end
  kern = inv(kern[1]).*kern #norm kernelvec
  # recon FB_logs mod p  mod p (note this works here if (p-1)/2 prime) Only 2 checks necessary.
  Q,L = Array{ZZRingElem}([]),Array{ZZRingElem}([])
  two = ZZRingElem(2)
  _modulus = get_attribute(F, :_modulus)
  u,v = get_attribute(F, :u), get_attribute(F, :v)
  FB = get_attribute(F, :FB_array)
  a = get_attribute(F, :primitive_elem)
  l = get_attribute(F, :fb_length)
  for i in 1:l
    temp = lift(kern[i])*two*u
    test1 = temp%(p-1)
    test2 = (temp + v*_modulus)%(p-1)
    q_temp = FB[i]
    if a^test1 == q_temp   
      push!(Q,q_temp)
      push!(L,ZZRingElem(test1))
    elseif a^test2 == FB[i]
      push!(Q,q_temp)
      push!(L,ZZRingElem(test2))
    end 
  end 
  
  Logdict = Dict(zip(Q,L))

  length(Logdict) == l ? (@vprint :DiscLog 2 "FB_LOGS: all FB logs found") : (@vprint :DiscLog 2 "FB_LOGS: at least $(l-length(Logdict)) logarithms not found") 
  set_attribute!(F, :Logdict=>Logdict, :kern=>kern, :Q=>FactorBase(Q))
  return F
end

@doc raw"""
    log(F::Nemo.Galois(Fmpz)Field, b) -> ZZRingElem

Returns $g$ s.th. $a^g == b$ given the factorbase logs in $F$.
"""
function log(F::T, b) where T<:Union{Nemo.fpField, Nemo.FpField}
  #return log_a(b) i.e x s.t a^x = b
  p = get_attribute(F, :p)
  p_elem = get_attribute(F, :primitive_elem)
  FB = get_attribute(F, :Q)
  FB_logs = get_attribute(F, :Logdict)
  if typeof(FB_logs)==Nothing
    @warn "FB_logs empty"
    return 0
  end
  randomexp = ZZRingElem(rand(1:p-1))
  while !issmooth(FB,ZZRingElem(lift(b*p_elem^randomexp)))
    randomexp = ZZRingElem(rand(1:p-1))
  end  
  factorization = Hecke.factor(FB,lift(b*p_elem^randomexp))

  logb = -randomexp + sum([exp*FB_logs[prime] for (prime,exp) in factorization])
  return logb
end

###############################################################################
#
#   DISCRETE LOGARITHM IN SAFE PRIME FIELDS
#
###############################################################################

@doc raw"""
    IdxCalc(a::gfp_(fmpz_)elem, b::gfp_(fmpz_)elem, F=parent(a)) -> Tupel{ZZRingElem, Nemo.Galois(Fmpz)Field} 

Tries to find $g$ s.th. $a^g == b$ where $a$ is primitive element of $F$.
"""
function IdxCalc(a::T, b::T, F=parent(a)) where T<:Union{fpFieldElem, FpFieldElem} #RingElem better?
  @assert parent(a) === parent(b)
<<<<<<< HEAD
  b==1 && return ZZRingElem(0), F
  b==a && return ZZRingElem(1), F
=======
  b==1 && return fmpz(0), F
  b==a && return fmpz(1), F
>>>>>>> 1e3d19dbc (tests updated, sieve improved)
  set_attribute!(F, :a=>a)
  if typeof(get_attribute(F, :RelMat))==Nothing
    @vtime :DiscLog 3 sieve(F)
  end
  if typeof(get_attribute(F, :Logdict))==Nothing
    p = get_attribute(F, :p)
    _modulus = div((p-1),2)
    two = ZZRingElem(2)
    F2 = residue_ring(ZZ, _modulus) #change it when prepro fixed
    set_attribute!(F, :F2=>F2)
    c, u, v = gcdx(two, _modulus)
    c == 1 || (@error "FB_LOGS: 2 ,(p-1)/2 not coprime")
    set_attribute!(F, :u=>u, :v=>v)
    set_attribute!(F, :_modulus=>_modulus)
    #Preprocessing
    A = change_base_ring(F2, get_attribute(F,:RelMat))
    TA = transpose(A)
<<<<<<< HEAD
    A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length),2)
=======
    A, TA = sp_prepro(A, TA, get_attribute(F, :fb_length),10)
>>>>>>> 6f2458d06 (before script)
    #Wiedemann + dict with logs of FB
    @vtime :DiscLog 3 log_dict(F, A, TA)
  end
  logb = log(F, b)
  if logb == 0
    return logb, F
  end
  if a != get_attribute(F, :primitive_elem) 
    p = get_attribute(F, :p)
    loga = log(F, a)
<<<<<<< HEAD
    logb = solvemod(loga, logb, ZZRingElem(p-1))
=======
    logb = solvemod(loga, logb, fmpz(p-1))
>>>>>>> 37ff6a677 (Sieve: values of size sqrt(p) have type Int now + extra sieve for Nemo.GaloisField)
  end
  return logb, F 
end
