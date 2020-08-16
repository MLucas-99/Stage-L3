(*  Faugère's F5 algorithm in Maple - by Lucas Morisset - L3 Internship tutored by Frédéric Chyzak and Jérémie Berthomieu *)

(* Various Data structures used and notations :
    - Set of polynomials generating the ideal wich we are trying to calculate the Gröbner basis : Data structure - Set, Notation - 'F'
    - Vectors of (k[X_1,..X_n])^s : Data struture - row Vector, Notation - 'a', 'g', 'h' or 'x' (every a[i] is normalized in order to test the equality to 0 easily)
    - Representation of the monomial order used : Data type - ShortMonomialOrder, Notation - 'order'
    - Priority queue storing remaining vectors to treat (we always extract the smallest element according to POT Order) : Data Structure - heap, Notation - P
    - Partial Groebner basis : Data structure - set (may change to table), Notation - G
*)

(* This work was mostly inspired by chapter 10 (part 4) of 'Ideals, Varieties and Algorithms (4th edition)' by Cox, Little & O'Shea
   if any doubt remains on the efficiency of the algorithms written below, the reader may want to read this chapter
*)

F5_Setup := proc(F::list, order::ShortMonomialOrder,$)
   return module()
   export Phi, Lm, Lt,Lt_Phi, Lm_Phi, GT_POT, Signature, Reduction, Sv, Add_Sv, Criterion_W, Create_E, Create_all_E, Koszul, Init_heap;
   local s := numelems(F):
   
   (* 'Phi' is the evaluation fonction phi : (k[X_1,..X_n])^s --> k[X_1,..X_n] *)  
   Phi := proc(a, $)
       local i;
       return expand(add(a[i]*F[i], i = 1 .. s));
   end:
   
   
   (* 'Lm' stands for LeadingMonomial, it's a procedure returning the Leading monomial of 'a', with respect to 'order'*)
   Lm_Phi := proc(p, $) 
       return Groebner:-LeadingMonomial(Phi(p),order); 
   end:
   
   
   (* 'Lt' stands for LeadingTerm *)
   Lt_Phi := proc(p, $)
       return `*`(Groebner:-LeadingTerm(Phi(p),order));
   end:
   
   
   Lm := proc(poly, $)
       return Groebner:-LeadingMonomial(poly,order);
   end:
   
   
   Lt := proc(poly, $)
       return `*`(Groebner:-LeadingTerm(poly,order));
   end:
   
   
   (* 'GT_POT' is the ordering test, respecting the POT order, it returns true iff s1 >=_pot s2 *)
   GT_POT := proc(s1, s2, $)
      return evalb(s1[2] > s2[2] or (s1[2] = s2[2] and Groebner:-TestOrder(s2[1],s1[1],order)));
   end:
   
   
   (* 'Signature' is the procedure returning the signature of an element of k[X_1,..X_n])^s *)
   Signature := proc(a,$)
      local i;
      i := s;
      while 0 < i do
          if a[i] <> 0 then
              return [Lm(a[i]), i];
          end if;
          i := i - 1;
      end do;
      return [0,0];       (* The signature of the 0 vector is [0,0], should not be used *)
   end:
   
   
   (* 'Reduction' is a main componnent of F5, it returns a regular S-reducted vector *)
   (* g is the reducted vector of k[X_1,..X_n])^s, H is a finite subset of k[X_1,..X_n])^s we are reducting by *)
   Reduction := proc(g, H, $)
      local l, u, d, dif, i, ReductionOccurred, lt_H, m;
      l := numelems(H);
      if l = 0 then return g; end if;
      u := g;
      dif := normal(Phi(u));        (* dif is the polynomial used to show the algorithm's terminaiton *)
      
      (* Computation of the leading terms of H *)
      lt_H := [seq(Lt_Phi(H[i]),i=1..l)];
      print(lt_H);
      
      while dif <> 0 do
          m := Lt(dif);
          i := 1;
          ReductionOccurred := false;
          while i <= l and not(ReductionOccurred) do
              d := normal(m*H[i]/lt_H[i]);
              if divide(Lm(m),Lm(lt_H[i])) and not GT_POT(Signature(d), Signature(u)) then
                  u := normal(u - d);
                  dif := normal(dif - Phi(d));
                  ReductionOccurred := true;
              else
                  i := i + 1;
              end if;
          end do;
          if not ReductionOccurred then
              dif := normal(dif - m);
          end if;
      end do;
      print(u, Phi(g), Phi(u));
      return u;
   end:

   (* 'Sv' stands for S-Vector*)
   Sv := proc(g, h, $) 
      local lg := Lt_Phi(g), lh := Lt_Phi(h), M := lcm(lg,lh);
      return expand~(M/lg*g - M/lh*h);
   end:
   
   Add_Sv := proc(P, G, h, $)
       local s_h := Signature(h);
       local k;
       for k in G do
           local s_k := Signature(k);
           if s_k <> s_h then   (* test if the S-vector is regular *)
                heap:-insert(Sv(k,h), P);
                #print(Sv(k,h));
           end if;
       end do;
   end:
   
   
   (* Weak F5 criterion *)
   Criterion_W := proc(sig, sig_G, sig_S, $)
       local a;
       if member(sig, sig_G) then return true end if;
       for a in sig_S do
           if (divide(sig[1],a[1]) and sig[2]=a[2]) then
               return true;
           end if;
       end do;
       return false;
   end:
    
    
   (* auxillary Procedure returning the base vectors of (k[X_1,...X_n])^s, e_i = (0,0,..,0,1,0,..,0) *)
   Create_E := proc(i, $)
       local v := Vector[row](1..s,0);
       v[i] := 1; 
       return v;
   end:
   
   
   Create_all_E := proc()
       local i;
       return [seq(Create_E(i), i = 1..s)];
   end:
   
   
   (* auxillary procedure computing the set of koszul syzygy *)
   Koszul := proc(E, $)
       local i,j;
       return {seq(seq(map(expand,F[i]*E[j] - F[j]*E[i]), j = i+1..s), i = 1..s)};
   end:
    
    
   Init_heap := proc(P, E, $) 
       local i;
       for i from 1 to s do
           heap:-insert(map(expand,E[i]), P);
       end do;
   end:
   
end:
end:


(* F5 Algorithm :
    Input : list [f_1,...f_s], and 'order' which is of type ShortMonomialOrder 
    Output : list, its elements form a Gröbner basis of the ideal <f_1,...,f_s> *)

F5 := proc(F,order)
    local M_F5 := F5_Setup(F,order);  (* Module containing every usefull procedure *)
 
    local G := {}, sig, sig_G := {}, sig_S, g, h, f;

    local E := M_F5:-Create_all_E();
    local S := M_F5:-Koszul(E);

    (* Preparing the heap *) 
    local P := heap:-new(proc(x,y) return M_F5:-GT_POT(M_F5:-Signature(x),M_F5:-Signature(y)) end proc);
    M_F5:-Init_heap(P, E);
  
    (*Computing the initial set of syzygy signature*)
    sig_S := M_F5:-Signature~(S);print(sig_S);

    (* Main calculation *)
    while not heap:-empty(P) do
        print("___________________________________________
        
        
        
        
        ");
        g := heap:-extract(P);
        sig := M_F5:-Signature(g);
        if not M_F5:-Criterion_W(sig,sig_G,sig_S) then
            print("Reduction de : ", g, "par : ", G);
            h := M_F5:-Reduction(g, G);
            if M_F5:-Phi(h) = 0 then        
                if sig <> [0,0] then            (* Their will be divisions by 0 if [0,0] is in sig_S, and it's useless *)
                    S := S union {h};
                    sig_S := sig_S union {sig};
                end if;
            else
                M_F5:-Add_Sv(P, G, h);
                print(P);
                G := G union {h};
                sig_G := sig_G union {sig};
            end if;
        end if;
    end do;

    (* Returns the image of G by Phi *)
    return [seq(M_F5:-Phi(f), f in G)];
end proc:

(*
(* Test *)
gb := F5([x^2 + 1, x*y - z], grlex(x,y,z));

GB := Groebner:-Basis([x^2 + 1, x*y - z], grlex(x,y,z));
map(Groebner:-NormalForm, gb, GB, grlex(x,y,z));  # I(gb) <= I(GB)
map(Groebner:-NormalForm, GB, gb, grlex(x,y,z));  # I(GB) <= I(gb)
*)
