module type FiniteFieldSig = sig
        type t
        (* order of the finite field *)
        val order : int 

        (* one-to-one mapping between integers [0..ord) to field elements *)
        val field_of_int : int -> t
        val int_of_field : t -> int
        
        (* additive and multiplicative identities *)
        val zero  : t
        val one   : t

        (* field operations *)
        val (<+>) : t -> t -> t
        val (<->) : t -> t -> t
        val (<*>) : t -> t -> t
        val (<^>) : t -> int -> t
        val inv   : t -> t option 
end;;

(* Galois field of 256 elements
 * the operations are computed with respect to a log and antilog table
 * populated with the generator 3 *)
module GF256  = struct
        (* proper mod for integers *)
        let (%) a b = let remainder = a mod b in
                      if remainder >=0 then remainder
                      else remainder + b

        (* shift left for chars *)
        let (<<=) a n = let a' = (int_of_char a ) lsl n in
                        char_of_int (a' land 255)

        (* shift right for char. *)
        let (=>>) a n = char_of_int ((int_of_char a) lsr n)

        (* method to test if the low bit is set *)
        let lbitset a = (int_of_char a) land 1 = 1

        (* method to test if the high bit is set *)
        let hbitset a = (int_of_char a) land 128 = 128

        (* f256 Galois field
         * This is a field of 256 elements
         * Alternatively, the field generated over F2 by F2[x]/x^8 + x^4 + x^3 + x + 1 *)
        type t = char

        (* order of the field *)
        let order = 256

        (* one-to-one mapping between integers 0<= m < 255 and field elements 
         * does not necessarily preserve order *)
        let field_of_int a = assert (a >= 0 && a < order); char_of_int a

        let int_of_field a = int_of_char a

        (* additive identity *)
        let zero = char_of_int 0

        (* multiplicative identity *)
        let one = char_of_int 1

        (* addition operation *)
        let (<+>) a b = char_of_int ((int_of_char a) lxor (int_of_char b))

        (* subtraction operation *)
        let (<->) a b = a <+> b

        (* Initialization of the log and antilog table for faster multiplication and division 
         * using 3 as a generator 
         * logTable table maps key a:t to value i:int such that a = 3 <^> i 
         * antilogTable maps keys i:int to values a:t such that a = 3 <^> i *)
        module CharTable = Map.Make(Char)
        module IntTable = Map.Make(struct type t = int let compare = compare end)
        let logTable = ref CharTable.empty
        let antilogTable = ref IntTable.empty
        let initialize = let a = ref (char_of_int 1) in
                         for c=0 to 254 do
                                 let t = !a in
                                 antilogTable:= IntTable.add c t !antilogTable;
                                 let a_hbit = hbitset !a in
                                 if a_hbit then a:= (!a <<= 1) <-> char_of_int 27
                                 else a:= !a <<= 1;
                                 a:=!a <-> t;
                                 logTable:=CharTable.add t c !logTable
                         done

        (* multiplication operation *)
        let (<*>) a b = if (a = zero || b = zero) then zero
                        else let i = CharTable.find a !logTable in
                             let j = CharTable.find b !logTable in
                             let k = (i+j) % 255 in
                             IntTable.find k !antilogTable


        (* exponentation *)
        let (<^>) a b = let i = CharTable.find a !logTable in
                        let k = (i * b) % 255 in
                        IntTable.find k !antilogTable

        (* inverse operation *)
        let inv a = if a = zero then None
                    else let i = CharTable.find a !logTable in
                         let k = -i % 255 in
                         Some (IntTable.find k !antilogTable)

end;;

(* Implementation of Galois field of 256 elements 
 * This impelementation does not use log and antilog tables
 * probably slightly slower. *)
module GF256NI  = struct
        (* shift left for chars *)
        let (<<=) a n = let a' = (int_of_char a ) lsl n in
                        char_of_int (a' land 255)

        (* shift right for char. *)
        let (=>>) a n = char_of_int ((int_of_char a) lsr n)

        (* method to test if the low bit is set *)
        let lbitset a = (int_of_char a) land 1 = 1

        (* method to test if the high bit is set *)
        let hbitset a = (int_of_char a) land 128 = 128

        (* f256 Galois field
         * This is a field of 256 elements
         * Alternatively, the field generated over F2 by F2[x]/x^8 + x^4 + x^3 + x + 1 *)
        type t = char

        (* order of the field *)
        let order = 256

        (* one-to-one mapping between integers 0<= m < 255 and field elements 
         * does not necessarily preserve order *)
        let field_of_int a = assert (a >= 0 && a < order); char_of_int a

        let int_of_field a = int_of_char a

        (* additive identity *)
        let zero = char_of_int 0

        (* multiplicative identity *)
        let one = char_of_int 1

        (* addition operation *)
        let (<+>) a b = char_of_int ((int_of_char a) lxor (int_of_char b))

        (* subtraction operation *)
        let (<->) a b = a <+> b

        (* multiplication operation without log and antilog tables*)
        let (<*>) a b = let a' = ref a in
                        let b' = ref b in
                        let p = ref zero in
                           for i=0 to 7 do
                                if lbitset !b' then p:= !p <+> !a'; (* a + product *)
                                if hbitset !a' then a':= (!a'<<= 1) <-> char_of_int 27 (* a * x mod x^8+x^4+x^3+x+1 *)
                                else a':= !a' <<= 1; (* a * x *)
                                b':=!b' =>> 1; (* b-b(0)/x *)
                           done;
                           !p

        (* exponentiation operation without log and antilog tables*)
        let (<^>) a b = let rec loop accum i = if i = 0 then accum
                                               else  loop (a <*> accum) (i-1)
                        in loop one b



        (* degree of an element as a polynomial over F2 *)
        let deg a = let rec deg' d a' = if a' <= 1 then d else deg' (d+1) (a' lsr 1) in
                    deg' 0 (int_of_char a)

        (* extended gcd computation for polynomials over F2 
         * input integers x y
         * output integers (r,s,g,p,q) 
         * r x + s y = g and x = pg and y = q g *)
        let gcd x y = let deg a = let rec deg' d a' = if a' <= 1 then d else deg' (d+1) (a' lsr 1)
                                  in deg' 0 a
                      in
                      let rec gcd' a b (r,s) (q,p) = if b = 0 then
                                                       (r,s,a,q,p)
                                                     else if a = 0 then
                                                       (q,p,b,r,s)
                                                      else match deg a < deg b with
                                                              true  -> gcd' b a (q,p) (r,s)
                                                            | false -> let div = deg a - deg b in
                                                                       let r'  = r lxor (q lsl div) in  (* r - X^div * q *)
                                                                       let s'  = s lxor (p lsl div) in  (* s - x^div * p *)
                                                                       let a'  = a lxor (b lsl div) in  (* remainder: a - x^div * b *)
                                                                       gcd' a' b (r',s') (q,p)
                      in
                      let (r,s,g, neg_q, p) = gcd' x y (1,0) (0,1)
                      in (r,s,g,p, 0 lxor neg_q)

        (* inverse operation
         * input char b
         * output char option
         * if inv b = Some k then k <*> b = 1 *)
        let inv b = if b = zero then None
                    else let b' = int_of_char b in
                         let (r,s,g,neg_q,p) = gcd 283 b' in
                         let inverse = char_of_int s in
                         if g != 1 then raise (Failure ("gcd not 1, gcd = "^string_of_int g))
                         else if inverse <*> b != one then raise( Failure "not a multiplicative inverse")
                         else Some inverse

end;;

