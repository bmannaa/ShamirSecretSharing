open FiniteField

module MakeSSS (Field : FiniteFieldSig) = struct
        open Field
      
        (* Input t:int
         * Output a list of (t-1) random integers in the range [0..order) *)
        let coeff t = Random.self_init ();
              List.init (t-1) (fun _-> field_of_int (Random.int order))
        
        (* t out of n sharing for s 
         * Input n:int t:int s:Field.t 
         * Output a list of shares, each is a pair (int, Field.t) *)
        let share n t s = assert (n < order);
                          let poly = s :: coeff t in
                          let f v p c  =  c <*> (v <^> p) in (* coefficient * value^exponent *)
                          let key v =  List.fold_left (<+>) zero (List.mapi (f v) poly) in
                              List.init n (fun i -> (i+1,key (field_of_int (i+1))))

        (* Lagrange interpolation for finite fields 
         * Input k:Field.t List  i:Field.t
         * Output the constant coefficient of the polynomial of type Field.t
         * formula TT (j in k and i/=j) -j/(i-j) *)
        let c k i = let i' = field_of_int i in
                    let f j = let j' = field_of_int j in
                    if j' = i' then one
                    else match inv (j' <-> i') with
                                 Some t -> j' <*> t
                               | None   -> raise (Failure "not invertible")
                    in
                        List.fold_left (<*>) one (List.map f k)

        (* Secret revealing procedure 
         * Input: list of shares 
         * Output: Field.t 
         * reveals the secret if given enough correct shares *)
        let reveal l = let k = List.map fst l in 
                           List.fold_left (<+>) zero (List.map (fun (i,v) -> v <*> c k i) l)

        (* t out of n sharing for a list of secrets 
         * Input n:Int t:Int l: Field.t List
         * output is a list of shares each is (int, [Field.t]) 
         * Warning: length of each share is equal to the length of the secret *)
        let shareList n t fieldlist = let f c ls  = List.map2 (fun (i,c) (j,l) -> (i,c::l)) (share n t c) ls in
                                      let ls = List.init n (fun i -> (i+1,[])) in
                                            List.fold_right f fieldlist ls

        (* Secrete revealing procedure for lists
         * Input l: (int, Field.t) List
         * Output Field.t List
         * reveals the secrets if given enought correct shares *)
        let recoverList l = match l with
                                  []       -> []
                                | (_,r)::_ -> let m = List.length r in
                                let transpose (n, keys) ls = List.map2 (fun key l' -> (n,key)::l') keys ls in
                                let transposed = List.fold_right transpose l (List.init m (fun _->[])) in
                                        List.map reveal transposed
        
        (* representation of integer in base-n
         * Input n:int a:int
         * output int List each in the range [0..n) *)
        let tobase n a = let euclid x y = (x/ y, x mod y) in 
                         let rec loop accum b = if b < n then b::accum else
                                                 let (q,r) = euclid b n in 
                                                  loop (r::accum) q
                        in loop [] a

        (* produces an integer from its base-n representation
         * Input n:Int l:int List
         * Output an integer value of the base-n representation l *)
        let frombase n l = (List.fold_left (fun a b -> n * (a + b)) 0 l)/ n

        (* method to put an integer into base-x where x is the Field.order
         * Input n:int
         * Output Field.t List *)
        let fromIntToFieldBase n = let sign = if n < 0 then 1 else 0 in  
                                     (tobase order (abs n) )@ [sign] 

        (* t out of n sharing for secrete integer m
         * Input n:int t:int m:int
         * output list of shares each of type (int,int) 
         * Warning the magnitude of each share reveals the range of the secret 
         * e.g. if the shares are in the range [0..2^16) the secret is in the range [0..2^8) 
         * (order-1):: is a hack. frombase order [zero,....] will ignore zero. To avoid this we append order-1 *)
        let shareInt n t m = let fieldlist = List.map field_of_int (fromIntToFieldBase m) in 
                             let f (i,l) = (i,frombase order ((order-1)::(List.map int_of_field l))) in 
                               List.map f (shareList n t fieldlist)

        (* reveal method for secret integer
         * Input list of shares, each is a pair (int, int)
         * Output int
         * reveals the secret if given enough correct shares *)
        let revealInt l = let f (i, n) = (i, List.map (field_of_int ) (List.tl (tobase order n))) in 
                          let r = List.rev  (recoverList (List.map f l)) in 
                          let isnegative = int_of_field (List.hd r) == 1 in 
                          let m = frombase order (List.rev_map int_of_field (List.tl r)) in
                            if isnegative then (-1 * m) else m
                           

end;;
