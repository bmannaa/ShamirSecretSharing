open ShamirSecretSharing
open FiniteField

let rec splitAround n l = match (n,l) with
                             (n,[]) -> raise (Invalid_argument "short list")
                           | (0,a::ls) -> ([], ls)
                           | (n,a::ls) -> let (xs,ys) = splitAround (n-1) ls in
                                          (a::xs,ys)
module SSS = MakeSSS(GF256)

let test () = let r = Random.int 256 in 
              if (r = 0) then ('\000','\000') else
                let t = Random.int r in 
                if (t = 0) then ('\000','\000') else
                  let n = char_of_int (Random.int 256) in 
                  let s = ref (SSS.share r t n) in
                  let a = ref [] in 
                  let d = ref t in 
                  while (!d != 0) do 
                    let j = Random.int (List.length (!s)) in 
                    a := (List.nth (!s) j) :: !a; 
                    s := (fun (a,b) -> a@b )(splitAround j !s);
                    d:= !d -1
                  done;
                 (n,SSS.reveal !a)

let quickCheck n = Random.self_init ();
                   let rec check x = match x with
                                           0 -> true
                                         | y -> let (a,b) = test () in 
                                                  (a=b) && (check (y-1))
                   in check n


let test' () = let r = Random.int 256 in
               if (r = 0) then (0,0) else
                let t = Random.int r in
                if (t = 0) then (0,0) else
                   let n = Random.int 1073741823 in
                   let s = ref (SSS.shareInt r t n) in 
                   let a = ref [] in 
                   let d = ref t in 
                    while (!d !=0 ) do
                        let j = Random.int (List.length (!s)) in
                        a := (List.nth (!s) j) :: !a;
                        s := (fun (a,b) -> a@b )(splitAround j !s);
                        d:= !d -1
                  done;
                 (n,SSS.revealInt !a)


let quickCheck' n = Random.self_init ();
                    let rec check x = match x with
                                           0 -> true
                                         | y -> let (a,b) = test' () in
                                                  (a=b) && (check (y-1))
                   in check n



