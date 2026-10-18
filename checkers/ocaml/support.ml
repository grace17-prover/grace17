(* Strict JSON, canonical UTF-16 key ordering, and SHA-256 for the independent checkers.
   Part of the Grace17 proof assistant for mathematics based on set theory.
   Copyright (c) 2026 Grant Passmore.
   Released under the Apache License 2.0. See LICENSE in the repository root.
   Authors: Grant Passmore *)

(* Small standalone support layer: strict JSON, canonical UTF-16 key ordering,
   and SHA-256. No GRACE17 producer code or foreign checker is called. *)
exception Reject of string

let fail s = raise (Reject s)

let require b s = if not b then fail s

let read_file path =
  let c = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in c)
    (fun () -> really_input_string c (in_channel_length c))

let utf8 s =
  let rec loop i acc =
    if i = String.length s then List.rev acc
    else
      let b = Char.code s.[i] in
      let n, low, value =
        if b < 128 then (1, 0, b)
        else if b >= 194 && b <= 223 then (2, 128, b land 31)
        else if b >= 224 && b <= 239 then (3, 2048, b land 15)
        else if b >= 240 && b <= 244 then (4, 65536, b land 7)
        else fail "invalid UTF-8"
      in
      require (i + n <= String.length s) "truncated UTF-8" ;
      let v = ref value in
      for j = 1 to n - 1 do
        let x = Char.code s.[i + j] in
        require (x land 192 = 128) "invalid UTF-8 continuation" ;
        v := (!v lsl 6) lor (x land 63)
      done ;
      require
        (!v >= low && !v <= 0x10ffff && not (!v >= 0xd800 && !v <= 0xdfff))
        "noncanonical UTF-8" ;
      loop (i + n) (!v :: acc)
  in
  loop 0 []

let utf16 s =
  List.concat_map
    (fun n ->
      if n < 65536 then [n]
      else
        let x = n - 65536 in
        [0xd800 + (x lsr 10); 0xdc00 + (x land 1023)] )
    (utf8 s)

let add_utf8 b n =
  let byte x = Buffer.add_char b (Char.chr x) in
  if n < 128 then byte n
  else if n < 2048 then (
    byte (192 lor (n lsr 6)) ;
    byte (128 lor (n land 63)) )
  else if n < 65536 then (
    byte (224 lor (n lsr 12)) ;
    byte (128 lor ((n lsr 6) land 63)) ;
    byte (128 lor (n land 63)) )
  else (
    byte (240 lor (n lsr 18)) ;
    byte (128 lor ((n lsr 12) land 63)) ;
    byte (128 lor ((n lsr 6) land 63)) ;
    byte (128 lor (n land 63)) )

type json =
  | Null
  | Bool of bool
  | Num of int
  | Str of string
  | Arr of json list
  | Obj of (string * json) list

let parse s =
  let i = ref 0 and len = String.length s in
  let peek () = if !i < len then s.[!i] else '\000' in
  let take () =
    require (!i < len) "truncated JSON" ;
    let c = s.[!i] in
    incr i ; c
  in
  let rec ws () =
    match peek () with ' ' | '\n' | '\r' | '\t' -> incr i ; ws () | _ -> ()
  in
  let hex () =
    let v = ref 0 in
    for _ = 1 to 4 do
      let c = take () in
      let x =
        match c with
        | '0' .. '9' -> Char.code c - 48
        | 'a' .. 'f' -> Char.code c - 87
        | 'A' .. 'F' -> Char.code c - 55
        | _ -> fail "bad JSON escape"
      in
      v := (!v lsl 4) + x
    done ;
    !v
  in
  let string () =
    require (take () = '"') "expected string" ;
    let b = Buffer.create 32 in
    let rec loop () =
      match take () with
      | '"' ->
          let s = Buffer.contents b in
          ignore (utf8 s) ;
          s
      | '\\' ->
          ( match take () with
          | '"' -> Buffer.add_char b '"'
          | '\\' -> Buffer.add_char b '\\'
          | '/' -> Buffer.add_char b '/'
          | 'b' -> Buffer.add_char b '\b'
          | 'f' -> Buffer.add_char b '\012'
          | 'n' -> Buffer.add_char b '\n'
          | 'r' -> Buffer.add_char b '\r'
          | 't' -> Buffer.add_char b '\t'
          | 'u' ->
              let n = hex () in
              let n =
                if n >= 0xd800 && n <= 0xdbff then (
                  require (take () = '\\' && take () = 'u') "missing surrogate" ;
                  let m = hex () in
                  require (m >= 0xdc00 && m <= 0xdfff) "bad surrogate" ;
                  0x10000 + ((n - 0xd800) lsl 10) + m - 0xdc00 )
                else (
                  require (n < 0xdc00 || n > 0xdfff) "unpaired surrogate" ;
                  n )
              in
              add_utf8 b n
          | _ -> fail "bad escape" ) ;
          loop ()
      | c ->
          require (Char.code c >= 32) "control in JSON string" ;
          Buffer.add_char b c ;
          loop ()
    in
    loop ()
  in
  let rec value depth =
    require (depth < 1000) "JSON nesting limit" ;
    ws () ;
    match peek () with
    | '"' -> Str (string ())
    | '[' ->
        incr i ;
        ws () ;
        let rec items acc =
          if peek () = ']' then (
            incr i ;
            Arr (List.rev acc) )
          else
            let v = value (depth + 1) in
            ws () ;
            match take () with
            | ']' -> Arr (List.rev (v :: acc))
            | ',' ->
                ws () ;
                require (peek () <> ']') "trailing comma" ;
                items (v :: acc)
            | _ -> fail "bad array"
        in
        items []
    | '{' ->
        incr i ;
        ws () ;
        let rec fields acc =
          if peek () = '}' then (
            incr i ;
            Obj (List.rev acc) )
          else
            let k = string () in
            require (not (List.mem_assoc k acc)) "duplicate JSON key" ;
            ws () ;
            require (take () = ':') "missing colon" ;
            let v = value (depth + 1) in
            ws () ;
            match take () with
            | '}' -> Obj (List.rev ((k, v) :: acc))
            | ',' ->
                ws () ;
                require (peek () <> '}') "trailing comma" ;
                fields ((k, v) :: acc)
            | _ -> fail "bad object"
        in
        fields []
    | 't' | 'f' | 'n' ->
        let word, v =
          match peek () with
          | 't' -> ("true", Bool true)
          | 'f' -> ("false", Bool false)
          | _ -> ("null", Null)
        in
        String.iter (fun c -> require (take () = c) "bad literal") word ;
        v
    | '-' | '0' .. '9' -> (
        let start = !i in
        if peek () = '-' then incr i ;
        require (peek () >= '0' && peek () <= '9') "bad number" ;
        if peek () = '0' then incr i
        else
          while peek () >= '0' && peek () <= '9' do
            incr i
          done ;
        let t = String.sub s start (!i - start) in
        try Num (int_of_string t) with _ -> fail "JSON integer overflow" )
    | _ -> fail "invalid JSON"
  in
  let v = value 0 in
  ws () ;
  require (!i = len) "trailing JSON" ;
  v

let str = function Str s -> s | _ -> fail "expected JSON string"

let num = function Num n -> n | _ -> fail "expected JSON integer"

let arr = function Arr a -> a | _ -> fail "expected JSON array"

let obj = function Obj a -> a | _ -> fail "expected JSON object"

let get j k =
  match List.assoc_opt k (obj j) with
  | Some v -> v
  | None -> fail ("missing field " ^ k)

let optional j k d = match List.assoc_opt k (obj j) with Some v -> v | None -> d

let pairs j =
  List.map
    (function Arr [Str k; v] -> (k, v) | _ -> fail "invalid association")
    (arr j)

let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"' ;
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\b' -> Buffer.add_string b "\\b"
      | '\012' -> Buffer.add_string b "\\f"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | c when Char.code c < 32 ->
          Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c )
    s ;
  Buffer.add_char b '"' ;
  Buffer.contents b

let rec canonical = function
  | Null -> "null"
  | Bool b -> string_of_bool b
  | Num n -> string_of_int n
  | Str s -> quote s
  | Arr a -> "[" ^ String.concat "," (List.map canonical a) ^ "]"
  | Obj o ->
      let o = List.sort (fun (a, _) (b, _) -> compare (utf16 a) (utf16 b)) o in
      "{"
      ^ String.concat "," (List.map (fun (k, v) -> quote k ^ ":" ^ canonical v) o)
      ^ "}"

module Sha256 = struct
  open Int32

  let ( +! ) = add

  let rotr x n = logor (shift_right_logical x n) (shift_left x (32 - n))

  let xor3 a b c = logxor a (logxor b c)

  let k =
    Array.map of_string
      [| "0x428a2f98"
       ; "0x71374491"
       ; "0xb5c0fbcf"
       ; "0xe9b5dba5"
       ; "0x3956c25b"
       ; "0x59f111f1"
       ; "0x923f82a4"
       ; "0xab1c5ed5"
       ; "0xd807aa98"
       ; "0x12835b01"
       ; "0x243185be"
       ; "0x550c7dc3"
       ; "0x72be5d74"
       ; "0x80deb1fe"
       ; "0x9bdc06a7"
       ; "0xc19bf174"
       ; "0xe49b69c1"
       ; "0xefbe4786"
       ; "0x0fc19dc6"
       ; "0x240ca1cc"
       ; "0x2de92c6f"
       ; "0x4a7484aa"
       ; "0x5cb0a9dc"
       ; "0x76f988da"
       ; "0x983e5152"
       ; "0xa831c66d"
       ; "0xb00327c8"
       ; "0xbf597fc7"
       ; "0xc6e00bf3"
       ; "0xd5a79147"
       ; "0x06ca6351"
       ; "0x14292967"
       ; "0x27b70a85"
       ; "0x2e1b2138"
       ; "0x4d2c6dfc"
       ; "0x53380d13"
       ; "0x650a7354"
       ; "0x766a0abb"
       ; "0x81c2c92e"
       ; "0x92722c85"
       ; "0xa2bfe8a1"
       ; "0xa81a664b"
       ; "0xc24b8b70"
       ; "0xc76c51a3"
       ; "0xd192e819"
       ; "0xd6990624"
       ; "0xf40e3585"
       ; "0x106aa070"
       ; "0x19a4c116"
       ; "0x1e376c08"
       ; "0x2748774c"
       ; "0x34b0bcb5"
       ; "0x391c0cb3"
       ; "0x4ed8aa4a"
       ; "0x5b9cca4f"
       ; "0x682e6ff3"
       ; "0x748f82ee"
       ; "0x78a5636f"
       ; "0x84c87814"
       ; "0x8cc70208"
       ; "0x90befffa"
       ; "0xa4506ceb"
       ; "0xbef9a3f7"
       ; "0xc67178f2" |]

  let digest s =
    let len = String.length s in
    let n = (len + 9 + 63) / 64 * 64 in
    let b = Bytes.make n '\000' in
    Bytes.blit_string s 0 b 0 len ;
    Bytes.set b len '\128' ;
    let bits = Int64.mul (Int64.of_int len) 8L in
    for i = 0 to 7 do
      Bytes.set b
        (n - 1 - i)
        (Char.chr
           (Int64.to_int (Int64.logand 255L (Int64.shift_right_logical bits (8 * i)))))
    done ;
    let h =
      Array.map of_string
        [| "0x6a09e667"
         ; "0xbb67ae85"
         ; "0x3c6ef372"
         ; "0xa54ff53a"
         ; "0x510e527f"
         ; "0x9b05688c"
         ; "0x1f83d9ab"
         ; "0x5be0cd19" |]
    in
    let w = Array.make 64 0l in
    for off = 0 to (n / 64) - 1 do
      for i = 0 to 15 do
        let v = ref 0l in
        for j = 0 to 3 do
          v :=
            logor (shift_left !v 8)
              (of_int (Char.code (Bytes.get b ((64 * off) + (4 * i) + j))))
        done ;
        w.(i) <- !v
      done ;
      for i = 16 to 63 do
        let x = w.(i - 15) and y = w.(i - 2) in
        w.(i)
        <- w.(i - 16)
           +! xor3 (rotr x 7) (rotr x 18) (shift_right_logical x 3)
           +! w.(i - 7)
           +! xor3 (rotr y 17) (rotr y 19) (shift_right_logical y 10)
      done ;
      let v = Array.copy h in
      for i = 0 to 63 do
        let a = v.(0) and e = v.(4) in
        let t1 =
          v.(7)
          +! xor3 (rotr e 6) (rotr e 11) (rotr e 25)
          +! logxor (logand e v.(5)) (logand (lognot e) v.(6))
          +! k.(i) +! w.(i)
        in
        let t2 =
          xor3 (rotr a 2) (rotr a 13) (rotr a 22)
          +! xor3 (logand a v.(1)) (logand a v.(2)) (logand v.(1) v.(2))
        in
        for j = 7 downto 1 do
          v.(j) <- v.(j - 1)
        done ;
        v.(4) <- v.(4) +! t1 ;
        v.(0) <- t1 +! t2
      done ;
      for i = 0 to 7 do
        h.(i) <- h.(i) +! v.(i)
      done
    done ;
    String.concat "" (Array.to_list (Array.map (fun x -> Printf.sprintf "%08lx" x) h))
end
