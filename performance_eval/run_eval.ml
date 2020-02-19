open Lexing
open Printf
open MyJsonParser
       
(* Utility functions *)
let chars_of_string (s : string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l)
  in  exp (String.length s - 1) []

let chars_of_int i : char list = chars_of_string (string_of_int i)

let chars_of_float f = chars_of_string (string_of_float f)

let str_of_float_list fs = "[" ^ String.concat "," (List.map string_of_float fs) ^ "]"

let str_of_int_list is   = "[" ^ String.concat "," (List.map string_of_int is) ^ "]"

let sum_floats (fs : float list) : float =
  List.fold_right (+.) fs 0.0

let avg_floats (fs : float list) : float =
  sum_floats fs /. float_of_int (List.length fs)
                                       
let filenames_in_dir (dirname : string) : string list =
  List.sort String.compare (List.map (fun s -> dirname ^ "/" ^ s) 
                              (Array.to_list (Sys.readdir dirname)))
            
let file_sizes (fnames : string list) : int list =
  List.map (fun fname -> (Unix.stat fname).st_size) fnames
                                             
(*
let rec nat_of_int' (i : int) : nat =
  if i = 0 then O else S (nat_of_int' (i - 1))
       
let nat_of_int (i : int) : nat =
  if i < 0 then 
    raise (Invalid_argument "i can't be negative") 
  else 
    nat_of_int' i

let nat_of_float (f : float) : nat =
  nat_of_int (int_of_float f)

let print_char_list cs = List.iter (fun c -> print_string (Char.escaped c)) cs

let rec str_of_nat n = match n with | O -> "O" | S n' -> "S" ^ str_of_nat n'

(* Functions for converting the tokens that the Menhir lexer generates
   to the tokens that Vermillion expects *)
let simplyTypedTokenOfMenhirToken (t : JsonTokenizer.token) : simply_typed_token =
  match t with
  | INT i       -> StInt (nat_of_int i)
  | FLOAT f     -> StFloat (nat_of_float f)
  | STRING s    -> StStr (char_list_of_string s)
  | TRUE        -> StTru
  | FALSE       -> StFls
  | NULL        -> StNull
  | LEFT_BRACE  -> StLeftBrace
  | RIGHT_BRACE -> StRightBrace
  | LEFT_BRACK  -> StLeftBrack
  | RIGHT_BRACK -> StRightBrack
  | COLON       -> StColon
  | COMMA       -> StComma
  | EOF         -> failwith "Vermillion doesn't treat EOF as a token"

let vtoken_of_mtoken t =
  depTokenOfSimplyTypedToken (simplyTypedTokenOfMenhirToken t)
        *)

(* Convert the tokens that the Menhir lexer generates
   to the tokens that GallStar expects *)
let gtoken_of_token (t : JsonTokenizer.token) : MyJsonParser.D.Defs.token =
  match t with
  | INT i       -> (Int, chars_of_int i)
  | FLOAT f     -> (Float, chars_of_float f)
  | STRING s    -> (Str, chars_of_string s)
  | TRUE        -> (Tru, [])
  | FALSE       -> (Fls, [])
  | NULL        -> (Null, [])
  | LEFT_BRACE  -> (LeftBrace, [])
  | RIGHT_BRACE -> (RightBrace, [])
  | LEFT_BRACK  -> (LeftBrack, [])
  | RIGHT_BRACK -> (RightBrack, [])
  | COLON       -> (Colon, [])
  | COMMA       -> (Comma, [])
  | EOF         -> failwith "GallStar doesn't treat EOF as a token"
                             
let benchmark (f : 'a -> 'b) (x : 'a) : float * 'b =
  let start = Unix.gettimeofday () in
  let res   = f x                  in
  let stop  = Unix.gettimeofday () in
  let time  = stop -. start
  in  (time, res)
       
(* Benchmarking code for the Menhir JSON parser *)
       (*
let run_mparser_trial (fname : string) : float =
  let lexbuf    = Lexing.from_channel (open_in fname) in
  let (time, _) = benchmark (JsonParser.top Mlexer.mread) lexbuf
  in  time

let rec run_n_mparser_trials (n : int) (fname : string) : float list =
  if n <= 0 then 
    [] 
  else
    run_mparser_trial fname :: run_n_mparser_trials (n - 1) fname

let avg_mparser_trials (n : int) (fname : string) : float =
  let times = run_n_mparser_trials n fname
  in  avg_floats times

let benchmark_mparser (n : int) (fnames : string list) : float list =
  List.map (avg_mparser_trials n) fnames
        *)
       
(* Benchmarking code for the GallStar JSON parser *)

let run_gparser_trial (fname : string) : float * float =
  let lexbuf         = Lexing.from_channel (open_in fname) in
  let (lextime, ts) = benchmark (JsonTokenizer.top Lexer.vread) lexbuf in
  let ts'           = map gtoken_of_token ts in
  let (parsetime, v) = benchmark (PG.parseSymbol_opt jsonGrammar (NT Value)) ts' in
  (lextime, parsetime)

(*
let rec run_n_vparser_trials (n : int) (fname : string) : (float * float) list =
  if n <= 0 then 
    [] 
  else
    run_vparser_trial fname :: run_n_vparser_trials (n - 1) fname

let avg_vparser_trials (n : int) (fname : string) : float * float =
  let (lextimes, parsetimes) = List.split (run_n_vparser_trials n fname)
  in  (avg_floats lextimes, avg_floats parsetimes)

let benchmark_vparser (n : int) (fnames : string list) : (float * float) list =
  List.map (avg_vparser_trials n) fnames
        *)


       
(* Code for ensuring that the two parsers produce equivalent semantic values *)
       (*
let rec beq_values (v : Json.value) (jv : VermillionJsonParser.jvalue) : bool =
  match (v, jv) with
  | (`Bool b, JBool b')     -> b = b'

  | (`Float f, JFloat n)    -> (nat_of_float f) = n

  | (`Int i, JInt n)        -> (nat_of_int i) = n

  | (`Null, JNull)          -> true

  | (`String s, JString s') -> char_list_of_string s = s'

  | (`List l, JList l')     -> 
     List.for_all (fun (v, jv) -> beq_values v jv) 
                  (List.combine l l')

  | (`Assoc l, JAssoc l')   -> 
     List.for_all (fun ((s, v), (s', jv)) -> char_list_of_string s = s' && beq_values v jv)
                  (List.combine l l')

  | _ -> false

let mparse (fname : string) : Json.value =
  let lexbuf = Lexing.from_channel (open_in fname) in
  match JsonParser.top Mlexer.mread lexbuf with
  | Some v -> v
  | None   -> failwith "menhir parse failure"

let vparse (fname : string) : VermillionJsonParser.jvalue =
  match PG.parseTableOf jsonGrammar with
  | Inl _   -> failwith "no parse table"
  | Inr tbl -> 
     let lexbuf = Lexing.from_channel (open_in fname)   in
     let ts     = JsonTokenizer.top Vlexer.vread lexbuf in
     let ts'    = List.map vtoken_of_mtoken ts          in
     match PG.parse tbl (NT jsonGrammar.start) ts' with
     | Inl _      -> failwith "vermillion parse failure"
     | Inr (v, _) -> Obj.magic v

let compare_semantic_values (fname : string) : unit =
  let mv = mparse fname in
  let vv = vparse fname in
  if beq_values mv vv then
    print_string "semantic values equal! \n"
  else
    print_string "semantic values not equal :( \n"
        *)

let rec iota n : int list = if n <= 0 then [] else n :: iota (n-1)
    
let main (data_dir : string) (trials_per_file : int) (out_f : string) : unit = 
  (* First, collect the results *)
  let fnames = filenames_in_dir data_dir in
  let lextime_parsetime_pairs =
    map (fun fname ->
               let () = print_string ("file: " ^ fname ^ "\n") in
               let lt_pt_pairs = map (fun i ->
                                        let (lt, pt) = run_gparser_trial fname in
                                        let () = print_string ("trial " ^ string_of_int i ^ "\n") in
                                        let () = print_string (string_of_float pt ^ "s \n") in
                                        (lt, pt))
                                     (iota trials_per_file) in
               let () = print_newline () in
               let (lts, pts)  = List.split lt_pt_pairs in
               (avg_floats lts, avg_floats pts)) fnames in
  let (lextimes, parsetimes) = List.split lextime_parsetime_pairs in
  (* Next, format the results *)
  let json_str =
    Printf.sprintf "{\"file_sizes\" : %s,\n\"lexer_times\" : %s,\n\"parser_times\" : %s}\n"
                    (str_of_int_list   (file_sizes fnames))
                    (str_of_float_list lextimes)
                    (str_of_float_list parsetimes) in
  (* Finally, write the results file *)
  let out_c = open_out out_f in
  output_string out_c json_str

let () = main Sys.argv.(1) (int_of_string Sys.argv.(2)) Sys.argv.(3)
