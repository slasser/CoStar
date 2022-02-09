open JSON
open PPM
module Yb = Yojson.Basic
module Yu = Yojson.Basic.Util
(***********************************************************************)
(* Utilities for reading JSON representations of tokenized input       *)
(***********************************************************************)
type coq_string = char list
let coqstr_of_str (s : string) : coq_string = List.init (String.length s) (String.get s)
let str_of_coqstr (c : coq_string) : string = String.concat "" (List.map Char.escaped c)

let chars_from_file (fname : string) : coq_string =
    let ic = open_in fname in
    let cs = really_input_string ic (in_channel_length ic) |> coqstr_of_str in
    let () = close_in ic in
    cs
(*                                                 
let costar_token_of (f : char list -> 'a) (json_tok : Yb.t) : 'a * char list =
  let terminal = json_tok |> Yu.member "terminal" |> Yu.to_string |> coqstr_of_str |> f in
  let literal  = json_tok |> Yu.member "literal"  |> Yu.to_string |> coqstr_of_str      in
  (terminal, literal)
       
let read_tokens_from_file (t_of_string : coq_string -> 'a) (fname : string) : ('a * coq_string) list =
  let json_tokens = Yb.from_file fname |> Yu.to_list in
  List.map (costar_token_of t_of_string) json_tokens
 *)
(***********************************************************************)
(* Utilities for writing JSON representations of benchmark results     *)
(***********************************************************************)
type test_result =
  { filename    : string
  ; num_tokens  : int
  ; parse_times : float list}

let mk_test_result (fn : string) (nt : int) (pts : float list) : test_result =
  {filename = fn; num_tokens = nt; parse_times = pts}

(* Int.compare causes an "unbound value" error *)
let cmp_test_results (tr : test_result) (tr' : test_result) : int =
  let open Int in compare tr.num_tokens tr'.num_tokens

let json_of_test_result (tr : test_result) : Yb.t =
  match tr with
  | {filename = fn; num_tokens = nt; parse_times = pts} ->
     let json_floats = List.map (fun pt -> `Float pt) pts
     in  `Assoc [("filename", `String fn); ("num_tokens", `Int nt); ("execution_times", `List json_floats)]

let json_of_test_results (trs : test_result list) : Yb.t =
  `List (List.map json_of_test_result (List.sort cmp_test_results trs))

let write_test_results (trs : test_result list) (fname : string) : unit =
  Yb.to_file fname (json_of_test_results trs)
(***********************************************************************)
(* Code for benchmarking CoStar parsers and printing/recording results *)
(***********************************************************************)
let benchmark (f : 'a -> 'b) (x : 'a) : float * 'b =
  let start = Unix.gettimeofday () in
  let res   = f x                  in
  let stop  = Unix.gettimeofday () in
  let time  = stop -. start
  in  (time, res)

let print_result (fname : string) (res : coq_string) =
  Printf.printf "***\nFile   : %s\nResult : %s \n%!" fname (str_of_coqstr res)

let benchmark_lexer_and_parser_on_dataset lex parse show_result data_dir num_trials : test_result list =
  let files       = Sys.readdir data_dir    in
  let total_files = Array.length files      in
  let results     = ref []                  in
  for i = 0 to Array.length files - 1 do
    let ()          = Printf.printf "file #%d of %d\n" (i + 1) total_files    in
    let fname       = files.(i)                                               in
    let input_str   = chars_from_file (data_dir ^ "/" ^ fname)                in
    let (ts_o, rem) = lex input_str in
    match ts_o with
    | None -> ()
    | Some ts ->
       let parse_times = ref []                                               in
       (for j = 0 to num_trials - 1 do
          let (time, res) = benchmark parse ts in
          if j = 0 then print_result fname (show_result res) else ();
          parse_times := time :: !parse_times
        done);
       results := (mk_test_result fname (List.length ts) !parse_times) :: !results
  done;
  !results
       
let main () =
  let lang       = Sys.argv.(1) in
  let data_dir   = Sys.argv.(2) in
  let num_trials = int_of_string (Sys.argv.(3)) in
  let outfile    = Sys.argv.(4) in
  let results    =
    (match lang with
     | "-ppm"  -> benchmark_lexer_and_parser_on_dataset lex_ppm parse_ppm show_ppm_result data_dir num_trials
     | "-json" -> benchmark_lexer_and_parser_on_dataset lex_json parse_json show_json_result data_dir num_trials
     | _ -> failwith ("unrecognized lang argument: " ^ lang))
  in  write_test_results results outfile

let () = main ()
