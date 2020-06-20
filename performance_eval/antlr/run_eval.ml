open List

module Yb = Yojson.Basic
module Yu = Yojson.Basic.Util

type coq_string = char list
let coq_string_of (s : string) : coq_string = List.init (String.length s) (String.get s)
                                                 
let costar_token_of (f : char list -> 'a) (json_tok : Yb.t) : 'a * char list =
  let terminal = json_tok |> Yu.member "terminal" |> Yu.to_string |> coq_string_of |> f in
  let literal  = json_tok |> Yu.member "literal"  |> Yu.to_string |> coq_string_of      in
  (terminal, literal)
       
let read_tokens_from_file (t_of_string : coq_string -> 'a) (fname : string) : ('a * coq_string) list =
  let json_tokens = Yb.from_file fname |> Yu.to_list in
  map (costar_token_of t_of_string) json_tokens

    
  
