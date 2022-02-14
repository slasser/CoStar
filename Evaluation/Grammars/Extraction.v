Require Import ExtrOcamlBasic.
(*Require Import ExtrOcamlNatInt.*)
(*Require Import ExtrOcamlZInt.*)
Require Import ExtrOcamlString.
Require Import CoStar.Evaluation.Grammars.PPM.
Require Import CoStar.Evaluation.Grammars.JSON.
Require Import CoStar.Evaluation.Grammars.Newick.
Require Import CoStar.Evaluation.Grammars.XML.

Extraction Blacklist List String.

Separate Extraction
         lex_ppm
         parse_ppm
         show_ppm_result
         lex_json
         parse_json
         show_json_result
         lex_newick
         parse_newick
         show_newick_result
         lex_xml
         parse_xml
         show_xml_result.
