Require Import GallStar.Defs.
Require Import GallStar.Parser.


Lemma multistep_complete :
  forall g st a v,
    unique_gamma_derivation g ys w v -> multistep g st a = Accept v.

hd : gamma_derivation g ys w v
  hu : forall v' : forest, gamma_derivation g ys w v' -> v = v'
  ============================
  multistep g (mkInitState g ys w)
    (Lex.lex_nat_triple_wf (meas g (mkInitState g ys w))) = 
  Accept v

Theorem parser_complete :
  forall g ys w v,
    unique_gamma_derivation g ys w v -> parse g ys w = Accept v.
Proof.
  intros g ys w v [hd hu].
  unfold parse.
  