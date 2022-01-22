Require Extraction.
(* For proper string extraction*)
From Coq Require Import extraction.ExtrOcamlNativeString.

Require Import Theory.Stlc.

Extraction "extr.ml" type_of.
