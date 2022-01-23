(* ouverture de la "library" definie dans lib/dune *)
open Miniml

(* ouverture de modules de la library Miniml *)
open Miniml_lexer
open Miniml_parser
open Miniml_typer
open TestParser
open Miniml_printer

(* ******** à compléter ********* *)
       
let lexer_parser_typer : string -> unit = fun name -> 
  let (messages, optionType) = typing_expression  (get_expr name) in
    match optionType with
      |None -> (match messages with
        | [] -> Format.fprintf Format.std_formatter "@[%s@]@." "Problème non résolu"
        | t::_ -> Format.fprintf Format.std_formatter "@[%s@]@." t
        )
      |Some(typeExpr) -> print_typ TypeVariable.fprintf Format.std_formatter typeExpr;;



lexer_parser_typer "/media/basile/DATA/Cours/PF/projet_ProgFonc/miniml_distrib_etud/lib/testParser.ml";;