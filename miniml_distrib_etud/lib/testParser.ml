open Miniml_types
open Miniml_lexer
open Lazyflux

(* les deux types de flux utilisés: le flux à parser et le flux des solutions *)
(* (le fait de passer () à Make assure que ces deux types de flux seront différents et ne pourront donc pas être mélangés involontairement) *)
module Flux = Lazyflux.Make ();;
module Solution = Lazyflux.Make ();;

(* types des parsers généraux *)
type ('a, 'b) result = ('b * 'a Flux.t) Solution.t;;
type ('a, 'b) parser = 'a Flux.t -> ('a, 'b) result;;

(* interface des parsers: combinateurs de parsers et parsers simples *)
module type Parsing =
  sig
    val map : ('b -> 'c) -> ('a, 'b) parser -> ('a, 'c) parser

    val return : 'b -> ('a, 'b) parser

    val ( >>= ) : ('a, 'b) parser -> ('b -> ('a, 'c) parser) -> ('a, 'c) parser

    val zero : ('a, 'b) parser

    val ( ++ ) : ('a, 'b) parser -> ('a, 'b) parser -> ('a, 'b) parser

    val run : ('a, 'b) parser -> 'a Flux.t -> 'b Solution.t

    val pvide : ('a, unit) parser

    val ptest : ('a -> bool) -> ('a, 'a) parser

    val ( *> ) : ('a, 'b) parser -> ('a, 'c) parser -> ('a, 'b * 'c) parser
  end

(* implantation des parsers, comme vu en TD. On utilise les opérations *)
(* du module Flux et du module Solution                                *)
module Parser : Parsing =
  struct
    let map fmap parse f = Solution.map (fun (b, f') -> (fmap b, f')) (parse f);; 

    let return b f = Solution.return (b, f);;

    let (>>=) parse dep_parse = fun f -> Solution.(parse f >>= fun (b, f') -> dep_parse b f');;

    let zero f = Solution.zero;;

    let (++) parse1 parse2 = fun f -> Solution.(parse1 f ++ parse2 f);;

    let run parse f = Solution.(map fst (filter (fun (b, f') -> Flux.uncons f' = None) (parse f)));;

    let pvide f =
      match Flux.uncons f with
      | None   -> Solution.return ((), f)
      | Some _ -> Solution.zero;;

    let ptest p f =
      match Flux.uncons f with
      | None        -> Solution.zero
      | Some (t, q) -> if p t then Solution.return (t, q) else Solution.zero;;

    let ( *> ) parse1 parse2 = fun f ->
      Solution.(parse1 f >>= fun (b, f') -> parse2 f' >>= fun (c, f'') -> return ((b, c), f''));;
  end



(* Fonction de lecture d'un fichier.    *)
(* Produit le flux des lexèmes reconnus *)
let read_miniml_tokens_from_file filename : token Flux.t =
  try
    let chan = open_in filename in
    let buf = Lexing.from_channel chan in
    line_g := 1;
    let next_token () =
      try
        let next = token buf in
        if next = EOF
        then
          begin
            close_in chan;
            None
          end
        else
          Some (next, ())
   with
   | ErreurLex msg ->
      begin
        close_in chan;
        raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
      end in
    Flux.unfold next_token ()
 with
    | Sys_error _ -> raise (ErreurLecture (Format.sprintf "ERREUR : Impossible d'ouvrir le fichier '%s' !" filename))
;;

(* Fonction de lecture d'un buffer.   *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_lexbuf buf : token Flux.t =
  line_g := 1;
  let next_token () =
    try
      let next = token buf in
      if next = EOF
      then
        begin
          None
        end
      else
        Some (next, ())
    with
    | ErreurLex msg ->
       begin
         raise (ErreurLecture (Format.sprintf "ERREUR : ligne %d, lexème '%s' : %s" !line_g (Lexing.lexeme buf) msg))
       end in
  Flux.unfold next_token ()
;;

(* Fonction de lecture d'une chaîne.  *)
(* Similaire à la fonction précédente *)
let read_miniml_tokens_from_string chaine : token Flux.t =
  read_miniml_tokens_from_lexbuf (Lexing.from_string chaine)
;;

(* Fonctions auxiliaires de traitement des lexèmes *)
(* contenant une information: IDENT, BOOL et INT   *)
let isident =
  function IDENT _     -> true
         | _           -> false
let isbool =
  function BOOL _      -> true
         | _           -> false
let isint =
  function INT _       -> true
         | _           -> false

let unident =
  function
  | IDENT id    -> id
  | _           -> assert false
let unbool =
  function
  | BOOL b      -> b
  | _           -> assert false   
let unint =
  function
  | INT i       -> i
  | _           -> assert false


(* Fonctions de parsing de MiniML *)
let accept token : (token -> (token, unit) parser) =
  ptest ((=) token)


let rec parse_expr : (token, expr) parser = fun flux ->
  (
    (accept LET *> parse_liaison *> accept IN *> parse_expr >>=
      fun  ((((), (ident, expr1)), ()), expr2) -> return (ELet (ident, expr1, expr2))
    ) ++
    (accept LET *> accept REC *> parse_liaison *> accept IN *> parse_expr >>=
      fun  (((((), ()), (ident, expr1)), ()), expr2) -> return (ELetrec (ident, expr1, expr2))
    ) ++
    ( accept PARO *> parse_expr *> parse_binop *> parse_expr *> accept PARF >>=
      fun (((((), expr1), binop), expr2), ()) ->  if binop = EBinop (CONS) then 
                                                    return (ECons (expr1, expr2))
                                                  else if binop = EBinop ()
                                                  else if
                                                  EApply ( EApply ( expr1, binop ), expr2))
    ) ++ 
    ( accept PARO *> parse_expr *> accept PARF >>=
      fun (((), expr1),()) -> return expr1
    ) ++ 
    (accept PARO *> parse_expr *> parse_expr *>  accept PARF >>=
      fun ((((), expr1), expr2), ()) -> return (EApply (expr1, expr2))
    ) ++ 
    ( accept IF *> parse_expr *> accept THEN *> parse_expr *>  accept ELSE *> parse_expr >>=
      fun ((((((), expr1), ()), expr2), ()), expr3) -> return (EIf (expr1, expr2, expr3))
    ) ++
    ( accept PARO *> accept FUN *> accept IDENT *> accept TO *> parse_expr *>  accept PARF >>=
      fun ((((((), ()), ident), ()), expr),()) -> return (EFun (ident, expr))
    ) ++
    ( accept IDENT >>=
      fun ident -> return (EIdent ident)
    ) ++
    ( parse_const >>=
      fun constant -> return (EConstant constant)
    )
  ) flux
and parse_liaison = fun flux ->
  ( accept IDENT *> accept EQU *> parse_expr >>=
      fun ((ident,()),expr) -> return (ident, expr)
  ) flux
and parse_binop = fun flux ->
  ( 
    ( parse_arithop >>=
      fun arothop -> return arothop (* Ebinop inclut dans arothop *)
    ) ++
    ( parse_boolop >>=
      fun boolop -> return boolop (* Ebinop inclut dans boolop *)
    ) ++
    ( parse_relop >>=
      fun relop -> return relop (* Ebinop inclut dans relop *)
    ) ++
    ( accept CONCAT >>=
      fun concat -> return (EBinop concat)
    ) ++
    ( accept CONS >>=
      fun cons -> return (EBinop cons)
    )
  ) flux
and parse_arithop = fun flux ->
  (
    ( accept PLUS >>=
      fun  plus -> return (EBinop plus)
    ) ++
    ( accept MOINS >>=
      fun moins -> return (EBinop moins)
    ) ++
    ( accept MULT >>=
      fun  mult -> return (EBinop mult)
    ) ++
    ( accept DIV >>=
      fun  div -> return (EBinop div)
    ) 
  ) flux
and parse_boolop = fun flux ->
  (
    ( accept AND >>=
      fun  ad -> return (EBinop ad)
    ) ++
    ( accept OR >>=
      fun ou -> return (EBinop ou)
    ) 
  ) flux
and parse_relop = fun flux ->
  (
    ( accept EQU >>=
      fun  equ -> return (EBinop equ)
    ) ++
    ( accept NOTEQ >>=
      fun  noteq -> return (EBinop noteq)
    ) ++
    ( accept INFEQ >>=
      fun  infeq -> return (EBinop infeq)
    ) ++
    ( accept INF >>=
      fun  inf -> return (EBinop inf)
    ) ++
    ( accept SUPEQ >>=
      fun  supeq -> return (EBinop supeq)
    ) ++
    ( accept SUP >>=
      fun sup -> return (EBinop sup)
    ) 
  ) flux
and parse_const = fun flux ->
  (
    ( accept INT >>=
      fun entier -> return (CEntier entier)
    ) ++
    ( accept BOOL >>=
      fun bool -> return (CBooleen bool)
    ) ++
    ( accept CROO  *> accept CROF >>=
      fun _ -> return CNil
    ) ++
    ( accept PARO  *> accept PARF >>=
      fun _ -> return CUnit
    ) 
  ) flux
let parser flux : (token Flux.t -> ('a, 'b) result)
