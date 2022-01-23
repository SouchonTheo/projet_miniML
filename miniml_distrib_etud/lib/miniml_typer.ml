open Miniml_types

(* signature minimale pour définir des variables *)
module type VariableSpec =
  sig
    (* type abstrait des variables      *)
    type t

    (* création d'une variable fraîche  *)
    val fraiche : unit -> t

    (* fonctions de comparaison         *)
    (* permet de définir des conteneurs *)
    (* (hash-table, etc) de variables   *)
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int

    (* fonction d'affichage             *)
    (* on utilise Format.std_formatter  *)
    (* comme premier paramètre          *)
    (* pour la sortie standard          *) 
    val fprintf : Format.formatter -> t -> unit
  end

(* implantation de la spécification     *)
module TypeVariable : VariableSpec =
  struct
    type t = int

    let fraiche =
      let cpt = ref 0 in
      (fun () -> incr cpt; !cpt)

    let compare a b = a - b
    let equal a b = a = b
    let hash a = Hashtbl.hash a

    let fprintf fmt a = Format.fprintf fmt "t{%d}" a
  end


(* ******** à compléter ********* *)



module ModuleVar = TypeVariable
type ensEquation = (ModuleVar.t typ * ModuleVar.t typ) list

type env = ((ident* ModuleVar.t typ) list) * ((ModuleVar.t typ * ModuleVar.t typ) list)


(*Taille de la table arbitraire*)
let nouveau : unit -> env = fun () -> ([],[])

let ajouterCouple : env -> ident -> ModuleVar.t typ -> env = fun (tableType, listeEquation) variable typeVar ->
  ((variable, typeVar)::tableType, listeEquation)

let ajouterEquation : env -> ModuleVar.t typ -> ModuleVar.t typ -> env = fun (tableType,listeEquation) type1 type2 -> 
  (tableType,(type1, type2)::listeEquation)

let obtenirType : env -> ident -> ModuleVar.t typ option = fun (tableType, _) identifiant ->
  List.assq_opt identifiant tableType

let obtenirEquations: env -> ensEquation = fun (_,listeEq) -> listeEq



let rec remplacementNormalisation : ModuleVar.t typ -> ModuleVar.t typ -> ModuleVar.t typ -> ModuleVar.t typ = fun typeInit typeAvant typeApres ->
match typeInit with
  

  |TVar(alpha) -> (match typeAvant with | TVar(beta) when TypeVariable.equal alpha beta -> typeApres | _ -> typeInit)
  |TUnit |TBool |TInt -> typeInit 
  |TList(type1) -> TList(remplacementNormalisation type1 typeAvant typeApres)
  |TProd(type1,type2) -> TProd(remplacementNormalisation type1 typeAvant typeApres, remplacementNormalisation type2 typeAvant typeApres)
  |TFun(type1, type2) -> TFun(remplacementNormalisation type1 typeAvant typeApres, remplacementNormalisation type2 typeAvant typeApres)


let rec remplacementEquations : ensEquation -> ModuleVar.t typ -> ModuleVar.t typ -> ensEquation = fun listeInit typeAvant typeApres -> match listeInit with
  |[] -> []
  |(tau1,tau2)::q -> (remplacementNormalisation tau1 typeAvant typeApres, remplacementNormalisation tau2 typeAvant typeApres)::(remplacementEquations q typeAvant typeApres)

let rec estLibre : ModuleVar.t typ -> ModuleVar.t typ -> bool = fun (TVar(alpha)) type_a_verifier -> match type_a_verifier with
|TInt |TBool | TUnit -> true
|TVar(beta) -> not (TypeVariable.equal alpha beta)
|TFun(tau1,tau2) -> estLibre (TVar(alpha)) tau1 && estLibre (TVar(alpha)) tau2
|TProd(tau1,tau2) -> estLibre (TVar(alpha)) tau1 && estLibre (TVar(alpha)) tau2 
|TList(tau) -> estLibre (TVar(alpha)) tau


let rec inference : env -> expr -> env * ModuleVar.t typ = fun env express -> 
match express with
      (*Si on tombe sur une constante, on ne change pas l'environnement et on renvoie le bon type*)
    | EConstant(constante) -> ( match constante with 
        |CBooleen(_) -> (env, TBool)
        |CEntier(_) -> (env, TInt)
        |CNil -> let alpha = ModuleVar.fraiche () in (env, TList(TVar(alpha)))
        |CUnit -> (env, TUnit)
        )

    | EIdent(identifiant) -> let alpha = ModuleVar.fraiche () in 
        let newEnv = ajouterCouple env identifiant (TVar(alpha)) in 
        (newEnv, TVar(alpha))

    | EProd(expr1, expr2) -> let (newEnv1, tau1) = inference env expr1 in
        let (newEnv2, tau2) = inference newEnv1 expr2 in 
        (newEnv2, TProd(tau1,tau2))

    | ECons(expr1, expr2) -> let (newEnv1, tau1) = inference env expr1 in
        let (newEnv2, tau2) = inference newEnv1 expr2 in 
        let newEnv3 = ajouterEquation newEnv2 tau2 (TList(tau1)) in
        (newEnv3, tau2)

    | EFun(identifiant, expr1) -> let alpha = ModuleVar.fraiche () in 
    let newEnv1 = ajouterCouple env identifiant (TVar(alpha)) in 
        let (newEnv2, tau) = inference newEnv1 expr1 in
        (newEnv2, TFun(TVar(alpha),tau))

    | EIf(exprBool,exprThen,exprElse) -> let (newEnv1, tau) = inference env exprBool in
        let (newEnv2, tau1) = inference newEnv1 exprThen in
        let (newEnv3, tau2) = inference newEnv2 exprElse in
        let newEnv4 = ajouterEquation newEnv3 tau TBool in
        let newEnv5 = ajouterEquation newEnv4 tau1 tau2 in
        (newEnv5, tau1)

    | EApply(exprFun,exprVar) -> let alpha = ModuleVar.fraiche () in 
        let (newEnv1, tau1) = inference env exprFun in
        let (newEnv2, tau2) = inference newEnv1 exprVar in
        let newEnv3 = ajouterEquation newEnv2 tau1 (TFun(tau2, TVar(alpha))) in
        (newEnv3, TVar(alpha)) 

    | EBinop(tokenOP) -> (match tokenOP with
        |CONCAT -> let alpha = ModuleVar.fraiche () in 
            (env, TFun(TList(TVar(alpha)), TFun(TList(TVar(alpha)), TList(TVar(alpha)))))
        |PLUS | MOINS |MULT |DIV -> (env, TFun(TProd(TInt, TInt),TInt))
        |AND | OR -> (env, TFun(TBool, TFun(TBool, TBool)))
        |EQU |NOTEQ |INF |INFEQ |SUP |SUPEQ -> let alpha = ModuleVar.fraiche () in 
            (env, TFun(TVar(alpha), TFun(TVar(alpha), TBool)))
        | _ -> failwith "Problème de Parsing")

    | ELet(identifiant,exprLet, exprIn) -> let (newEnv1, tau1) = inference env exprLet in
        let newEnv2 = ajouterCouple newEnv1 identifiant tau1 in 
        let (newEnv3, tau2) = inference newEnv2 exprIn in
        (newEnv3, tau2)

    | ELetrec(identifiant,exprLet,exprIn) -> let alpha = ModuleVar.fraiche () in 
        let newEnv1 = ajouterCouple env identifiant (TVar(alpha)) in 
        let (newEnv2, tau1) = inference newEnv1 exprLet in
        let (newEnv3, tau2) = inference newEnv2 exprIn in
        let newEnv4 = ajouterEquation newEnv3 (TVar(alpha)) tau1 in
        (newEnv4, tau2)

let rec toString: ModuleVar.t typ -> string = function
|TInt -> "TInt"
|TBool -> "TBool"
|TUnit -> "TUnit"
|TVar(_) -> "TVar(alpha)"
|TFun(tau1,tau2) -> "TFun("^ (toString tau1) ^ "," ^ (toString tau2) ^ ")"
|TProd(tau1,tau2) -> "TProd("^ (toString tau1) ^ ", " ^ (toString tau2) ^ ")"
|TList(tau) -> "TList("^(toString tau)^")"


let rec normalisation : ensEquation -> ModuleVar.t typ -> (string list * ModuleVar.t typ option) = fun liste tau -> 
match liste with
  |[] -> ([],Some(tau))
  |t::q -> (match t with
    |(TInt,TInt) |(TUnit, TUnit) |(TBool, TBool) -> normalisation q tau
    |(TList(tau1), TList(tau2)) -> normalisation ((tau1, tau2)::q) tau
    |(TFun(tau1, tau2), TFun(sigma1, sigma2)) -> normalisation ((tau1, sigma1)::(tau2,sigma2)::q) tau
    |(TProd(tau1, tau2), TProd(sigma1, sigma2)) -> normalisation ((tau1, sigma1)::(tau2,sigma2)::q) tau
    |(TVar(alpha), TVar(rho)) -> if (TypeVariable.equal alpha rho) then normalisation q tau
      else normalisation (remplacementEquations q (TVar(alpha)) (TVar(rho))) (remplacementNormalisation tau (TVar(rho)) (TVar(alpha)))
    |(rho, TVar(alpha)) -> normalisation ((TVar(alpha),rho)::q) tau
    |(TVar(alpha),rho) when estLibre (TVar(alpha)) rho -> normalisation q (remplacementNormalisation tau (TVar(alpha)) rho )
    |(tau1,tau2) -> (["Incompatibilité entre "^(toString tau1)^" et "^(toString tau2)], None)
  )


let typing_expression: expr -> string list * ModuleVar.t typ option = fun expr -> 
  let env = nouveau() in 
  let (envFinal,typeInfere) = inference env expr in
  let listeEquations = obtenirEquations envFinal in 
  normalisation listeEquations typeInfere
