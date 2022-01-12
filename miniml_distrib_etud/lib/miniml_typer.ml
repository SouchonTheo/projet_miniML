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

(*Signature pour définir l'environnement*)
module type EnvironnementSpec =
  sig
    (*Le type de l'environnement*)
    type env

    (*Le type de l'ensemble des equations*)
    type ensEquation
    (*Le module des variables*)
    module ModuleVar : VariableSpec
    (*Créer l'environement initial*)
    val nouveau: unit -> env

    (*Ajouter un couple (variable:type) à l'environnement*)
    val ajouterCouple: env -> ident -> ModuleVar.t typ -> env

    (*Ajouter une equation (type1 ≡ type2) à l'environnement*)
    val ajouterEquation: env -> ModuleVar.t typ -> ModuleVar.t typ -> env

    (*Obtenir le type associé à une variable si elle est présente dans l'environnement*)
    val obtenirType: env -> ident -> ModuleVar.t typ option

    val obtenirEquations:env-> ensEquation

end

module TypeEnvironnement : EnvironnementSpec = 
  struct
      module ModuleVar = TypeVariable
      type ensEquation = (ModuleVar.t typ * ModuleVar.t typ) list

      type env = ((ident, ModuleVar.t typ) Hashtbl.t) * ((ModuleVar.t typ * ModuleVar.t typ) list)

      (*Taille de la table arbitraire*)
      let nouveau : unit -> env = fun () -> (Hashtbl.create 128,[])

      let ajouterCouple : env -> ident -> ModuleVar.t typ -> env = fun (tableType, listeEquation) variable typeVar ->
        Hashtbl.add tableType variable typeVar; 
        let newTable = Hashtbl.copy tableType
          in (newTable, listeEquation)

      let ajouterEquation : env -> ModuleVar.t typ -> ModuleVar.t typ -> env = fun (tableType,listeEquation) type1 type2 -> 
        (tableType,(type1, type2)::listeEquation)

      let obtenirType : env -> ident -> ModuleVar.t typ option = fun (tableType, _) identifiant ->
        Hashtbl.find_opt tableType identifiant
      
        let obtenirEquations: env -> ensEquation = fun (_,listeEq) -> listeEq

end

(*Signature du typer*)
module type TyperSpec =
  sig
    (*Le type des expression à typer*)
    type expression

    (*Le module de l'environnement*)
    module ModuleEnv : EnvironnementSpec

    (*Le type des expressions*)
    type typeExpr

    type ensEquation

    (*Fonction qui remplace dans le premier type de deuxième parle troisième et renvoie le résultat*)
    val remplacementNormalisation : typeExpr -> typeExpr -> typeExpr -> typeExpr

    val remplacementEquations : ensEquation -> typeExpr -> typeExpr -> ensEquation

    (*Fonction d'inférence des types, prend un environnement initial et une expression, et renvoie l'environnement et le type final après inférence*)
    val inference : ModuleEnv.env -> expression -> ModuleEnv.env * typeExpr

    (*Fonction de normalisation des equations de type. Renvoie le type final ainsi que une liste des logs à afficher.*)
    val normalisation : ensEquation -> typeExpr -> (string list * typeExpr option)
end

(*Typer sans polymorphisme*)
module TypeTyper : TyperSpec =
  struct
    type expression = expr

    module ModuleEnv = TypeEnvironnement

    type typeExpr = ModuleEnv.ModuleVar.t typ

    type ensEquation = (ModuleEnv.ModuleVar.t typ * ModuleEnv.ModuleVar.t typ) list

    let rec remplacementNormalisation : typeExpr -> typeExpr -> typeExpr -> typeExpr = fun typeInit typeAvant typeAprès ->
      match typeInit with
        |typeVU when typeVU = typeAvant -> typeAprès
        |TUnit |TBool |TInt |TVar(_) -> typeInit
        |TList(type1) -> TList(remplacementNormalisation type1 typeAvant typeAprès)
        |TProd(type1,type2) -> TProd(remplacementNormalisation type1 typeAvant typeAprès, remplacementNormalisation type2 typeAvant typeAprès)
        |TFun(type1, type2) -> TFun(remplacementNormalisation type1 typeAvant typeAprès, remplacementNormalisation type2 typeAvant typeAprès)


      let rec remplacementEquations : ensEquation -> typeExpr -> typeExpr -> ensEquation = fun listeInit typeAvant typeAprès -> match listeInit with
        |[] -> []
        |(tau1,tau2)::q -> (remplacementNormalisation tau1 typeAvant typeAprès, remplacementNormalisation tau2 typeAvant typeAprès)::(remplacementEquations q typeAvant typeAprès)

    let rec inference : ModuleEnv.env -> expression -> ModuleEnv.env * typeExpr = fun env express -> 
      match express with
            (*Si on tombe sur une constante, on ne change pas l'environnement et on renvoie le bon type*)
          | EConstant(constante) -> ( match constante with 
              |CBooleen(_) -> (env, TBool)
              |CEntier(_) -> (env, TInt)
              |CNil -> let alpha = ModuleEnv.ModuleVar.fraiche () in (env, TList(TVar(alpha)))
              |CUnit -> (env, TUnit)
              )

          | EIdent(identifiant) -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
              let newEnv = ModuleEnv.ajouterCouple env identifiant (TVar(alpha)) in 
              (newEnv, TVar(alpha))

          | EProd(expr1, expr2) -> let (newEnv1, tau1) = inference env expr1 in
              let (newEnv2, tau2) = inference newEnv1 expr2 in 
              (newEnv2, TProd(tau1,tau2))

          | ECons(expr1, expr2) -> let (newEnv1, tau1) = inference env expr1 in
              let (newEnv2, tau2) = inference newEnv1 expr2 in 
              let newEnv3 = ModuleEnv.ajouterEquation newEnv2 tau2 (TList(tau1)) in
              (newEnv3, tau2)

          | EFun(identifiant, expr1) -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
          let newEnv1 = ModuleEnv.ajouterCouple env identifiant (TVar(alpha)) in 
              let (newEnv2, tau) = inference newEnv1 expr1 in
              (newEnv2, TFun(TVar(alpha),tau))

          | EIf(exprBool,exprThen,exprElse) -> let (newEnv1, tau) = inference env exprBool in
              let (newEnv2, tau1) = inference newEnv1 exprThen in
              let (newEnv3, tau2) = inference newEnv2 exprElse in
              let newEnv4 = ModuleEnv.ajouterEquation newEnv3 tau TBool in
              let newEnv5 = ModuleEnv.ajouterEquation newEnv4 tau1 tau2 in
              (newEnv5, tau1)

          | EApply(exprFun,exprVar) -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
              let (newEnv1, tau1) = inference env exprFun in
              let (newEnv2, tau2) = inference newEnv1 exprVar in
              let newEnv3 = ModuleEnv.ajouterEquation newEnv2 tau1 (TFun(tau2, TVar(alpha))) in
              (newEnv3, TVar(alpha)) 

          | EBinop(tokenOP) -> (match tokenOP with
              |CONCAT -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
                  (env, TFun(TList(TVar(alpha)), TFun(TList(TVar(alpha)), TList(TVar(alpha)))))
              |PLUS | MOINS |MULT |DIV -> (env, TFun(TInt, TFun(TInt, TInt)))
              |AND | OR -> (env, TFun(TBool, TFun(TBool, TBool)))
              |EQU |NOTEQ |INF |INFEQ |SUP |SUPEQ -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
                  (env, TFun(TVar(alpha), TFun(TVar(alpha), TBool)))
              | _ -> failwith "Problème de Parsing")

          | ELet(identifiant,exprLet, exprIn) -> let (newEnv1, tau1) = inference env exprLet in
              let newEnv2 = ModuleEnv.ajouterCouple newEnv1 identifiant tau1 in 
              let (newEnv3, tau2) = inference newEnv2 exprIn in
              (newEnv3, tau2)

          | ELetrec(identifiant,exprLet,exprIn) -> let alpha = ModuleEnv.ModuleVar.fraiche () in 
              let newEnv1 = ModuleEnv.ajouterCouple env identifiant (TVar(alpha)) in 
              let (newEnv2, tau1) = inference newEnv1 exprLet in
              let (newEnv3, tau2) = inference newEnv2 exprIn in
              let newEnv4 = ModuleEnv.ajouterEquation newEnv3 (TVar(alpha)) tau1 in
              (newEnv4, tau2)

    let rec toString: typeExpr -> string = function
      |TInt -> "TInt"
      |TBool -> "TBool"
      |TUnit -> "TUnit"
      |TVar(_) -> "TVar(alpha)"
      |TFun(tau1,tau2) -> "TFun("^ (toString tau1) ^ "," ^ (toString tau2) ^ ")"
      |TProd(tau1,tau2) -> "TProd("^ (toString tau1) ^ ", " ^ (toString tau2) ^ ")"
      |TList(tau) -> "TList("^(toString tau)^")"
    let rec normalisation : ensEquation -> typeExpr -> (string list *typeExpr option) = fun liste tau -> 
      match liste with
        |[] -> ([],Some(tau))
        |t::q -> (match t with
          |(TInt,TInt) |(TUnit, TUnit) |(TBool, TBool) -> normalisation q tau
          |(TList(tau1), TList(tau2)) -> normalisation ((tau1, tau2)::q) tau
          |(TFun(tau1, tau2), TFun(sigma1, sigma2)) -> normalisation ((tau1, sigma1)::(tau2,sigma2)::q) tau
          |(TProd(tau1, tau2), TProd(sigma1, sigma2)) -> normalisation ((tau1, sigma1)::(tau2,sigma2)::q) tau
          |(TVar(alpha), TVar(rho)) -> if alpha = rho then normalisation q tau
            else normalisation (remplacementEquations q (TVar(alpha)) (TVar(rho))) (remplacementNormalisation tau (TVar(rho)) (TVar(alpha)))
          |(TVar(alpha),rho) -> normalisation ((rho, TVar(alpha))::q) (remplacementNormalisation tau rho (TVar(alpha)))
          |(tau1,tau2) -> (["Incompatibilité entre "^(toString tau1)^" et "^(toString tau2)], None)
        )

end