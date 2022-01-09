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
    (*Le type des variables*)
    type var
    (*Le type des équations (type1 ≡ type2)*)
    type eqn
    (*Créer l'environement initial*)
    val nouveau: unit -> env

    (*Ajouter un couple (variable:type) à l'environnement*)
    val ajouterCouple: env -> var -> typ -> env

    (*Ajouter une equation (type1 ≡ type2) à l'environnement*)
    val ajouterEquation: env -> typEnv -> typEnv -> env

    (*Obtenir le type associé à une variable si elle est présente dans l'environnement*)
    val obtenirType: env -> var -> typ option

end