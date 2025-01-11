(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Type
open Tds
open Exceptions
open Ast

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme


(* analyse_tds_affectable : tds -> AstSyntax.affectable -> AstTds.affectable *)
(* Paramètre a : l'affectable à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'affectable
en un affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_affectable a  = 
  match a with
  | AstTds.Ident info -> begin match info_ast_to_info info with
    | InfoVar (_,_,t,_,_) -> (AstType.Ident info, t)
    | InfoConst(_,_) -> (AstType.Ident info, Int)
    | _ -> failwith "impossible"
    end
  | AstTds.Deref a2 -> match analyse_type_affectable a2 with
    | (naff, Pointeur(t)) -> (AstType.Deref naff, t)
    | (_,t)-> raise (TypePointeurAttendu(t))


(* analyse_type_expression : type -> AstTds.expression -> AstType.expression *)
(* Paramètre type : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)

let rec analyse_type_expression e =
  match e with
    | AstTds.AppelFonction(info,le) ->
      begin
        match info_ast_to_info info with
          | InfoFun(_,tr,tp,nb) ->
            let l = List.map analyse_type_expression le in

            (*tp est dans le mauvais sens, on le retourne*)
            let tp2 = List.rev tp in

            let np = List.map fst l in
            let ntp = List.map snd l in

            let rec n_premiers_elements n lst =
              match lst, n with
              | [], _ -> []
              | _, n when n <= 0 -> []
              | x :: xs, n -> x :: n_premiers_elements (n - 1) xs
            in 

            if est_compatible_list (n_premiers_elements (List.length ntp) tp2) ntp && nb <= List.length le then
              (AstType.AppelFonction(info,np),tr)
            else raise (TypesParametresInattendus(ntp,tp2))
          | _ -> failwith "impossible"
      end 
    | AstTds.Affectable a -> let (a, t) = (analyse_type_affectable a) in
      (AstType.Affectable a, t)
    
    | AstTds.Adresse info -> begin match info_ast_to_info info with
      | InfoVar (_,_,t,_,_) -> (AstType.Adresse info, Pointeur(t))
      | _ -> failwith "impossible"
    end
    | AstTds.Null -> (AstType.Null, Pointeur(Undefined))

    | AstTds.New t -> (AstType.New t, Pointeur(t))

    | AstTds.Binaire (b,e1,e2) -> let (ne1,te1) = analyse_type_expression e1 in
      let (ne2,te2) = analyse_type_expression e2 in
      begin
        match te1,b,te2 with
        | Int,Plus,Int -> (AstType.Binaire(PlusInt,ne1,ne2),Int)
        | Int,Fraction,Int -> (AstType.Binaire(Fraction,ne1,ne2),Rat)
        | Rat,Plus,Rat -> (AstType.Binaire(PlusRat,ne1,ne2),Rat)
        | Int,Mult,Int -> (AstType.Binaire(MultInt,ne1,ne2),Int)
        | Rat,Mult,Rat -> (AstType.Binaire(MultRat,ne1,ne2),Rat)
        | Int,Equ,Int -> (AstType.Binaire(EquInt,ne1,ne2),Bool)
        | Bool,Equ,Bool -> (AstType.Binaire(EquBool,ne1,ne2),Bool)
        | Int,Inf,Int -> (AstType.Binaire(Inf,ne1,ne2),Bool)
        | _ -> raise (TypeBinaireInattendu(b,te1,te2))
      end

    | AstTds.Unaire (op,e) -> 
      let (ne,t) = analyse_type_expression e in
      if (est_compatible t Rat) then
        begin
          match op with
          | Numerateur -> (AstType.Unaire(Numerateur,ne),Int)
          | Denominateur -> (AstType.Unaire(Denominateur,ne),Int)
        end
      else
        raise (TypeInattendu(t,Rat))
    | AstTds.Booleen b -> (AstType.Booleen b,Bool)
    | AstTds.Entier i -> (AstType.Entier i,Int)
  


(* analyse_type_instruction : type -> info_ast option -> AstTds.instruction -> AstType.instruction *)
(* Paramètre type : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
    Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_instruction i =
  match i with
  | AstTds.Declaration (t, info, e) ->
      let (ne,te) = analyse_type_expression e in
        if est_compatible t te then
          begin
          modifier_type_variable t info;
          AstType.Declaration(info,ne)
          end
        else raise (TypeInattendu(te,t))
  | AstTds.Affectation (a,e) ->
    let (na,ta) = analyse_type_affectable a in
    let (ne,te) = analyse_type_expression e in
      if est_compatible ta te then
          AstType.Affectation(na,ne)
        else raise (TypeInattendu(te,ta))
  | AstTds.Affichage e ->
    let (ne,te) = analyse_type_expression e in
    begin
      match te with
        | Int -> AstType.AffichageInt(ne)
        | Bool -> AstType.AffichageBool(ne)
        | Rat -> AstType.AffichageRat(ne)
        | Pointeur _ -> AstType.AffichageInt(ne)
        | _ -> failwith "affichage non implémenté"
    end

  | AstTds.Conditionnelle (c,t,e) ->
      let (nc,tc) = analyse_type_expression c in
        if tc = Bool then 
          let nt = analyse_type_bloc t in
          let ne = analyse_type_bloc e in
          AstType.Conditionnelle(nc,nt,ne)
        else
          raise (TypeInattendu(tc,Bool))

  | AstTds.TantQue (c,b) ->
    let (nc,tc) = analyse_type_expression c in
    if tc = Bool then
      let nb = analyse_type_bloc b in
      AstType.TantQue(nc,nb)
    else raise (TypeInattendu(tc,Bool))

  | AstTds.Retour (e,ia) ->
      begin
      let ne,te = analyse_type_expression e in
        match info_ast_to_info ia with
          | InfoFun(_,t,_,_) -> if est_compatible t te then
            AstType.Retour (ne,ia)
            else raise (TypeInattendu(te,t))
          | _ -> failwith "impossible"
      end
  | AstTds.Empty -> AstType.Empty


(* analyse_type_bloc : type -> info_ast option -> AstTds.bloc -> AstType.bloc *)
and analyse_type_bloc li =
  List.map analyse_type_instruction li
  

(* analyse_type_fonction : type -> AstTds.fonction -> AstType.fonction *)
let analyse_type_fonction (AstTds.Fonction(t,info,lp,li))  =
begin
  modifier_type_fonction t (List.map (fun (t,_,_) -> t) lp) info;
  let info_types = List.map ( fun (t,i,v) ->
    modifier_type_variable t i; match v with
    | None -> (i,None)
    | Some e -> let (ne,te) = analyse_type_expression e in
      if est_compatible te t then
        (i,Some ne)
      else
        raise (TypeInattendu(te,t))
  ) lp in
  AstType.Fonction(info,info_types, analyse_type_bloc li)
end

(* analyser : AstType.programme -> AstType.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le programme
en un programme de type AstType.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (varGlobales,fonctions,prog)) =
  let nv = List.map analyse_type_instruction varGlobales in
  let nf = List.map analyse_type_fonction fonctions in
  let nb = analyse_type_bloc prog in 
  AstType.Programme(nv,nf,nb)
