(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Type
open Tds
open Ast

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* analyse_placement_instruction : AstType.instruction -> int -> string -> AstPlacement.instruction * int *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : le deplacement en cours *)
(* Paramètre reg : le registre en cours *)
(* Transforme l'instruction en une instruction de type AstPlacement.instruction *)
let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (info, e) ->
      begin
       match info_ast_to_info info with
        | InfoVar ( false,_,t,_,_) -> modifier_adresse_variable depl reg info;
          (AstPlacement.Declaration(info,e), getTaille t)
        | InfoVar ( true,_,_,_,_) -> (*Une variable statique locale à une fonction est déjà stockée ailleurs, elle ne prend pas de place dans la pile*)
          (AstPlacement.Declaration(info,e), 0)
        | _ -> failwith "impossible"
      end
  | AstType.Affectation (a,e) -> (AstPlacement.Affectation(a,e),0)

  | AstType.AffichageInt e -> (AstPlacement.AffichageInt(e),0)

  | AstType.AffichageRat e -> (AstPlacement.AffichageRat(e),0)

  | AstType.AffichageBool e -> (AstPlacement.AffichageBool(e),0)

  | AstType.Conditionnelle (c,t,e) ->
      let nt = analyse_placement_bloc t depl reg in
      let ne = analyse_placement_bloc e depl reg in
      (AstPlacement.Conditionnelle(c,nt,ne),0)

  | AstType.TantQue (c,b) ->
    let nb = analyse_placement_bloc b depl reg in
    (AstPlacement.TantQue(c,nb),0)

  | AstType.Retour (e,ia) -> 
    begin
      match info_ast_to_info ia with
       | InfoFun(_,t,ltp,_) -> let tr = getTaille t in
        let tp = List.fold_right (fun x resq -> getTaille x + resq) ltp 0 in
        (AstPlacement.Retour(e,tr,tp),0)
       | _ -> failwith "impossible"
     end
  | AstType.Empty -> (AstPlacement.Empty,0)


(* analyse_placement_bloc : AstType.bloc -> int -> string -> AstPlacement.bloc * int *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre depl : le deplacement en cours *)
(* Paramètre reg : le registre en cours *)
(* Transforme le bloc en un bloc de type AstPlacement.bloc *)
and analyse_placement_bloc li depl reg = match li with
      | [] -> ([],0)
      | t::q -> let (ni,ti) = analyse_placement_instruction t depl reg in 
        let (nq,tq) = analyse_placement_bloc q (depl+ti) reg in (ni::nq,ti+tq)
  
(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction *)
(* Transforme la fonction en une fonction de type AstPlacement.fonction *)
let analyse_placement_fonction (AstType.Fonction(info,lp,li))  =
begin
  (* Cette ligne ne renvoie rien d'intéressant mais on a quand même besoin d'un fold_right pour les appels récursifs *)
  (* Placement des arguments de la fonction à des adresses négatives de LB *)
  let _ = List.fold_right (fun x resq ->
      match info_ast_to_info x with
        | InfoVar ( _,_,t,_,_) -> modifier_adresse_variable (resq - getTaille t) "LB" x; (resq - getTaille t)
        | _ -> failwith "impossible"
    ) (List.rev (List.map fst lp)) 0 in

  (* Placement des variables du bloc de la fonction*)
  let nb = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info,lp,nb)
end

(* analyse_placement_statique_fonction : AstType.fonction -> int -> AstType.fonction * int *)
(* Paramètre : fonction à analyser *)
(* Paramètre top : haut de la pile *)
(* Place uniquement les variables statiques locales *)
let rec analyse_placement_statique_fonction (AstType.Fonction(info,lp,li)) top =
  let nli,ntop = analyse_placement_statique_bloc li top "SB" in
  AstType.Fonction(info,lp,nli),ntop

(* analyse_placement_statique_bloc : AstType.bloc -> int -> string -> AstType.bloc * int *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre depl : le deplacement en cours *)
(* Paramètre reg : le registre en cours *)
(* Place uniquement les variables statiques locales *)
and analyse_placement_statique_bloc li depl reg = match li with
  | [] -> ([],0)
  | t::q -> let (ni,ti) = analyse_placement_statique_instruction t depl reg in 
    let (nq,tq) = analyse_placement_statique_bloc q (depl+ti) reg in (ni::nq,ti+tq)

(* analyse_placement_instruction : AstType.instruction -> int -> string -> AstType.instruction * int *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : le deplacement en cours *)
(* Paramètre reg : le registre en cours *)
(* Place uniquement les variables statiques locales *)
and analyse_placement_statique_instruction i depl reg =
  match i with
  | AstType.Declaration (info, e) ->
      begin
       match info_ast_to_info info with
        | InfoVar ( false,_,_,_,_) -> (i,0)
        | InfoVar ( true,_,_,_,_) -> modifier_adresse_variable depl reg info; (AstType.Declaration(info,e),1)
        | _ -> failwith "impossible"
      end
  | _ -> (i,0)


(* analyser : AstType.programme -> AstPlacement.programme *)
(* Paramètre : le programme à analyser *)
(* Transforme le programme en un programme de type AstPlacement.programme *)
let analyser (AstType.Programme (varGlobales,fonctions,prog)) =
  (* Placement des variables globales *)
  let nv,top = List.fold_left (fun resq x -> let appel = analyse_placement_instruction x (snd resq) "SB" in
                                              (appel:: (fst resq), snd resq + snd appel)) 
                              ([],0)
                              varGlobales
  in
  (* Placement des variables statiques locales *)
  let nf1, ntop = List.fold_right (fun f resq -> let nf,ntop = analyse_placement_statique_fonction f (snd resq) in (nf::(fst resq), ntop + (snd resq))) fonctions ([],top) in
  
  let nf2 = List.map analyse_placement_fonction nf1 in
  let nprog = analyse_placement_bloc prog ntop "SB" in 
  AstPlacement.Programme((List.map fst nv, ntop),nf2,nprog,ntop - top)
