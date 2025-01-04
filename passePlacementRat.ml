(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Type
open Tds
open Ast

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* analyse_placement_instruction : type -> info_ast option -> AstType.instruction -> AstPlacement.instruction *)
(* Paramètre type : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
    Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstPlacement.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (info, e) ->
      begin
       match info_ast_to_info info with
        | InfoVar ( _,_,t,_,_) -> modifier_adresse_variable depl reg info;
          (AstPlacement.Declaration(info,e),getTaille t)
        | _ -> failwith "impossible"
      end
  | AstType.Affectation (a,e) ->
    begin
      (AstPlacement.Affectation(a,e),0)
    end
  | AstType.AffichageInt e ->
    begin
      (AstPlacement.AffichageInt(e),0)
    end
  | AstType.AffichageRat e ->
    begin
      (AstPlacement.AffichageRat(e),0)
    end
  | AstType.AffichageBool e ->
    begin
      (AstPlacement.AffichageBool(e),0)
    end
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
       | InfoFun(_,t,ltp) -> let tr = getTaille t in
        let tp = List.fold_right (fun x resq -> getTaille x + resq) ltp 0 in
        (AstPlacement.Retour(e,tr,tp),0)
       | _ -> failwith "impossible"
     end
  | AstType.Empty -> (AstPlacement.Empty,0)


(* analyse_placement_bloc : type -> info_ast option -> AstType.bloc -> AstPlacement.bloc *)
and analyse_placement_bloc li depl reg = match li with
      | [] -> ([],0)
      | t::q -> let (ni,ti) = analyse_placement_instruction t depl reg in 
        let (nq,tq) = analyse_placement_bloc q (depl+ti) reg in (ni::nq,ti+tq)
  
(* analyse_placement_fonction : type -> AstType.fonction -> AstPlacement.fonction *)
let analyse_placement_fonction (AstType.Fonction(info,lp,li))  =
begin
  let _ = List.fold_right (fun x resq ->
      match info_ast_to_info x with
        |InfoVar ( _,_,t,_,_) -> modifier_adresse_variable (resq - getTaille t) "LB" x; (resq - getTaille t)
        |_ -> failwith "impossible"
    ) (List.rev lp) 0 in
  let nb = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info,lp,nb)
end

(* analyser : AstPlacement.programme -> AstPlacement.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le programme
en un programme de type AstPlacement.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstType.Programme (varGlobales,fonctions,prog)) =
  let nv,top = List.fold_left (fun resq x -> let appel = analyse_placement_instruction x (snd resq) "SB" in
                                              (appel:: (fst resq), snd resq + snd appel)) 
                              ([],0)
                              varGlobales
                               in
  let nf = List.map analyse_placement_fonction fonctions in
  let nb = analyse_placement_bloc prog top "SB" in 
  AstPlacement.Programme((List.map fst nv, top),nf,nb)
