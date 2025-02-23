(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme

(* analyse_tds_affectable : tds -> AstSyntax.affectable -> Bool -> AstTds.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre a : l'affectable à analyser *)
(* Paramètre modif : booléen vrai si on est à gauche d'une affectation *)
(* Vérifie la bonne utilisation des identifiants et transforme l'affectable
en un affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_affectable tds a modif = 
  match a with
  | AstSyntax.Ident n ->
    begin match chercherGlobalement tds n with
    | None -> raise (IdentifiantNonDeclare n)
    | Some info -> begin match info_ast_to_info info with
      | InfoVar _ -> AstTds.Ident(info)
      | InfoConst(_,_) -> (* On ne peut pas modifier la valeur d'une constante *)
        if modif then raise (MauvaiseUtilisationIdentifiant n)
        else AstTds.Ident(info)
      | InfoFun _ -> (* On ne peut pas modifier la valeur d'une fonction *)
        raise (MauvaiseUtilisationIdentifiant n) end end
  | AstSyntax.Deref a2 -> AstTds.Deref (analyse_tds_affectable tds a2 modif)



(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e =
  match e with
    | AstSyntax.AppelFonction(id,le) -> 
      begin match chercherGlobalement tds id with
      | None -> raise (IdentifiantNonDeclare id)
      | Some info -> 
        begin match info_ast_to_info info with
        | InfoFun _ -> AstTds.AppelFonction (info, List.map (analyse_tds_expression tds) le)
        | _ -> raise (MauvaiseUtilisationIdentifiant id) 
        end 
      end

    | AstSyntax.Affectable a -> AstTds.Affectable (analyse_tds_affectable tds a false)

    | AstSyntax.Adresse n -> 
      begin match chercherGlobalement tds n with
      | None -> raise (IdentifiantNonDeclare n)
      | Some info -> 
        begin match info_ast_to_info info with
        | InfoVar _ -> AstTds.Adresse info
        | _ -> raise (MauvaiseUtilisationIdentifiant n)
        end
      end

    | AstSyntax.Null -> AstTds.Null

    | AstSyntax.New t -> AstTds.New t

    | AstSyntax.Binaire (b,e1,e2) -> AstTds.Binaire (b,
                                            analyse_tds_expression tds e1,
                                            analyse_tds_expression tds e2)
    | AstSyntax.Unaire (op,e1) -> AstTds.Unaire (op, analyse_tds_expression tds e1)
    | AstSyntax.Booleen b -> AstTds.Booleen b
    | AstSyntax.Entier i -> AstTds.Entier i
  


(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia i =
  match i with
  | AstSyntax.Declaration (b, t, n, e) ->
      begin
        match chercherLocalement tds n with
        | None ->
            (* L'identifiant n'est pas trouvé dans la tds locale,
            il n'a donc pas été déclaré dans le bloc courant *)
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds e in
            (* Création de l'information associée à l'identfiant *)
            let info = InfoVar (b,n,Undefined, 0, "") in
            (* Création du pointeur sur l'information *)
            let ia = info_to_info_ast info in
            (* Ajout de l'information (pointeur) dans la tds *)
            ajouter tds n ia;
            (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information
            et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Declaration (t, ia, ne)
        | Some _ ->
            (* L'identifiant est trouvé dans la tds locale,
            il a donc déjà été déclaré dans le bloc courant *)
            raise (DoubleDeclaration n)
      end
  | AstSyntax.Affectation (a,e) -> let ne = analyse_tds_expression tds e in
      AstTds.Affectation (analyse_tds_affectable tds a true, ne)
  | AstSyntax.Constante (n,v) ->
      begin
        match chercherLocalement tds n with
        | None ->
          (* L'identifiant n'est pas trouvé dans la tds locale,
             il n'a donc pas été déclaré dans le bloc courant *)
          (* Ajout dans la tds de la constante *)
          ajouter tds n (info_to_info_ast (InfoConst (n,v)));
          (* Suppression du noeud de déclaration des constantes devenu inutile *)
          AstTds.Empty
        | Some _ ->
          (* L'identifiant est trouvé dans la tds locale,
          il a donc déjà été déclaré dans le bloc courant *)
          raise (DoubleDeclaration n)
      end
  | AstSyntax.Affichage e ->
      (* Vérification de la bonne utilisation des identifiants dans l'expression *)
      (* et obtention de l'expression transformée *)
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
      AstTds.Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc then *)
      let tast = analyse_tds_bloc tds oia t in
      (* Analyse du bloc else *)
      let east = analyse_tds_bloc tds oia e in
      (* Renvoie la nouvelle structure de la conditionnelle *)
      AstTds.Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) ->
      (* Analyse de la condition *)
      let nc = analyse_tds_expression tds c in
      (* Analyse du bloc *)
      let bast = analyse_tds_bloc tds oia b in
      (* Renvoie la nouvelle structure de la boucle *)
      AstTds.TantQue (nc, bast)
  | AstSyntax.Retour (e) ->
      begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
        (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : erreur *)
      | None -> raise RetourDansMain
        (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        (* Analyse de l'expression *)
        let ne = analyse_tds_expression tds e in
        AstTds.Retour (ne,ia)
      end


(* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si le bloc li est dans le programme principal,
                   Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le bloc en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds oia li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc.
     Cette tds est modifiée par effet de bord *)
   let nli = List.map (analyse_tds_instruction tdsbloc oia) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli



(* analyser_param : tds -> info_ast -> (Type.typ * string * AstSyntax.expression option) list -> (Type.typ * info_ast * AstTds.expression option) list -> bool -> (Type.typ * info_ast * AstTds.expression option) list *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre ia : l'info sur la fonction dont les paramètres sont analysés*)
(* Paramètre lp : la liste des paramètres *)
(* Paramètre lpia : la liste des paramètres à jour (accumulateur) *)
(* Paramètre wasNone : si l'argument précédent de la liste des paramètres n'était pas un paramètre par défaut *)
(* Vérifie la bonne utilisation des identifiants,
   Met à jour l'InfoFun (nombre de paramètres non "par défaut"),
   Transforme la la liste des paramètres en une liste de paramètres adaptée à une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants
   Erreur si définition des paramètres dans un mauvais ordre *)
let rec analyser_param tds iaf lp lpia wasNone = match lp with
  | [] -> lpia
  | (typ,nom,valeur)::q -> 
    let infox = InfoVar (  false,nom,Undefined, 0, "") in
    let iax = info_to_info_ast infox in

    (* Màj de iaf, et vérification de l'ordre des paramètres *)
    let (ne,isNone) = (match valeur with
      | None -> incrementer_nb_param_normaux iaf; 
        if wasNone then (None,true)
        else raise (ArgumentParDefautMalOrdonne nom)
      | Some e -> (Some (analyse_tds_expression tds e)),false) in
    
    (* Vérification des identifiants *)
    if (List.mem (typ,iax,ne) lpia) then
      raise (DoubleDeclaration nom)
    else
      ajouter tds nom iax; 
      analyser_param tds iaf q ((typ,iax,ne)::lpia) isNone 

(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  =
begin
  match chercherLocalement maintds n with
    | Some _ -> raise (DoubleDeclaration n)
    | None ->
      (* Création de l'information sur la fonction *)
      let info = InfoFun (n,Undefined, [], 0) in
      let ia = info_to_info_ast info in
      ajouter maintds n ia; 
      let tdsfille = creerTDSFille maintds in
      
      let lpia = analyser_param tdsfille ia lp [] true in
      AstTds.Fonction(t, ia, lpia, analyse_tds_bloc tdsfille (Some ia) li)
end

(* analyser : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (varGlobales, fonctions, prog)) =
  let tds = creerTDSMere () in
  (* Analyse des variables globales vues comme une bloc *)
  let nv = List.map (analyse_tds_instruction tds None) varGlobales in
  (* Analyse des fonctions et du programme principal *)
  let nf = List.map (analyse_tds_fonction tds) fonctions in
  let nb = analyse_tds_bloc tds None prog in
  AstTds.Programme (nv,nf,nb)
