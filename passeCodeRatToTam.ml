(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Type
open Ast
open Code
open Tam

type t1 = Ast.AstPlacement.programme
type t2 = string

(* analyse_code_affectable : tds -> AstSyntax.affectable -> AstTds.affectable *)
(* Paramètre a : l'affectable à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme l'affectable
en un affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_code_affectable a modif = 
  match a with
  | AstType.Ident info -> 
    begin
      match info_ast_to_info info with
        | InfoVar ( false,_,t,dep,reg) -> (if modif then store else load) (getTaille t) dep reg
        | InfoVar ( true,_,t,dep,reg) -> load 1 dep reg ^ (if modif then storei else loadi) (getTaille t)
        | InfoConst(_,v) -> loadl_int v
        | _ -> failwith "impossible"
    end
  | AstType.Deref a2 ->
    (* On veut dorénavant load les "sous-objets" et plus store, si on était du côté gauche d'une affectation *)
    let sa2 = analyse_code_affectable a2 false in
    let taille =
    match a2 with
    | AstType.Ident info -> 
      begin
        match info_ast_to_info info with
          | InfoVar ( false,_,t,_,_) -> getTaille t
          | InfoVar ( true,_,_,_,_) -> 1
          | _ -> failwith "impossible"
      end
    | AstType.Deref _ -> 1
    in
    sa2 ^ ((if modif then storei else loadi) taille)


(* analyse_type_expression : type -> AstPlacement.expression -> AstType.expression *)
(* Paramètre type : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)


let rec analyse_code_expression e =
  match e with
    | AstType.AppelFonction(info,le) ->
      begin
        List.fold_right (fun x resq -> analyse_code_expression x ^ resq) le ""
        ^ call "SB" (match info_ast_to_info info with
          | InfoFun(n,_,_) -> n
          | _ -> failwith "impossible")
      end 
    | AstType.Affectable a -> analyse_code_affectable a false

    | AstType.Adresse info -> begin match info_ast_to_info info with
      | InfoVar ( _,_,_,dep,reg) -> loada dep reg
      | _ -> failwith "impossible"
    end
    
    | AstType.New t -> loadl_int (getTaille t) ^ subr "MAlloc"

    | AstType.Null -> subr "MVoid"

    | AstType.Binaire (b,e1,e2) -> let s1 = analyse_code_expression e1 in
      let s2 = analyse_code_expression e2 in s1 ^ s2 ^
      begin
        match b with (* -------------------- On a mis SB, on est pas sûrs ----------------------------- *)
          | Fraction -> call "SB" "norm"
          | PlusInt  -> subr "IAdd"
          | PlusRat  -> call "SB" "radd"
          | MultInt  -> subr "IMul"
          | MultRat  -> call "SB" "rmul"
          | EquInt   -> subr "IEq"
          | EquBool  -> subr "IEq"
          | Inf      -> subr "ILss"
      end
    | AstType.Unaire (op,e) -> 
      let ne = analyse_code_expression e in
      begin
        match op with
          | Numerateur -> ne ^ pop 0 1
          | Denominateur -> ne ^ pop (1) 1
      end
    | AstType.Booleen b -> if b then loadl_int 1 else loadl_int 0
    | AstType.Entier i -> loadl_int i
  


(* analyse_code_instruction : type -> info_ast option -> AstPlacement.instruction -> string.instruction *)
(* Paramètre type : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
    Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type string.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) ->
      begin
       let ne = analyse_code_expression e in
        match info_ast_to_info info with
          | InfoVar ( false,_,t,dep,reg) -> push (getTaille t) ^ ne ^ store (getTaille t) dep reg
          | InfoVar ( true,_,t,dep,reg) -> let fin = getEtiquette () in 
            load 1 dep reg ^ loadl_int 0 ^ subr "IEq" ^ jumpif 0 fin ^
              loadl_int (getTaille t) ^ subr "MAlloc" ^ store 1 dep reg ^ ne ^ load 1 dep reg ^ storei (getTaille t) ^
            label fin
          | _ -> failwith "impossible"
      end
  | AstPlacement.Affectation (a,e) ->
      let ne = analyse_code_expression e in
      let na = analyse_code_affectable a true in
      ne ^ na
  | AstPlacement.AffichageInt e ->
    begin
      let ne = analyse_code_expression e in ne ^ subr "IOut"
    end
  | AstPlacement.AffichageRat e ->
    begin
      let ne = analyse_code_expression e in ne ^ call "SB" "rout"

    end
  | AstPlacement.AffichageBool e ->
    begin
      let ne = analyse_code_expression e in ne ^ subr "BOut"
    end
  | AstPlacement.Conditionnelle (c,t,e) ->
      let sc = analyse_code_expression c in
      let st = analyse_code_bloc (fst t) (snd t) in
      let se = analyse_code_bloc (fst e) (snd e) in
      let debutElse = getEtiquette () in
      let fin = getEtiquette () in
      sc ^ jumpif 0 debutElse ^ st ^ jump fin ^ label debutElse ^ se ^ label fin

  | AstPlacement.TantQue (c,b) ->
    let nc = analyse_code_expression c in
    let nb = analyse_code_bloc (fst b) (snd b) in
    let debut = getEtiquette () in let fin = getEtiquette () in
    label debut ^ nc ^ jumpif 0 fin ^ nb ^ jump debut ^ label fin 

  | AstPlacement.Retour (e, tailleRet, tailleParam) -> 
    begin
      let se = analyse_code_expression e in
      se ^ return tailleRet tailleParam
     end
  | AstPlacement.Empty -> ""


(* analyse_code_bloc : type -> info_ast option -> AstPlacement.bloc -> string.bloc *)
and analyse_code_bloc li taille = match li with
      | [] -> pop 0 taille
      | t::q -> let si = analyse_code_instruction t in 
        let sq = analyse_code_bloc q taille in si ^ sq

(* Analyse du code des déclarations des variables globales *)
and analyse_code_varglobales li = match li with
      | [] -> ""
      | t::q -> let si = analyse_code_instruction t in 
        let sq = analyse_code_varglobales q in si ^ sq
  
(* analyse_code_fonction : type -> AstPlacement.fonction -> string.fonction *)
let analyse_code_fonction (AstPlacement.Fonction(info,_,(li,taille)))  =
begin
  (match info_ast_to_info info with
    | InfoFun(n,_,_) -> label n ^ analyse_code_bloc li taille ^ halt ^ "\n"
    | _ -> failwith "impossible")
  
end

(* analyser : string.programme -> string.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et transforme le programme
en un programme de type string.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstPlacement.Programme (varGlobales,fonctions,prog,nbVarStaticLocal)) =

  let rec placeStatic taille =
    if taille > 0 then
      loadl_int 0 ^ placeStatic (taille-1)
    else ""
  in
  let entete = getEntete () in
  let sv = analyse_code_varglobales (fst varGlobales) in
  let sf = List.fold_right (fun x resq -> analyse_code_fonction x ^ resq) fonctions "" in
  let sb = analyse_code_bloc (fst prog) (snd prog) in sv ^ placeStatic nbVarStaticLocal ^ entete ^ sf ^ label "main" ^ sb ^ pop 0 (snd varGlobales) ^ halt
  
