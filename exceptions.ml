open Type
open Ast.AstSyntax

(* Exceptions pour la gestion des identificateurs *)
exception DoubleDeclaration of string 
exception IdentifiantNonDeclare of string 
exception MauvaiseUtilisationIdentifiant of string
exception ArgumentParDefautMalOrdonne of string
exception NombreArgumentsInsuffisant of string

(* Exceptions pour le typage *)
(* Le premier type est le type réel, le second est le type attendu *)
exception TypeInattendu of typ * typ
(* Le type en argument est le type réel *)
exception TypePointeurAttendu of typ
exception TypesParametresInattendus of typ list * typ list
exception TypeBinaireInattendu of binaire * typ * typ (* les types sont les types réels non compatible avec les signatures connues de l'opérateur *)

(* Utilisation illégale de return dans le programme principal *)
exception RetourDansMain
