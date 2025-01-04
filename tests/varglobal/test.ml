open Rat
open Compilateur
(* open Exceptions *)
open Passe


exception ErreurNonDetectee

(* Changer le chemin d'accès du jar. *)
let runtamcmde = "java -jar ../../../../tests/runtam.jar"
(* let runtamcmde = "java -jar /mnt/n7fs/.../tools/runtam/runtam.jar" *)

(* Execute the TAM code obtained from the rat file and return the ouptut of this code *)
let runtamcode cmde ratfile =
  let tamcode = compiler ratfile in
  let (tamfile, chan) = Filename.open_temp_file "test" ".tam" in
  output_string chan tamcode;
  close_out chan;
  let ic = Unix.open_process_in (cmde ^ " " ^ tamfile) in
  let printed = input_line ic in
  close_in ic;
  Sys.remove tamfile;    (* à commenter si on veut étudier le code TAM. *)
  String.trim printed

(* Compile and run ratfile, then print its output *)
let runtam ratfile =
  print_string (runtamcode runtamcmde ratfile)

(* Return la liste des adresses des variables d'un programme RAT *)
let getListeDep ratfile =
  let input = open_in ratfile in
  let filebuf = Lexing.from_channel input in
  try
  let ast = Parser.main Lexer.token filebuf in
  let past = CompilateurRat.calculer_placement ast in
  let listeAdresses = VerifPlacement.analyser past in
  listeAdresses
  with
  | Lexer.Error _ as e ->
      report_error ratfile filebuf "lexical error (unexpected character).";
      raise e
  | Parser.Error as e->
      report_error ratfile filebuf "syntax error.";
      raise e

(* teste si dans le fichier fichier, dans la fonction fonction (main pour programme principal)
la occ occurence de la variable var a l'adresse dep[registre]
*)
let test fichier fonction (var,occ) (dep,registre) = 
  let l = getListeDep fichier in
  let lmain = List.assoc fonction l in
  let rec aux i lmain = 
    if i=1 
    then
      let (d,r) = List.assoc var lmain in
      (d=dep && r=registre)
    else 
      aux (i-1) (List.remove_assoc var lmain)
  in aux occ lmain

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../tests/varglobal/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

(* let%test_unit "testAdresseConstante" =
  try 
  let _ = compiler (pathFichiersRat^"testAdresseConstante.rat")
    in raise ErreurNonDetectee
  with
  | MauvaiseUtilisationIdentifiant("c") -> () *)

let%test_unit "test1" = 
 let _ = compiler (pathFichiersRat^"test1.rat") in ()

let%test_unit "test2" = 
 let _ = compiler (pathFichiersRat^"test2.rat") in ()

let%test_unit "test3" = 
 let _ = compiler (pathFichiersRat^"test3.rat") in ()

let%test "test3_placementa" = 
 test (pathFichiersRat^"test3.rat")  "varGlobales" ("a",1)  (0,"SB")

let%test "test3_placementb" = 
 test (pathFichiersRat^"test3.rat")  "varGlobales" ("b",1)  (1,"SB")

let%test "test3_placementz" = 
 test (pathFichiersRat^"test3.rat")  "main" ("z",1)  (2,"SB")

let%expect_test "testTAM" = 
 runtam (pathFichiersRat^"test4.rat");
 [%expect{| 13574 |}]
