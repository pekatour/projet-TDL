open Rat
open Compilateur
open Exceptions

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

(****************************************)
(** Chemin d'accès aux fichiers de test *)
(****************************************)

let pathFichiersRat = "../../../../tests/pointeurs/fichiersRat/"

(**********)
(*  TESTS *)
(**********)

let%test_unit "testAdresseConstante" =
  try 
  let _ = compiler (pathFichiersRat^"testAdresseConstante.rat")
    in raise ErreurNonDetectee
  with
  | MauvaiseUtilisationIdentifiant("c") -> ()

 let%test_unit "testAffichagePointeur" = 
 let _ = compiler (pathFichiersRat^"testAffichagePointeur.rat") in ()

let%expect_test "testTD" = 
  runtam (pathFichiersRat^"testPointeurTD.rat");
  [%expect{| 4 |}]

let%expect_test "testCascade" = 
  runtam (pathFichiersRat^"testCascade.rat");
  [%expect{| 2 |}]

let%expect_test "testNull" = 
  runtam (pathFichiersRat^"testNull.rat");
  [%expect{| 4 |}]
