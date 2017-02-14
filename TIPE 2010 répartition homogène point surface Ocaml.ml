(* ce programme répartit des points sur une surface implicite 
Il a été écrit par mathieu Guinin dans le cadre du TIPE 2009/2010
 dDes exemples de surfaces sont disponiblent, 
pour changer d'exemple il suffit de changer le numéro 
dans la définition de "surface" et "grad" *)





(* fonctions de débogage utilisé pendant la conception *)

let debug i texte =  print_int i ; print_string texte ; print_newline ()  ;;

let debugf x texte =  print_float x ; print_string texte ; print_newline ()  ;;

let debugp (x,y,z) texte = 
	print_string "(" ;print_float x ; print_string "," ;print_float y ; print_string "," ;print_float z ;print_string ") ";
	print_string texte ; print_newline () ;; 


let mange _ = () ;;




(* définition des constantes utilisées pour le programme *)


type point = {mutable p: float * float * float  ; mutable v: float * float * float } ;;



let nNb = 500 ;;				 (* nombre de points *) 

let nN = float_of_int nNb ;;

let oO = (0.,0.,0.) ;;				(* origine *)

let npoint pos = {p= pos ; v= oO} ;;

let pPt = Array.make nNb (npoint oO) ;;		(* liste des points *)	

let fFrot = 0.8 ;;				(* coefficient de frottement fluide *)	

let dDt = 0.3 ;;					(* intervalle de temps élémentaire de la simulation *)

let eE_limite = 1e-3 ;;				(* seuil d'énergie moyenne à atteindre *)	

let aAlpha = 5. ;;				(* coefficient d'interaction *)




let infini = 1e1000 ;;	

let infini3 = (infini,infini,infini) ;;

let voisins = Array.make (nNb*256) (-1,-1,1e1000) ;;
voisins.(0) <- (-1,-1,-1.) ;;				(* tas des couples de points proches l'un de l'autre *)

let index_tas = ref (nNb*128) ;;		

let haut_tas () = 
	index_tas := (!index_tas+1) mod (nNb*128) ;
	!index_tas + nNb*128 ;;








(* définitions des fonctions géométriques de base *) 



let sgn = function 
	| x when x<0. -> -1.
	| _ -> 1. 	;;
	


let plus (x,y,z) (a,b,c) =
	(x+.a,y+.b,z+.c) ;;

let moin (x,y,z) (a,b,c) =
	(x-.a,y-.b,z-.c) ;;

let scal (x,y,z) (a,b,c) =
	x*.a +. y*.b +. z*.c
;;

let norme2 p = scal p p ;;

let norme p = sqrt (norme2 p) ;;

let dist p1 p2 =
	norme (moin p1 p2) 	
;;
	
let mult k (x,y,z) =
	(k *. x, k *. y, k*. z)
;;

let normalise v = 
	mult (1. /. (norme v)) v ;;


let project_orth n v  = 
	moin v (mult (scal v n /. (norme2 n)) n)	
;;

let project_paral d v  = 
	mult (scal v d /. (norme2 d)) d	
;;





(* formes de bases et opération sur les fonction implicite : union, intersection, complémentaire  *)



let plan normale a p = 
	scal normale p +. a ;;

let sphere centre rayon p =
	(dist centre p)**2. -. rayon**2. ;;


let grad_sphere centre p =
	mult 2. (moin p centre) ;;


let elipse axe1 axe2 axe3 centre a b c r p = 
	let d = moin p centre in
	a *. (scal axe1 d)**2. +. b *. (scal axe2 d)**2. +. c *. (scal axe3 d)**2. -. r**2. ;;

let elipse_grad axe1 axe2 axe3 centre a b c p = 
	let d = moin p centre in
	match (axe1,axe2,axe3) with ((e1x,e1y,e1z),(e2x,e2y,e2z),(e3x,e3y,e3z)) ->
	let aa = 2. *. a *. (scal axe1 d) and bb = 2. *. b *. (scal axe2 d) and cc = 2. *. c *. (scal axe3 d) in
	(aa *. e1x +. bb *. e2x +. cc *. e3x ,
	aa *. e1y +. bb *. e2y +. cc *. e3y ,
	aa *. e1z +. bb *. e2z +. cc *. e3z  ) ;;

let r22 = (sqrt 2.) /. 2. ;;

let ex = (1.,0.,0.) and ey = (0.,1.,0.) and ez = (0.,0.,1.) 
and exy = (r22,r22,0.) and eyz = (0.,r22,r22) and exz = (r22,0.,r22)
and epxy = (-. r22,r22,0.) and epyz = (0.,-. r22,r22) and epxz = (-. r22,0.,r22) ;;



let herisson rayon nt pic (x,y,z) =
	let teta = nt *. (atan2 x y) and phi = nt *. (atan2 x z) in 
	sqrt (norme2 (x,y,z)) -. (rayon +. (sin teta) *. (sin phi) *. pic) ;;


let grad_herisson nt pic (x,y,z) = 
	let norm = sqrt (norme2 (x,y,z)) in
	let teta = nt *. (atan2 x y) and phi = nt *. (atan2 x z) in 
	let d1 = nt *. pic *. (cos teta) *. (sin phi) /.  (x *. x +. y *. y)  
	and d2 = nt *. pic *. (sin teta) *. (cos phi) /.  (x *. x +. z *. z) in
	( x /. norm -. y *. d1 -. z *. d2 ,
	  y /. norm +. x *. d1 ,
	  z /. norm +. x *. d2 ) ;;



let union f1 f2 p = 
	min (f1 p) (f2 p) ;;


let union_grad (f1,g1) (f2,g2) =
	if f1 < f2 
		then (f1,g1) 
		else (f2,g2) ;;


let intersection f1 f2 p = 
	max (f1 p) (f2 p) ;;


let intersection_grad (f1,g1) (f2,g2) =
	if f1 > f2  
		then (f1,g1) 
		else (f2,g2) ;;




let compl (f,g) = (-. f , function p -> moin oO (g p) ) ;;

let exclusion f f_exc p = 
	max (f p) (-. (f_exc p)) ;;

let exclusion_grad cpl cpl_exc = 
	intersection_grad cpl (compl cpl_exc) ;; 



let operations_ensemble unions intersections exclusions p = 
	let rec boucle_union (f,g) = function
		| [] -> boucle_intersection (f,g) intersections
		| (f1,g1)::reste -> let (f2,g2) = union_grad (f1 p,g1) (f,g) in 
				boucle_union (f2,g2) reste
	and boucle_intersection (f,g)  = function
		| [] -> boucle_exclusion (f,g) exclusions
		| (f1,g1)::reste -> let (f2,g2) = intersection_grad (f1 p,g1) (f,g) in 
				boucle_intersection (f2,g2) reste
	and boucle_exclusion (f,g) = function
		| [] -> (f,g)
		| (f1,g1)::reste -> let (f2,g2) = exclusion_grad (f,g) (f1 p,g1)  in 
				boucle_exclusion (f2,g2) reste
	in match unions with 
		| (f0,g0)::suite -> boucle_union (f0 p,g0) suite 
		| _ -> failwith "surface vide" ;;


(* définition d'exemples de fonctions implicites et de leurs gradiants *)

let exemple0 = sphere oO 150. ;;
let exemple0_grad = grad_sphere oO ;;

let exemple1 = exclusion ( union (sphere oO 75.) (sphere (75.,100.,0.) 100.) ) (sphere (160. , 160. ,20.) 70.) ;;

let exemple1_grad p = (snd (	exclusion_grad ( union_grad (sphere oO 75. p ,grad_sphere oO) (sphere (75.,100.,0.) 100. p,grad_sphere (75.,100.,0.)) )  
				(sphere (160. , 160. ,20.) 70. p,grad_sphere (160. , 160. ,20.))	) 	) p ;;

let exemple2 = herisson 150. 5. 40. ;;

let exemple2_grad  = grad_herisson 5. 40. ;;

let exemple3 = elipse exy epxy ez oO 0.5 1. 2. 100. ;; 

let exemple3_grad = elipse_grad exy epxy ez oO 0.5 1. 2.  ;; 

let mG2010 = operations_ensemble [(elipse ex ey ez oO 10. 1. 10. 102.,				elipse_grad exy epxy ez oO 10. 1. 10.) ;
					(elipse exy epxy ez (45.,40.,0.) 7. 1. 7. 80.,		elipse_grad exy epxy ez (45.,40.,0.) 7. 1. 7. ) ;
					(elipse epxy exy ez (135.,40.,0.) 7. 1. 7. 80.,		elipse_grad epxy exy ez (135.,40.,0.) 7. 1. 7. ) ;
					(elipse ex ey ez (180.,0.,0.) 10. 1. 10. 102.,		elipse_grad exy epxy ez (180.,0.,0.) 10. 1. 10.) ;
					(elipse exy epxy ez (240.,-40.,0.) 8. 1. 8. 80.,	elipse_grad exy epxy ez (240.,-40.,0.) 8. 1. 8. ) ;
					(elipse epxy exy ez (250.,40.,0.) 10. 1. 10. 90.,	elipse_grad epxy exy ez (250.,40.,0.) 10. 1. 10. ) ;
					(elipse epxy exy ez (330.,-40.,0.) 8. 1. 8. 80.,	elipse_grad epxy exy ez (330.,-40.,0.) 8. 1. 8. ) ;
					(elipse ex ey ez (375.,-10.,0.) 1. 11. 11. 90.,	elipse_grad exy epxy ez (375.,-10.,0.) 1. 11. 11.) ;
					(elipse (cos 1.1,sin 1.1,0.) (-. sin 1.1,cos 1.1,0.) ez (450.,0.,0.) 1. 13. 13. 114.,
							elipse_grad (cos 1.,sin 1.,0.) (-. sin 1.,cos 1.,0.) ez (450.,0.,0.) 1. 13. 14. ) ;
					(elipse ex ey ez (450.,70.,10.) 1. 1. 15. 60. , 	elipse_grad ex ey ez (450.,70.,10.) 1. 1. 15.  ) ;
					(elipse ex ey ez (490.,-90.,0.) 1. 13. 13. 100.,	elipse_grad exy epxy ez (490.,-90.,0.) 1. 13. 13.) ;
					(elipse ex ey ez (570.,-20.,0.) 1. 1. 15. 80. , 	elipse_grad ex ey ez (570.,-20.,0.) 1. 1. 15. ) ;
					(elipse ex ey ez (660.,-10.,0.) 10. 1. 10. 80.,		elipse_grad exy epxy ez (660.,-10.,0.) 10. 1. 10.) ;
					(elipse ex ey ez (750.,-20.,0.) 1. 1. 15. 80. , 	elipse_grad ex ey ez (750.,-20.,0.) 1. 1. 15. ) ; ] 

					[]
					[(sphere (450.,70.,25.) 40. , 	grad_sphere (450.,70.,25.) ) ;
					(sphere (570.,-20.,20.) 50. , 	grad_sphere (570.,-20.,20.) ) ;
					(sphere (750.,-20.,20.) 50. , 	grad_sphere (750.,-20.,20.) ) ] ;;


let (exemple4,exemple4_grad) = ((function p -> fst (mG2010 p)),(function p -> (snd (mG2010 p)) p)) ;;



(* ICI CHANGER L'EXEmPLE DE SURFACE *)

let surface = exemple2 ;;

let grad = exemple2_grad ;; 





let z_00 = 32. ;;


(* définition de la composente normale au plan de l'écran du gradiant pour l'affichage de la surface *)

let gradz p = 
	match grad p with 
	| (_,_,z) -> z ;;




(* fonction de projection d'un point sur la surface en utilisant la méthode de nNewton *)


let rec project_surface direction p = function 
	| 0 -> infini3
	| n -> 
	let s = surface p in 
	if abs_float s < 0.01 
		then   p 
		else   let g = direction p in
			project_surface direction (moin p (mult (s /. (norme2 g) ) g)) (n-1)
;;








(* pseudo_dist calcul un minorant de la distance réel sur la surface entre deux points *)


let pseudo_dist p1 p2 = 
	let milieu = mult 0.5 (plus p1 p2) 
	and mediateur = function p -> project_orth (moin p1 p2) (grad p) in
	let m = project_surface mediateur milieu 5 in 
	if m = infini3 
		then 4. *. (dist p1 p2)
		else (dist p1 m) +. (dist m p2) ;;
	




(* définition de la force d'intéraction entre deux point *)

let interaction p1 p2 r_inter dist = 
	let d = moin p1.p p2.p in
	let df = (exp (-. aAlpha *. (dist /. r_inter)**2.) ) *. r_inter *. dDt in
	let a = mult (df /. dist) d in
	p1.v <- plus p1.v a ; 
	p2.v <- moin p2.v a  
;;




		

(* ouvre la fenêtre graphique de Caml light *)

#load "graphics.cma" ;;
open Graphics ;;
open ArrayLabels ;;
open Random ;;
open_graph " 1280x1024" ;;


Random.self_init ();;

(* dessine et enregistre un aperçu de la forme crée avec une méthode de raytracing *)


let x1 = -300 and x2 = 900 and y1 = -300 and y2 = 300 ;;




let matrice_ecran = make_matrix (x2-x1) (y2-y1) infini ;;
for i = 0 to (x2-x1-1) do 
	matrice_ecran.(i).(0) <- 0. ;
	matrice_ecran.(i).(y2-y1-1) <- 0. ;
done ;
for i = 0 to (y2-y1-1) do 
	matrice_ecran.(0).(i) <- 0. ;
	matrice_ecran.(x2-x1-1).(i) <- 0. ;
done ;;



let direction_eclerage = (cos 1.,(sin 1.) *. (cos 1.) , (cos 1.) *. (cos 1.)  ) ;;

let eclairage p (rouge,vert,bleu) ampl = 
	let g = grad p in 
	let lum = ampl +. (1. -. ampl) *. (scal g direction_eclerage ) /. (norme g) in 
	set_color (int_of_float (bleu *. lum) + (int_of_float (vert *. lum))*256 + (int_of_float (rouge *. lum))*65536 ) ;;




let raytracing z_ini = 
	let rec project_gradz (x,y,z) = function 
		| 0 -> -. infini
		| n -> 
		let s = surface (x,y,z) in 
		if abs_float s < 0.1 
			then z 
			else   let g = gradz (x,y,z) in
				project_gradz (x,y,z -. s /. g) (n-1)
	in 
	let rec diffuse = function 
		| [],[] -> ()
		| suivants , [] -> diffuse ([] , suivants) 
		| suivants , ((i,j,z)::reste) ->
		if matrice_ecran.(i-x1).(j-y1) = infini
			then 
			let x = float_of_int i and y = float_of_int j in 
			let z0 = project_gradz (x,y,z+. 1.5) 6 in 
			if z0 <> -. infini 
				then ( 	matrice_ecran.(i-x1).(j-y1) <- z0 ;
					eclairage (x,y,z0) (255.,0.,0.) 0.5;
					plot (i+500) (j+500)  ;
					diffuse (((i-1,j,z0)::(i+1,j,z0)::(i,j-1,z0)::(i,j+1,z0)::suivants) , reste)
				)
				else diffuse (suivants , reste) 
			else diffuse (suivants , reste)
	in diffuse ([] , [(0,0,z_ini)]);
	get_image (x1+500) (y1+500) (x2-x1) (y2-y1)  ;;

let apercu = raytracing  z_00  ;; 

		
(* affiche l'image de la surface *)	
		
let dessine_surface () =
	 draw_image apercu (500+x1) (500+y1) 
;;

(* affiche un point sur l'écran *)


let affiche (x,y,z) =
	let i = int_of_float x and j = int_of_float y in
	if abs_float (z -. matrice_ecran.(i-x1).(j-y1) ) < 10.
		then (eclairage (x,y,z) (0.,255.,0.) 0.7;
			fill_circle (i +500) (j +500) 2 )
		else (eclairage (x,y,z) (0.,0.,255.) 0.7; 
			fill_rect (i +500) (j +500) 2 2) ;;










(* la fonction génère_points se compose de quatres parties : 
	_ gérération récursive de la moitier des points en utilisant génère_points (n/2) 
	_ chaque des n/2 points reçoit un fils qui est sa copie légèrement décalé sur la surface 
	_ on définie les nouveaux voisinage grace aux voisinages des point n/2 premiers point 
	_ on fait évoluer dynamiquement l'ensemble des point jusqu'à atteindre un équilibre     *)





let rec genere_points = function 
	| 1 -> pPt.(0) <- { p= project_surface grad (0.1,0.1,matrice_ecran.(-x1).(-y1)) 10 ; v=oO} ; 
		100. ;
	| n -> 
	let n1 = n/2 and n2 = n-n/2 in
	debug n2 " appel genere_points " ;
	let r_moyen = genere_points n2 in 
	debug n2 " genere_points accompli" ;
	debugf r_moyen " r_moyen" ;
	let r_voisinage = 8. *. r_moyen in
	

	debug n " debut mitose" ;

	let liste_attente = ref [] in

	let rec mitose = function 
		| 0 -> ()
		| i ->  let ecart = project_orth (grad pPt.(n1-i).p) (float 1.,float 1.,float 1.) in 
			let p = project_surface grad (plus pPt.(n1-i).p (mult (0.5 *. r_moyen /. (norme ecart) ) ecart) ) 10 in 
			if p = infini3 
				then mitose (i - 1)
				else ( pPt.(n-i) <- { p = p ; v = oO } ;
				liste_attente := (n1-i,n-i)::(!liste_attente) ;
				mitose (i-1) ; )
	in mitose n1 ;

	debug n " debut actualise_couple " ;
	
	let actualise_couple (i,j) k = 
		let d = pseudo_dist pPt.(i).p pPt.(j).p in
		let rec percole l = 
			let (ii,jj,dd) = voisins.(l/2) in
			if dd>d 
				then ( voisins.(l) <- (ii,jj,dd) ;
					percole (l/2)  )
				else  voisins.(l) <- (i,j,d) 
		in percole k ; d ;
	in

	debug n " debut fabrique_voisinages " ;

	
	let rec recherche_voisins k =
		if k < 256*nNb 
			then (
			let (i,j,d) = voisins.(k) in
			if d < r_voisinage 
				then (
				if j < n1 
					then liste_attente := (i,j+n2)::(j,i+n2)::(i+n2,j+n2)::(!liste_attente) 
					else liste_attente := (j,i+n2)::(!liste_attente) ;
				recherche_voisins (2*k) ;
				recherche_voisins (2*k+1) ; 
				) 
			)
	in recherche_voisins 1 ;

	let rec actualise_tas = function 
		| [] -> () 
		| c::reste -> mange (actualise_couple c (haut_tas ()) ) ;
				actualise_tas reste 
	in actualise_tas (!liste_attente) ;


	debug n " debut	evolution" ;




	
	let rec evolution phase r_inter = 
		
	
		let rec coef_raf n = 
			if n land 1 = 0 
				then ( sqrt 2.) *. coef_raf (n lsr 1)
				else 2. 
		in 
		let r_rafrech = (coef_raf phase) *. r_inter in 
		
		let min_r = ref 1e1000 in
	
		let rec interac_couple k =  
			if k < nNb*256
			then (  let (i,j,d) = voisins.(k) in
				if d < r_rafrech 
				then (
					let dp = actualise_couple (i,j) k in
					if dp < r_inter 
					then ( interaction pPt.(i) pPt.(j) r_inter dp  ;
						min_r := min !min_r dp ;
						) ;
					interac_couple (2*k) ;
					interac_couple (2*k+1) ;
					)  
				)
		in interac_couple 1 ;

		
		
		let r_moy = !min_r in 
	
		
		dessine_surface () ;
		
		

		let rec avance = function 
			| -1 -> () 
			| i -> let a = pPt.(i) in 
				let vp = project_orth (grad a.p) a.v in 
				a.v <- mult fFrot  vp ;
				let ap = project_surface grad (plus a.p a.v) 5 in
				if ap = infini3 
					then ( a.v <- oO  )
					else ( a.p <- ap  ) ;
				affiche a.p ;
				avance (i-1) ;
		in avance (n-1) ;

	

	
		let rec energie_moy e = function 
			| -1 -> e /. (float_of_int n)
			| i -> energie_moy (norme2 pPt.(i).v +. e) (i-1) 
		in 

		

		if phase mod 32 <> 0 ||  energie_moy 0. (n-1) > eE_limite *. r_moy**2. 
			then evolution (phase+1) (r_moy *. 2.0) 
			else (debug phase " phase d'arrêt" ; r_moy)

	in evolution 1 (r_moyen /. (sqrt 2.) );;


let r_final = genere_points nNb ;;




let rec boucle1 list_erreur = function 
	| -1 -> list_erreur 
	| i -> let rec boucle2 list_er = function 
		| -1 -> boucle1 list_er (i-1) 
		| j -> let d = pseudo_dist pPt.(i).p pPt.(j).p in 
			if d < r_final *. 0.5 
			then boucle2 (((i,j),d)::list_er) (j-1) 
			else boucle2 list_er (j-1) 
		in boucle2 list_erreur (i-1)
in boucle1 [] (nNb-1) ;;


read_key ();;
