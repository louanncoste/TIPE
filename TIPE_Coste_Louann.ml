

(*Coloration de graphe d'intervalles*)



type intervalle = int*int ;;     (*un intervalle est caractérisé par ses bornes de début et de fin, qui seront ici des entiers distincts*)
type graphe_intervalle = intervalle list ;;

(*un graphe d'intervalle est implémenté comme une liste d'intervalles, ordonnés dans l'ordre croissant de leur borne de début.
On commence la numérotation à 0. Pour chaques bornes des intervalles, on peut associer des entiers distincts et consécutifs.
Ainsi, en notant p le nombre d'intervalles (qui est aussi le nombre d'arêtes du graphe), chaque entier de 0 à 2p-1 représente une borne 
(de début ou de fin) d'un intervalle. (0 étant nécessairement une borne de début et 2p-1 une borne de fin*) 


(*Un exemple de graphe d'intervalles avec 7 sommets*)
let exemple_intervalle = [(0,7);(1,3); (2,6) ; (4,10); (5,12); (8,9) ; (11,13)] ;;





(*Inplémentation de l'algorithme de coloration d'un graphe d'intervalle*)

let coloration_graphe_intervalles g =

	let compteur = ref (-1) in                                (*nombre de couleurs utilisées*)
	let p = List.length g in 
	
	if p=0 then 0,[||]                (*cas graphe vide*)
	else                             
	
	
	let couleur = Array.make p (-1) in                     (*tableau des couleurs indicé par la place du sommet dans la liste. Les couleurs sont des entiers indicés à partir de 0*) 
	let couleurs_utilisees= Array.make (2*p - 1) [] in     (*tableau indicé par les entiers dont les bornes prennent les valeurs  *)


			(*trouve la couleur minimale disponible dans une liste non triée des couleurs déjà prises au début de l'intervalle*)
			let min_dispo l = 
				let n = List.length l in 
				let avail=Array.make n true in              (*avail.(i)=true si la couleur est disponible et false sinon. On a besoin d'aller jusqu'à au plus n-1 pour trouver une couleur disponible*)
			
					let rec parcours_liste = function 
						|[]-> ()
						|t::q -> if t<n then avail.(t)<- false;
									parcours_liste q
					in
					
					parcours_liste l;
					
					let i = ref 0 in
					while !i < n && not avail.(!i) do 
					incr i 
					done;
					!i
			
			in 


		let rec parcours_graphe g k = match g with
			|[]-> !compteur +1, couleur
			|(d,f)::q -> let m = min_dispo couleurs_utilisees.(d) in
							couleur.(k)<- m;
							if m> !compteur then incr compteur;
							for i=(d+1) to (f-1) do
							couleurs_utilisees.(i)<- m::couleurs_utilisees.(i) 
							done;
							
							parcours_graphe q (k+1)
		in	

		parcours_graphe g 0;;







coloration_graphe_intervalles exemple_intervalle;;	








	
	



(*Coloration de graphe cordal*)





(*On utilise la structure des listes d'ajacences pour implémenter les graphes cordaux*)


let exemple_graphe_cordal = [| [1;2;3;4;5] ; [0;2;5] ; [0;1;3;5] ; [0;2;4;5] ; [0;3;5] ; [0;1;2;3;4] |];; 




(*On implémente d'abord l'algorithme LexBFS en utilisant un tas de priorité respectant l'ordre lexicographique. 
On choisit arbitrairement de traiter le sommet 0 en premier*)


let ordre_lexbfs g = 
	let n = Array.length g in 
	let traiter = Array.make n 0 in             (*tableau indicé par les sommets de g, contient 1 si le sommet est traité, 0 sinon*)
	let ordre = ref [] in							  (*liste qu'on va renvoyer en sortie d'algorithme*) 
	let tas = Array.make (n+1) (0,[]) in        (*file de priorité composée du couple (sommet, liste_sommet), triée par ordre lexicographique de liste_sommet,
																	où liste_sommet est la liste des numéros des voisins de sommet déjà traités, leur numéro étant attribué dans l'ordre de traitement des sommets *)
	let place_dans_tas = Array.make n 1 in       (*tableau indicé par les sommets, qui stocke l'indice des sommets dans tas*)

		
	(*initialisation tas*)
	for i = 1 to (n-1) do
		place_dans_tas.(i)<-i+1 ;
		tas.(i+1) <- (i, [])
	done;
	tas.(0)<- (n, []) ;   (*la case d'indice 0 sert à indiquer le nombre de sommets dans tas*)
	tas.(1)<- (0, [n]) ;



				(*échange les cases i et j d'un tableau t*)
				let echange t i j =
						let ti= t.(i) in
						t.(i)<-t.(j);
						t.(j)<- ti 
				in



				(*On vient d'ajouter un élément à la liste placée dans tas.(k), on fait donc remonter ce couple pour conserver la structure de tas*)
				let rec replace k =
						if k>1 && snd(tas.(k/2)) < snd(tas.(k)) 
							then (echange tas (k/2) k ;
									echange place_dans_tas (fst(tas.(k/2))) (fst(tas.(k))); 
									replace (k/2) )
					in	




				(* vois est la liste des voisins du sommet auquel on a attribué le numéro de traitement i,
			   pour chacun de ces voisins non traités, on ajoute i à leur liste dans tas, et on les replace correctement dans tas*)
				let rec ajoute_aux_voisins vois i = match vois with
					|[]-> ()
					|h::q-> if traiter.(h)=0 
									then (let s,ls = tas.(place_dans_tas.(h)) in
											tas.(place_dans_tas.(h)) <- s, (ls @ [i-1]) ;
											replace (place_dans_tas.(h))  ) ;
								ajoute_aux_voisins q i
				in




				(*retire le maximum du tas t et réorganise t pour qu'il conserve sa structure de tas*)
				let retirer_max_tas t=
					let t0= fst(t.(0)) in

					let rec descente t i tn0 =
						let c = ref i in
						if 2*i <= tn0 && snd(t.(2*i)) > snd(t.(i)) then c:= 2*i ;
						if 2*i+1 <= tn0 && snd(t.(2*i+1)) > snd(t.(!c)) then c:= 2*i+1 ;
						if !c <> i then ( echange t i !c ; 
												echange place_dans_tas (fst(t.(i))) (fst(t.(!c)))  ;
												descente t !c tn0 )
					in

					echange t t0 1 ;
					echange place_dans_tas (fst(tas.(t0)))  (fst(tas.(1))) ;
					t.(0)<- (t0-1, []) ;
					descente t 1 (t0-1);
				in




	for i=n downto (1) do  
		let maxi = fst(tas.(1)) in
		ordre :=  maxi :: !ordre;
		traiter.(maxi)<-1;
		retirer_max_tas tas;
		ajoute_aux_voisins g.(maxi) i;
		(*reorganise_tas ;*)
		
	done ;
	
	!ordre
		;;


		


ordre_lexbfs exemple_graphe_cordal;;	






(*Puis on utilise lexbfs dans l'algorithme de coloration...*)


let coloration_cordal g  =
	
	let ordre = List.rev(ordre_lexbfs g) in
	let p = Array.length g in
	let couleur = Array.make p (-1) in     (*couleur.(i) <- couleur du noeud i. Couleurs numérotées à partir de 0*) 
	let compteur = ref 0 in						(*nombre de couleurs utilisées*)
	
	
		(*Prend en paramètre la liste des voisins d'un sommet x.
		  Pour chaque voisin de x déjà colorié, on indique dans avail que sa couleur n'est plus disponible*)
			let rec traiter_vois avail = function     
				|[]-> ()
				|h::q -> if couleur.(h) <> -1 then avail.(couleur.(h)) <- false; 
							traiter_vois avail q 
			in


		(*trouve la plus petite couleur disponible dans avail*)
			let min_dispo avail = 
				let rec aux = function
					|i when i=p -> failwith"pas assez de couleurs"
					|i when avail.(i) -> i
					|i -> aux (i+1)
				in aux 0
			in
		
		
		
	let rec parcours l g = match l with
		|[] -> (!compteur +1 , couleur)
		|t::q-> let avail = Array.make p true in  (*pour une couleur i, avail.(i) = true si le couleur est libre et false sinon*) 
					traiter_vois avail g.(t);
					let m = min_dispo avail in
					couleur.(t)<-m;
					if m> !compteur then compteur:=m;
					parcours q g
	in
	
	parcours ordre g 
;;






coloration_cordal (exemple_graphe_cordal) ;;






