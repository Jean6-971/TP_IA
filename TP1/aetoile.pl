%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant
   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.
   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.
Predicat principal de l'algorithme :
   aetoile(Pf,Pu,Q)
   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs
*/

%*******************************************************************************

%:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
%:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 

	% fixer la situation de départ S0
	initial_state5(S0),

	% calculer les valeurs F0, H0, G0 pour cette situation
	G0 is 0,
	heuristique(S0, H0),
	F0 is H0,

	% créer 3 AVL Pf, Pu et Q initialement vides
	empty(Pu),
	empty(Pf),
	empty(Q),

	% insérer un noeud [ [F0,H0,G0], S0 ] dans Pf et un noeud [S0, [F0,H0,G0], nil, nil] dans Pu
	insert([[F0,H0,G0],S0],Pf,Pf_new),
	insert([S0,[F0,H0,G0],nil,nil],Pu,Pu_new),

	% lancement de Aetoile
	aetoile(Pu_new, Pf_new, Q).


%*******************************************************************************

% on peut l’afficher
affiche_solution(_,[S]):-
    initial_state(S),
    write_state(S).

affiche_solution(P,[S]):-
    belongs([S,_,Pere, _],P),
    write_state(S),
	nl,
	affiche_solution(P,[Pere]).



% calculer leur évaluation [Fs, Hs, Gs] connaissant Gu et le coût pour passer de U à S
expand([S,[_,_,G],_,_], L) :-
	findall([S_new, [(Fs), Hs, Gs], S, A], (rule(A, _, S, S_new),Gs is G+1,heuristique(S_new, Hs),Fs is Gs+Hs),  L).

	

% traiter chaque nœud successeur
loop_successors([], _, Pu, Pf, Pu, Pf).

% si S est connu dans Q alors oublier cet état (S a déjà été développé)
loop_successors([[S, _, _, _]|Rest], Q, Pu, Pf, Pu_new, Pf_new) :-
	belongs([S,_,_,_],Q),
	loop_successors(Rest, Q, Pu, Pf, Pu_new, Pf_new).

% si S est connu dans Pu alors garder le terme associé à la meilleure évaluation  (dans Pu et dans Pf)
loop_successors([[S, [F,H,G], Pere, A]|Rest], Q, Pu, Pf, Pu_next, Pf_next) :-
	suppress([S, [F1,H1,G1], Pere_new, A_new], Pu, Pu_new),
	suppress([[F1,H1,G1],S], Pf, Pf_new),
	% comparer G + H à F1
	(F @< F1 -> 
		% si G + H < F1 alors on garde le nouveau terme
		insert([[F,H,G],S],Pf_new,Pf_new_2),
		insert([S,[F,H,G],Pere,A],Pu_new,Pu_new_2)
	;
		% sinon on garde le terme deja connu
		insert([[F1,H1,G1],S], Pf_new, Pf_new_2), 
        insert([S, [F1,H1,G1], Pere_new, A_new], Pu_new, Pu_new_2)
	),
	loop_successors(Rest, Q, Pu_new_2, Pf_new_2, Pu_next, Pf_next).

%		si S est entierement nouveau on l'insere dans Pf et dans Pu
% sinon (S est une situation nouvelle) il faut créer un nouveau terme à insérer dans Pu (idem dans Pf)
loop_successors([[S, [F,H,G], Pere, A]|Rest], Q, Pu, Pf, Pu_next, Pf_next) :-
	insert([S, [F,H,G], Pere, A], Pu, Pu_new),
	insert([[F,H,G], S], Pf, Pf_new),
	loop_successors(Rest, Q, Pu_new, Pf_new, Pu_next, Pf_next).



% si Pf et Pu sont vides, il n’y a aucun état pouvant être développé donc pas de solution au problème
aetoile(nil, nil, _) :-
    writeln('PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !'),
    fail.

% si le nœud de valeur F minimum de Pf correspond à la situation terminale, alors on a trouvé une solution et on peut l’afficher
aetoile(Pu, Pf, Q) :-
	final_state(Fin),
	suppress_min([[F,H,G],Fin], Pf, _),
    suppress([Fin, [F,H,G], Pere, A], Pu, _),
    insert([Fin,[F,H,G], Pere, A], Q, Q_new),
    affiche_solution(Q_new,[Fin]).

% sinon
aetoile(Pu, Pf, Q) :-
	% on enlève le nœud de Pf correspondant à l’état U à développer (celui de valeur F minimale) et on enlève aussi le nœud frère associé dans Pu
	suppress_min([[F,H,G],S], Pf, Pf_new),
	suppress([S, _, Pere, A], Pu, Pu_new),
	% développement de U

	% déterminer tous les nœuds contenant un état successeur S de la situation U et calculer leur évaluation [Fs, Hs, Gs] (prédicat expand)
	% connaissant Gu et le coût pour passer de U à S.
	expand([S,[F,H,G],Pere, A], L),
	% traiter chaque nœud successeur (prédicat loop_successors)
	loop_successors(L, Q, Pu_new, Pf_new, Pu_new_2, Pf_new_2),
 
	% U ayant été développé et supprimé de P, il reste à l’insérer le nœud [U,Val,…,..] dans Q
	insert([S,[F,H,G], Pere, A], Q, Q_new),
	% Appeler récursivement aetoile avec les nouveaux ensembles Pf_new, Pu_new et Q_new
	aetoile(Pu_new_2, Pf_new_2, Q_new).


