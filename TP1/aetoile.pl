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

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 
	writeln('Initialisation'),

	% fixer la situation de départ S0
	writeln('Situation de depart'),
	initial_state(S0),
	writeln(S0),

	% calculer les valeurs F0, H0, G0 pour cette situation
	writeln('Valeurs initiales'),
	G0 is 0,
	write('G0 = '), write(G0), nl,
	heuristique(S0, H0),
	write('H0 = '), write(H0), nl,
	F0 is (G0 + H0),
	write('F0 = '), write(F0), nl,

	% créer 3 AVL Pf, Pu et Q initialement vides
	writeln('Creation des ensembles'),
	empty(Pu),
	writeln(Pu),
	empty(Pf),
	writeln(Pf),
	empty(Q),
	writeln(Q),

	% insérer un noeud [ [F0,H0,G0], S0 ] dans Pf et un noeud [S0, [F0,H0,G0], nil, nil] dans Pu
	writeln('Insertion des noeuds'),
	insert([[F0,H0,G0],S0],Pf,Pf_new),
	writeln(Pf_new),
	insert([S0,[F0,H0,G0],nil,nil],Pu,Pu_new),
	writeln(Pu_new),
	
	% lancement de Aetoile
	writeln('Aetoile'),
	aetoile(Pu_new, Pf_new, Q),

	% affichage de la solution
	writeln('Solution'),
	affiche_solution(Pf_new, Pu_new, []).



%*******************************************************************************

% on peut l’afficher
affiche_solution(_,_,[S]):-initial_state(S).
affiche_solution(Pf,Pu,[]):-suppress_min(S,Pf,_),
	write_state(S),
	nl,
	affiche_solution(Pf,Pu,[S]).
affiche_solution(Pf,Pu,[S]):-belongs([S,_,Pere, _],Pu),
	write_state(Pere),
	nl,
	affiche_solution(Pf,Pu,[Pere]).


% calculer leur évaluation [Fs, Hs, Gs] connaissant Gu et le coût pour passer de U à S
expand([S,[_,_,G],_,_], L) :-
	findall([S_new, [(Gs + Hs), heuristique(S, Hs), Gs], S, A], rule(A, _, S, S_new), L),
	Gs is (G + 1).
	

% traiter chaque nœud successeur ON EN EST LA ET ON N'Y ARRIVE PAS trop


% si S appartient a Q, on l'oublie 
%		si S appartient a Pu (etat deja rencontre), on compare
%			g(S)+h(S) avec la valeur deja calculee pour f(S)
%			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
%				g et f 
%			sinon on ne touche pas a Pf
%		si S est entierement nouveau on l'insere dans Pf et dans Ps


% si S est connu dans Q alors oublier cet état (S a déjà été développé)
loop_successors([[S, _, _, _]|Rest], Q, Pu, Pf, Pu_new, Pf_new) :-
	writeln('loop_successors1'),
	write('S = '), write(S), nl,
	write('Q = '), write(Q), nl,
	belongs([S,_,_,_],Q),
	writeln('S appartient a Q'),
	loop_successors(Rest, Q, Pu, Pf, Pu_new, Pf_new).

% si S est connu dans Pu alors garder le terme associé à la meilleure évaluation  (dans Pu et dans Pf)
loop_successors([[S, [_,H,G], Pere, A]|Rest], Q, Pu, Pf, Pu_new, Pf_new) :-
	writeln('loop_successors2'),
	write('S = '), write(S), nl,
	write('Pu = '), write(Pu), nl,
	write('Pf = '), write(Pf), nl,
	suppress([S, [F1,_,_], Pere, A], Pu, Pu_new),
	writeln('S suppress de Pu'),
	suppress([_,S], Pf, Pf_new),
	writeln('S suppress de Pf'),
	% comparer G + H à F1
	(G + H < F1 -> 
		% si G + H < F1 alors on garde le nouveau terme
		writeln('G + H < F1'),
		insert([[G+H,H,G],S],Pf,Pf_new),
		insert([S,[G+H,H,G],Pere,A],Pu,Pu_new)
	;
		% sinon on garde le terme deja connu
		writeln('G + H >= F1'),
		Pf_new = Pf,
		Pu_new = Pu
	),
	writeln('Pu_new'),
	loop_successors(Rest, Q, Pu, Pf, Pu_new, Pf_new).

%		si S est entierement nouveau on l'insere dans Pf et dans Pu
% sinon (S est une situation nouvelle) il faut créer un nouveau terme à insérer dans Pu (idem dans Pf)
loop_successors([[S, [F,H,G], Pere, A]|Rest], Q, Pu, Pf, Pu_new, Pf_new) :-
	writeln('loop_successors3'),
	write('S = '), write(S), nl,
	write('Pu = '), write(Pu), nl,
	write('Pf = '), write(Pf), nl,
	insert([S, [F,H,G], Pere, A], Pu, Pu_new),
	writeln('insert S dans Pu'),
	insert([[F,H,G], S], Pf, Pf_new),
	writeln('insert S dans Pf'),
	loop_successors(Rest, Q, Pu_new, Pf_new, Pu_new, Pf_new).


% si Pf et Pu sont vides, il n’y a aucun état pouvant être développé donc pas de solution au problème
aetoile(nil, nil, _) :-
	nl,writeln('PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !').



% sinon
aetoile(Pu, Pf, Q) :-

	% on enlève le nœud de Pf correspondant à l’état U à développer (celui de valeur F minimale) et on enlève aussi le nœud frère associé dans Pu
	writeln('Suppression du noeud'),
	write('Pu : '),writeln(Pu),
	write('Pf : '),writeln(Pf),
	write('Pu_new : '),writeln(Pu_new),
	write('Pf_new : '),writeln(Pf_new),
	write('S : '),writeln(S),
	write('F : '),writeln(F),
	write('H : '),writeln(H),
	write('G : '),writeln(G),
	suppress_min([[F,H,G],S], Pf, Pf_new),
	writeln('Suppression du frère'),
	suppress([S, [F,H,G], _, _], Pu, Pu_new),

	% développement de U

	% déterminer tous les nœuds contenant un état successeur S de la situation U et calculer leur évaluation [Fs, Hs, Gs] (prédicat expand)
	% connaissant Gu et le coût pour passer de U à S.
	writeln('Expansion'),
	expand([S,[_,_,G],_, _], L),
	
	% traiter chaque nœud successeur (prédicat loop_successors)
	writeln('Traitement des successeurs'),
	loop_successors(L, Q, Pu, Pf, Pu_new, Pf_new),

	% U ayant été développé et supprimé de P, il reste à l’insérer le nœud [U,Val,…,..] dans Q
	writeln('Insertion du noeud'),
	insert([_,_, S, A], Q, Q_new),
	write('Action: '), write(A), nl,

	% Appeler récursivement aetoile avec les nouveaux ensembles Pf_new, Pu_new et Q_new
	writeln('Appel recursif'),
	aetoile(Pu_new, Pf_new, Q_new).

% si le nœud de valeur F minimum de Pf correspond à la situation terminale, alors on a trouvé une solution et on peut l’afficher
aetoile(Pu, Pf, _) :-
	writeln('Solution trouvee'),
	final_state(Fin),
	writeln(Fin),
	suppress_min([_,Fin], Pf, _),
	writeln('Suppression'),
	affiche_solution(Pu, Pf, []),
	writeln('AFFICHAGE').