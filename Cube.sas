/*---------------------------------------------------------------------------------*/
/* La macro CUBE permet le tirage d'échantillons équilibrés selon la méthode       */
/* du cube proposée par Jean-Claude DEVILLE et Yves TILLE.                         */
/*---------------------------------------------------------------------------------*/ 
/* Generation d'un vecteur _V_ presque quelconque                                  */
/* Projection de _V_ sur le sous espace des contraintes                            */
/* Calcul des Lambda1 & Lambda2                                                    */
/* Choix probabiliste de la nouvelle direction                                     */
/* Sélection d'un ou plusieurs individus                                           */
/*   F TARDIEU : 30/07/2001                                                        */ 
/*---------------------------Modification du 26/12/2002----------------------------*/
/* Pour éviter de calculer le rang de la matrice des contraintes à chaque          */
/* itération de la phase de vol :                                                  */  
/*   Au lancement de la phase de vol, on utilise le nombre de contraintes          */ 
/*   (qui est supérieur ou égal au rang de la matrice des contraintes),            */
/*   au lieu du rang de la matrice des contraintes, dans la condition d'arret      */
/*   de la boucle principale ( nombre d'individus restants > _Rang_ ).             */
/*   Ensuite, avant toute sortie de la phase de vol (qui pourrait etre             */
/*   prématurée car on utilise un _Rang_ supérieur ou égal au rang de la           */
/*   matrice des contraintes), on calcule le rang de la matrice des contraintes    */
/*   et on le stocke dans _Rang_.                                                  */ 
/*---------------------------Modification du 05/03/2003----------------------------*/
/* Amélioration proposéee par Guillaume Chauvet(Maitrise d'oeuvre méthodologique   */
/* du RRP) de la méthode de recherche directe d'un vecteur du noyau de la          */
/* matrice des contraintes développée par Pascal Ardilly.                          */
/*   Dans la boucle principale, on recherche un vecteur du noyau de la matrice     */
/*   A des contraintes (p,N) de la façon suivante :                                */ 
/*		S'il reste plus que p individus (N > p) :                                  */
/*   	  1. On conserve comme inconnues les p premières composantes du vecteur    */  
/*           du noyau, la (p+1)ème étant fixée à 1, les (N-p-1) dernières à 0, et  */
/*           on résoud, si c'est possible, le système linéaire de matrice B (p,p). */ 
/*  	  2. Si le déterminant de ce système est nul, on choisit un vecteur parmi  */
/*           les solutions du système homogène de matrice B, puis on complète ce   */
/*           vecteur par des 0 pour former un vecteur du noyau de A.               */
/*		S'il ne reste pas plus que p individus (N <= p) :                          */
/*		     Comme Rang(A)< N (condition remplie durant toute la phase de vol),    */
/*           la résolution du système homogène de matrice A fournit un vecteur     */
/*		     du noyau de A.                                                        */ 
/*   La modif du 26/12/2002 est corrigée pour prendre en compte le cas N <= p      */
/*   dans lequel la majoration de rang(A) par p ne permettrait pas de commencer    */
/*   la phase de vol.                                                              */ 
/*---------------------------Modifications du 14/03/2003---------------------------*/
/* Comme _Metric_ est une matrice colonne, composée de 1, qui intervenait          */
/* uniquement comme facteur multiplicatif, les instructions la contenant sont      */
/* modifiées ou mises en commentaires (l'instruction d'affectation, &Metri=1,      */
/* devenue inutile a été ensuite mise en commentaire).                             */
/* Le nombre de contraintes (p = NCOL(_Contr_) calculé avant le début du vol)      */
/* étant constant durant la phase de vol, deux instructions inutiles de calcul et  */
/* d'affectation de ce nombre sont mises en commentaires dans la boucle principale.*/ 
/*---------------------------Modification  du 24/04/2003---------------------------*/
/* A la fin de chaque itération de la boucle principale, _Xdilat_ est déterminée,  */
/* comme l'est _Contr_, par extraction à partir de sa version précédente (au lieu  */
/* d'etre recalculée à partir de _Pi_ et de _Contr_).                              */ 
/*---------------------------Modification  du 17/10/2003---------------------------*/
/* CUBE n'échantillonnant que les individus ayant o<pi<1, en fin de traitement     */
/* on intègre dans l'échantillon les individus ayant pi=1 (en affectant la valeur 1*/
/* aux variables Sortie, Pistar et Pond).                                          */
/*---------------------------Modifications du 20/10/2003---------------------------*/
/* Suppression du paramètre Metri. Controle de la présence des paramètres          */
/* obligatoires et de la numéricité des variables devant etre numériques.          */
/* Controle du contenu des paramètres Atter et Cout.                               */
/*---------------------------Modification  du 23/10/2003---------------------------*/
/* Si tous les individus ont pu etre échantillonnés durant la phase de vol (cas    */
/* Yx=0) il faut aussi actualiser les matrices de travail, notamment _P_ et Reste  */
/* qui constituent, par la suite, les tables Pistar et Reste formant ensuite la    */
/* table Residu. Sinon, les individus sur lesquels on a statué lors de la dernière */
/* itération ont, lorsque l'on réunit les sorties, une valeur de Pistar qui peut   */
/* etre très proche de 0 ou 1, mais sans etre égale à 0 ou 1, provoquant en cela   */
/* des anomalies dans le commentaire (valeurs erronées pour "Somme des Pika" et    */
/* "Nb d'individus restants").                                                     */
/*---------------------------Modification  du 30/10/2003---------------------------*/
/* Au cas où il n'y aurait pas de phase d'atterrissage, on le signale dans l'output*/
/* par le message "Il n'y a pas de phase d'atterrissage" qui figurait déjà dans la */
/* LOG.                                                                            */
/*---------------------------Modifications du 07/11/2003---------------------------*/
/* Modification des matrices _Denomi_ et _Metrick intermédiaires dans le calcul du */
/* coût des échantillons (options B et E).                                         */
/* Pour l'option E, la table Cont contenant la matrice _Contr_ en fin de vol est   */
/* remplacée par la table Xdilat qui contient la matrice _Xdilat_ en fin de vol, et*/
/* la table Metrick permet de stocker la matrice _Metrick.                         */
/*---------------------------Modifications du 13/11/2003---------------------------*/
/* Implantation d'un mode de calcul plus rapide du rang d'une matrice.             */
/* Dans la boucle principale, on supprime la mise à jour de la matrice _Contr_ des */
/* contraintes non dilatées, car dans tous les traitements ultérieurs c'est la     */
/* matrice _Xdilat_ des contraintes dilatées par le poids de chaque individu qui   */
/* est utilisée (meme chose pour la matrice _Pi_ devenue inutile).                 */
/* Suppression des compteurs  _DimP_, _DimS_, _SumP_ et _SumPi_ inutilisés par la  */
/* suite.                                                                          */
/*---------------------------Modifications du 11/02/2004---------------------------*/
/* 1. Dans la macro d'atterrissage selon les options B et C (ex E) %ATTERBC        */
/*    l'utilisation de tables à la place de matrices permet de diminuer l'espace   */
/*    mémoire nécessaire et de réduire considérablement le temps de calcul (ainsi, */
/*    avec 256 Mo on peut traiter jusqu'à 500 000 échantillons possibles, alors    */
/*    qu'en pur IML on était limité à 125 000 échantillons).                       */
/* 2. Dans la macro %Atter qui résoud le programme linéaire (options B et C)       */
/*    un test de non nullité est remplacé par un test de comparaison à 10E-10.     */
/*    Sans effet sur l'option B (car la valeur testée est alors toujours nulle)    */
/*    cette modification diminue de plus d'un tiers l'espérance du coût, selon     */
/*    le plan de sondage solution, en cas d'utilisation de l'option C (ex E),      */
/*    car, auparavant, on s'arretait à la phase 1 de la résolution du programme    */
/*    linéaire sans aller jusqu'à la solution optimale.                            */
/*---------------------------Modifications du 16/02/2004---------------------------*/
/* Le fichier Sortie contient l'échantillon. Le fichier complet (base de sondage   */
/* complétée par les trois variables Sortie, Pistar et Pond) a pour nom :          */
/* Datafic2_Sortie où Datafic2 = Datafic moins l'éventuelle référence à une        */
/* librairie (libname), de façon à se trouver toujours dans la Work.               */
/* La durée réelle d'exécution de la macro est indiquée dans la Log.               */
/*---------------------------Modifications du 17/02/2004---------------------------*/
/* Modifications du commentaire et des sorties graphiques proposées et programmées */
/* par Sylvie Rousseau : affichage du nombre d'unités échantillonnées et du        */
/* lancement ou non de la phase d'atterrissage, amélioration de la présentation du */
/* commentaire et des légendes des sorties graphiques.                             */
/*---------------------------Modification  du 18/02/2004---------------------------*/
/* Vérification qu'aucune variable d'équilibrage ne figure en double dans Contr.   */
/*---------------------------Modifications du 01/03/2004---------------------------*/
/* Ajout des controles suivants :                                                  */
/* - aucune des variables citées en paramètre ne doit présenter de valeur manquante*/
/* - controle de la valeur du paramètre Atter.                                     */
/* - toutes les probabilités d'inclusion doivent appartenir au segment [0,1].      */
/* - au moins une probabilité d'inclusion doit appartenir à l'intervalle ]0,1[ car */
/*   dans le cas contraire (toutes probas égales à 0 ou à 1) CUBE n'est pas utile. */
/*---------------------------Modifications du 04/03/2004---------------------------*/
/* Prise en compte des cas suivants :                                              */
/* - aucun individu n'est échantillonné à la fin de la phase de vol.               */
/* - aucun individu n'est échantillonné durant la phase d'atterrissage.            */
/*---------------------------Modification  du 08/03/2004---------------------------*/
/* Inactivation de l'option Atter=Z arretant la macro à la fin de la phase de vol. */
/*---------------------------Modification  du 10/03/2004---------------------------*/
/* L'utilisation de la fonction de coût CV n'est possible que si aucun vrai total  */
/* n'est égal à zéro. Dans le cas contraire, un message d'erreur est donc affiché  */
/* si la phase d'atterrrissage est nécessaire avec Atter=(B ou C) et Cout=CV.      */
/* Ce message indique à l'utilisateur la ou les variables de vrai total nul.       */
/*---------------------------Modification  du 19/03/2004---------------------------*/
/* Pour éviter la présence éventuelle d'un deuxième point rouge dans le graphique 2*/
/* à cause d'un échantillon ayant la meme proba que l'échantillon tiré (suite à un */
/* merge sur la proba des échantillons), la variable Pris de l'échantillon tiré est*/
/* affectée dans %TIR_LP.                                                          */
/*---------------------------Modification  du 22/03/2004---------------------------*/
/* Dans le commentaire, ajout de l'option d'atterrissage utilisée s'il y a eu      */
/* lancement de la phase d'atterrissage.                                           */
/*---------------------------Modification  du 05/04/2004---------------------------*/
/* Dans le commentaire, ajout de la fonction de coût utilisée s'il y a eu lancement*/
/* de la phase d'atterrissage selon les options B ou C.                            */
/*---------------------------Modification  du 06/04/2004---------------------------*/
/* Suppression de l'option lib=work des Proc Datasets (c'est l'option par défaut). */
/* But : éviter le plantage des options B et C lorsque la librairie contenant le   */
/* catalogue des macros compilées a USER pour libref (dans ce cas très particulier */
/* tous les fichiers temporaires, y compris les tables créées en sortie, sont dans */
/* la librairie de libref USER, ce qui provoque un plantage car une table attendue */
/* dans la work n'y est pas).                                                      */
/*---------------------------Modifications du 13/04/2004---------------------------*/
/* Ajout d'un controle sur les paramètres Id et Pi (ils ne doivent contenir qu'une */
/* seule variable).                                                                */
/* Les modalités de la variable Id doivent etre uniques.                           */
/*---------------------------Modifications du 29/10/2004---------------------------*/
/* Suite à des plantages survenant parfois avec l'option A lors de la 2ème création*/
/* de la table IdEch (identifiants des individus retenus) en fin d'atterrissage :  */
/* lorsque l'option A est utilisée, il n'y a plus création de la table IdEch à la  */
/* fin de la phase de vol (cette table n'étant indispensable que pour les options  */
/* B et C).                                                                        */
/* Afin de ne plus avoir à trier les observations de la table Datafic contenant    */
/* la base de sondage, selon l'identifiant Id :                                    */
/* 	  Dans %Sorties_avec_residu et %Sorties_sans_residu on utilise la table        */
/*    BaseTriParId, créée à la fin des controles préliminaires au lancement de     */
/*    CUBE, pour controler que Id est à valeurs uniques sur Datafic.               */
/*-------------------------Compilation en V9 le 31/01/2006-------------------------*/
/* Compilation en V9.1, sans modification du source de la macro, sauf pour mise à  */
/* jour de la date et de la version de compilation dans le bandeau de la log       */
/* contenant le compte rendu d'exécution.                                          */
/*---------------------------------------------------------------------------------*/

%MACRO CUBE  (Datafic=,
              Id=,
              Pi=,
			  Pond=pond,
              Contr=,
              Sortie=,
              Cout=CV,
              Atter=B,
			  Comment = oui)/store  ;

/* Afin d'améliorer les performances de la phase d'atterrissage, la version du       */
/* 30 01 2004 utilise abondamment des tables SAS (macros Atterbc et Atter).          */
/* Dans ce cas un gain de temps supplémentaire est obtenu avec l'option compress=yes.*/
options nomprint nosymbolgen nonotes label compress=yes; 

/*__________ Est-ce que les paramètres obligatoires sont renseignés _______*/
%IF &Datafic EQ %THEN %DO; %PUT; %PUT "LE PARAMETRE DATAFIC N'EST PAS RENSEIGNE"; %PUT; %END;
%IF &Id      EQ %THEN %DO; %PUT; %PUT "LE PARAMETRE ID N'EST PAS RENSEIGNE"; %PUT; %END;
%IF &Pi      EQ %THEN %DO; %PUT; %PUT "LE PARAMETRE PI N'EST PAS RENSEIGNE"; %PUT; %END;
%IF &Contr   EQ %THEN %DO; %PUT; %PUT "LE PARAMETRE CONTR N'EST PAS RENSEIGNE"; %PUT; %END;
%IF &Sortie  EQ %THEN %DO; %PUT; %PUT "LE PARAMETRE SORTIE N'EST PAS RENSEIGNE"; %PUT; %END;

%IF &Datafic EQ  OR  &Id EQ  OR  &Pi EQ  OR  &Contr EQ  OR  &Sortie EQ  %THEN %GOTO Fini ;
       
/*__________ Est-ce que le paramètre Sortie est valide ____________________*/
%IF  %INDEX(&Sortie,.) NE 0  %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "*** LE PARAMETRE SORTIE NE DOIT PAS CONTENIR DE POINT            ***";
	%PUT "*** CAR IL S'AGIT AUSSI DU NOM D'UNE VARIABLE DE LA TABLE SORTIE ***";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

/*__________ Est-ce que le paramètre Atter est valide _____________________*/
%IF  %UPCASE(&ATTER) NE A  AND  %UPCASE(&ATTER) NE B  AND  %UPCASE(&ATTER) NE C  /* AND  
	 %UPCASE(&ATTER) NE Z  */   %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "************* LA VALEUR &ATTER DU PARAMETRE ATTER N'EST PAS VALIDE *************";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

/*__________ Est-ce que le paramètre Comment est valide ___________________*/
%IF  %UPCASE(&COMMENT) NE OUI  AND  %UPCASE(&COMMENT) NE GRAPHE  AND    
	 %UPCASE(&COMMENT) NE NON  %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "************* LA VALEUR &COMMENT DU PARAMETRE COMMENT N'EST PAS VALIDE *********";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

/*________Si Atter=B ou C, est-ce que le paramètre Cout est valide ________*/
%IF  (%UPCASE(&ATTER) = B  OR  %UPCASE(&ATTER) = C)  AND
	  %UPCASE(&COUT) NE CV  AND  %UPCASE(&COUT) NE DIST  %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "************* LA VALEUR &COUT DU PARAMETRE COUT N'EST PAS VALIDE *************";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

/*________Le paramètre Id ne doit contenir qu'une seule variable __________*/
%IF %INDEX(&Id,%SCAN(&Id,2)) NE 0 %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "********* LE PARAMETRE ID NE DOIT CONTENIR QU'UNE SEULE VARIABLE *************";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

/*________Le paramètre Pi ne doit contenir qu'une seule variable __________*/
%IF %INDEX(&Pi,%SCAN(&Pi,2)) NE 0 %THEN
	%DO;
		%DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
	%PUT "********* LE PARAMETRE PI NE DOIT CONTENIR QU'UNE SEULE VARIABLE *************";
        %DO n=1 %TO 5 ;
            %PUT  ;
        %END ;
		%GOTO Fini ;
	%END;

	/*________________ Est-ce que la table et ses variables existent __________*/ 
%LOCAL I Kod chain1 blanc1 V_1 airc erreur NumVar;
/*___________________________________ Existence d'une table */
%IF %SYSFUNC(EXIST(&Datafic)) %THEN
	%DO ;
/*_________________Datafic2 = Datafic sans la référence éventuelle à une librairie */
/*                 pour création du fichier de sortie complet dans la Work         */ 
		%LET Datafic2 = %SUBSTR(&Datafic,%INDEX(&Datafic,.)+1) ;

/*______________________ Repérage et decompte des variables */
		%LET Kod = %SYSFUNC(OPEN(&Datafic)) ;
		%LET Chain1 = %CMPRES(&Contr &Pi &Id) ;
		%LET Blanc1 = %INDEX(&Chain1,%STR( )) ;
		%LET V_1    = %SUBSTR(&Chain1,1,%EVAL(&Blanc1-1)) ;
        %LET I      = 1 ;
        %DO %WHILE (%EVAL(&&Blanc&I) > 0 ) ;
           	%LET I       = %EVAL(&I + 1) ;
            %LET J       = %EVAL(&I - 1) ;
            %LET Chain&i = %SUBSTR(&&Chain&j,%EVAL(&&Blanc&j+1))  ;
            %LET Blanc&i = %INDEX(&&Chain&i,%STR( )) ;
            %IF &&Blanc&i > 0
            	%THEN %LET V_&i    = %SUBSTR(&&Chain&i,1,%EVAL(&&Blanc&i-1)) ;
                %ELSE %LET V_&i    = %SUBSTR(&&Chain&i,1) ;
		%END ;
/*_____________ Existence des variables des paramètres dans la table ____________________*/
		%LET erreur = 0 ;
		%DO Nb_var = 1 %TO &I ;
        	%LET NumVar =  %SYSFUNC(VARNUM(&Kod,&&V_&nb_Var)) ;
        	%IF &NumVar = 0  %THEN
            	%DO ;
					%LET erreur = 1 ;
                    %DO n=1 %TO 5 ;
                       %PUT  ;
                    %END ;
		%PUT "******** LA VARIABLE &&V_&nb_var DE LA TABLE &Datafic N'EXISTE PAS ********";
                    %DO n=1 %TO 5 ;
                       %PUT  ;
                    %END ;
				%END ;
        	%ELSE
/*_____________ Toutes les variables sauf l'identifiant doivent etre numériques _________*/
				%DO;
            	%IF &Nb_var < &I  AND  %SYSFUNC(VARTYPE(&Kod,&NumVar)) NE  N  %THEN   
					%DO;
						%LET erreur = 1 ;
                   		%DO n=1 %TO 5 ;
                   			%PUT  ;
                   		%END ;
		%PUT "***** LA VARIABLE &&V_&nb_var DE LA TABLE &Datafic N'EST PAS NUMERIQUE *****";
                	   	%DO n=1 %TO 5 ;
                   			%PUT  ;
                   		%END ;
					%END;
/*_____________ Aucune variable ne doit figurer en double dans les contraintes __________*/
            	%IF &Nb_var < %EVAL(&I - 2)    %THEN
					%DO k=%EVAL(&Nb_var + 1) %TO %EVAL(&I - 2);
						%IF %UPCASE(&&V_&Nb_var) = %UPCASE(&&V_&k)  %THEN
							%DO;
								%LET erreur = 1 ;
                   				%DO n=1 %TO 5 ;
                   					%PUT  ;
                   				%END ;
%PUT "***** LA VARIABLE &&V_&nb_var FIGURE PLUSIEURS FOIS DANS LE PARAMETRE CONTR ****";
%PUT "***** LES NOMS DES VARIABLES D'EQUILIBRAGE DOIVENT ETRE TOUS DISTINCTS ****";
                	   			%DO n=1 %TO 5 ;
                   					%PUT  ;
                   				%END ;
							%END;
					%END;
				%END;
/*_____________ Stockage du type de la variable identifiant (pour test valeur manquante) */
            	%IF &Nb_var = &I  %THEN	%LET Type_Id = %SYSFUNC(VARTYPE(&Kod,&NumVar)) ;
		%END ;

/*_____________ Stockage du nombre d'observations de Datafic                             */
/*_____________ Pour vérification que la variable Id est à valeurs uniques sur Datafic   */
		%LET NOBS = %SYSFUNC(ATTRN(&Kod,NOBS));
		%LET AIRC = %SYSFUNC(CLOSE(&Kod)) ;

/* Le 29 10 2004 : on remplace temp par un nom plus parlant (BaseTriParId) pour une      */
/*                 utilisation dans %Sorties_avec_residu et %Sorties_sans_residu         */
/*		PROC SORT DATA=&Datafic OUT=temp NODUPKEY; BY &Id; RUN;                          */
/*		%LET Ktri = %SYSFUNC(OPEN(Temp)) ;                                               */

		PROC SORT DATA=&Datafic OUT=BaseTriParId NODUPKEY; BY &Id; RUN;
		%LET Ktri = %SYSFUNC(OPEN(BaseTriParId)) ;
		%IF &Ktri %THEN 
			%DO;
				%LET NOBSTRI = %SYSFUNC(ATTRN(&KTri,NOBS));
				%LET RC = %SYSFUNC(CLOSE(&KTri));
				%IF &NOBS NE &NOBSTRI %THEN
							%DO;
								%LET erreur = 1 ;
                   				%DO n=1 %TO 5 ;
                   					%PUT  ;
                   				%END ;
%PUT "***** CERTAINS INDIVIDUS DE LA TABLE &Datafic ONT LE MEME IDENTIFIANT ****";
                	   			%DO n=1 %TO 5 ;
                   					%PUT  ;
                   				%END ;

/* Le 29 10 2004 : la table Temp renommée en BaseTriParId n'est détruite qu'en cas       */
/*				   d'anomalie sur Id, afin de servir dans %Sorties_avec_residu et        */
/*                 %Sorties_sans_residu si pas d'anomalie sur Id.                        */  
							 	PROC DATASETS  NOLIST ;
  									DELETE BaseTriParId /  MEMTYPE=DATA ;
								RUN ;                                                
								QUIT ;
							%END;
			%END;

/* Mises en commentaire le 29 10 2004       */
/*		PROC DATASETS  NOLIST ;             */
/*  		DELETE Temp /  MEMTYPE=DATA ;   */
/*		RUN ;                               */                                                
/*		QUIT ;                              */

		%IF &erreur = 1 %THEN %GOTO Fini ;
	%END ;
/*________________________________ Si la table n'existe pas */
%ELSE 	%DO ;
           	%DO n=1 %TO 5 ;
               	%PUT ;
            %END ;
           	%PUT "LA TABLE &Datafic N'EXISTE PAS" ;
            %DO n=1 %TO 5 ;
               	%PUT ;
            %END ;
       		%LET AIRC = %SYSFUNC(CLOSE(%SYSFUNC(EXIST(&Datafic)))) ;
			%GOTO Fini ;
		%END ;
/*________________________ Destruction préventive des Work.Data
                 								qui vont servir   */

/* Le 07 11 2003, on remplace la table Cont qui n'est utilisée que par ATTERBC      */
/* par la table Xdilat qui remplace Cont dans ATTERBC et on ajoute la table Metrick.*/
 
PROC DATASETS  NOLIST ;
  DELETE Xdilat Metrick Haine Saplane
         Alt One Tone IdEch &Sortie &Datafic2._&Sortie _Proba_ _Tutti_
         residu PiStar Staup /  MEMTYPE=DATA ;
RUN ;                                                
QUIT ;

/*______________________ On stocke l'heure de début                */
DATA heure; 
	debut=time();
RUN;

/*______________________ On ne travaille que sur les PROBA valides */

%LET MISSING = 0;
%LET PI_INVALID = 0;
%LET NOBS = 0;
 
DATA saplane ;
  SET &Datafic ;

/* Le 27 02 2004 : on teste si les variable spécifiées sont à valeur manquante */
  	IF Symget('Type_Id') = 'N' THEN
  		DO; IF &Id = .   THEN CALL SYMPUT('MISSING',1); END;
  	ELSE
  		DO; IF &Id = ' ' THEN CALL SYMPUT('MISSING',1); END;

  	%DO j=1 %TO %EVAL(&I - 1);
  		IF &&V_&j = .   THEN CALL SYMPUT('MISSING',1);
  	%END;

/* Le 01 03 2004 : on teste la validité des probabilités d'inclusion           */
	IF &Pi < 0 OR &Pi > 1 THEN CALL SYMPUT('PI_INVALID',1);

/* Modification du 14 03 2003 */
/*&Metri = 1 ;                */
/* Le 27 02 2004 : Remplacement du WHERE par un IF pour faire porter, aussi sur 
   les observations non écrites dans saplane, les tests des valeurs manquantes */
/*  WHERE 0 < &Pi < 1 ;                                                        */

  IF 0 < &Pi < 1 ;

/* Le 01 03 2004 : on compte le nombre d'observations de la table saplane      */
  CALL SYMPUT('NOBS',_N_) ;
RUN ;

%IF &MISSING = 1 %THEN
	%DO;
       	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
%PUT "VALEUR MANQUANTE DETECTEE POUR LES PROBABILITES D'INCLUSION OU LES VARIABLES D'EQUILIBRAGE";
%PUT "IL FAUDRAIT VERIFIER LA BASE DE SONDAGE";
 	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
		%GOTO Fini;
	%END;

%IF &PI_INVALID = 1 %THEN
	%DO;
       	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
%PUT "*** PRESENCE D'UNE PROBABILITE D'INCLUSION N'APPARTENANT PAS AU SEGMENT [0,1] ***";
       	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
		%GOTO Fini;
	%END;

%IF &NOBS = 0 %THEN
	%DO;
       	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
%PUT "*** AUCUNE PROBABILITE D'INCLUSION N'APPARTIENT A L'INTERVALLE ]0,1[ ***";
       	%DO n=1 %TO 5 ;
           	%PUT ;
        %END ;
		%GOTO Fini;
	%END;

PROC IML ;
/*___________________On construit les matrices qui vont nous servir*/

USE saplane  ;
  READ ALL VAR {&Contr} INTO  _Contr_  ;
/*     Modification du 14 03 2003        */
/*READ ALL VAR {&Metri} INTO  _Metric_ ; */

  READ ALL VAR {&Pi}    INTO  _P_      ;
/*READ ALL VAR {&Pi}    INTO  _Pi_     ; en commentaire le 26 02 2004 pour cause        */
/*                                       de double emploi avec l'instruction précédente */

  READ ALL VAR {&Id}    INTO  _Id_     ;

/*Y2  = J(NCOL(_CONTR_),1,0); Instruction inutile supprimée le 07/11/2003*/

/*              Modification du 14 03 2003           */
/*_Xdilat_ = ((_Metric_##0.5)#(_PI_##(-1)))#_Contr_; */

/*_Xdilat_ = (_PI_##(-1))#_Contr_; le 26 02 2004 on remplace _PI_ par _P_               */
/*                                 vecteur des probabilités d'inclusion                 */
_Xdilat_ = (_P_##(-1))#_Contr_;

%IF %UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C   %THEN 
  %DO ;
 
  /*Dénominateur de la fonction de coût des options B et E */
  /* ______________ Cout = CV _____________________________*/
  /*Modification du 07 11 2003 : détermination d'une       */
  /*matrice ligne contenant les totaux de chaque contrainte*/        
  /*_Denomi_ = SUM(T(_Contr_)*SHAPE(1,NROW(_Contr_),1)) ;  */
  	%IF %UPCASE(&Cout) = CV %THEN  	 %DO;                  
    	_Denomi_ = _Contr_[+,] ;     %END;

  /*Matrice intermédiaire fonction de coût des options B et E 
    deuxième version ......................................*/
  /* ______________ Cout = DIST ___________________________*/
  /*Modification du 07 11 2003 : c'est la matrice          */
  /*_Xdilat_` (=A) qu'il faut utiliser ici.                */        
  /*_Metrick = GINV(_Contr_`*_Contr_) ;                    */
  	%IF %UPCASE(&Cout) = DIST %THEN     	  %DO;             
    	_Metrick = GINV(_Xdilat_`*_Xdilat_) ; %END; 

  %END ;

/*_________________________________ modif du 26/12/2002 */
/* _Rang_   = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;   */  
/*                                version du 05/03/2003 :
    on prend en compte le cas : Nombre d'individus (=Yx) <= Nombre de contraintes (=p) */

Yx = NROW(_Id_) ;
 p = NCOL(_Contr_);
 
/* Si Yx > p on utilise p = Ncol(_Contr_) comme majorant du Rang       
             pour éviter d'avoir à calculer le rang                  */
IF Yx > p
	THEN  _Rang_ = p ;

/* sinon (Yx<=p) il faut calculer le rang pour pouvoir 
	             éventuellement entrer dans la boucle principale     */

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet */
/*  ELSE  _Rang_ = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;                   */ 
	ELSE	DO;
				_Noyau_ = HOMOGEN(BLOCK(_Xdilat_,0)) ;
				_Rang_  = NROW(_Noyau_) - NCOL(_Noyau_) ;
		  	END;

/* Le 05 03 2004 : Initialisation de la matrice somme nécessaire si on passe */
/* à l'atterrissage sans aucune itération de la boucle principale            */
somme   = SUM(_P_)         ;                         
			
/*_____________________________________________ La boucle principale */

DO WHILE ( Yx > _Rang_ ) ;

_dim_    = NROW(_Xdilat_)   ;

/* Instructions mises en commentaire le 13/11/2003       */ 
/* _DimP_   = NROW(_P_)        ;                         */ 
/* _DimS_   = NROW(S)          ;                         */
/* _SumP_   = SUM(_P_)         ;                         */
/* _SumPi_  = SUM(_Pi_)        ;                         */

/*  Modification du 14 03 2003   */
/* _NbCon_  = NCOL(_Contr_)    ; */

/*_________________________DEBUT DE LA MODIF DU 05 03 2003______________________________*/

/*_________________________On recherche directement un vecteur du noyau 
						   de la matrice (p,N) des contraintes A = _Xdilat_`            */
A = _Xdilat_`;
/* Modification du 14 03 2003   */
/* p = _NbCon_ ;                */

N = _dim_ ;

IF Yx > p THEN             /*____________________Si Yx = N > p__________________________*/ 
	DO; 
                           /* On fixe à 1 la (p+1) ème composante (et à 0 les N-p-1 autres)
                           du vecteur du noyau 
                          (ses p premières composantes formant un vecteur inconnu delta)*/

		un_à_p = DO(1,p,1);/* vecteur ligne ayant p composantes de 1 à p --> (1 2 ... p)*/
		B = A[,un_à_p];    /* B = p premières colonnes de A                             */
		det_B = det(B);    /* calcul du déterminant de B                                */

                           /* si un vecteur du noyau peut etre trouvé par cette méthode */

		IF det_B > 0.0000001 | det_B < -0.0000001 THEN 
			DO;
				C = A[,p+1];           /* C = (p+1) ème colonne de A                    */

				delta = SOLVE(B,-C);   /* on résoud B * delta = -C
	                                   SAS conseillant d'utiliser SOLVE plutot que INV  */
				fin = J(N-p,1,0);
				fin[1,1] = 1;
    			_Proj_ = delta // fin; /* concaténation verticale pour compléter delta  */
  			END;

                           /* si cette tentative a échoué (B supposée non inversible), 
                           on utilise la fonction HOMOGEN pour trouver un vecteur  
						   du noyau de B (on peut utiliser HOMOGEN car rang(B) < p )    */ 
		ELSE 
			DO;
				_SOL_ = HOMOGEN(B);
				IF NCOL(_SOL_) > 0 THEN	/* On s'assure que l'utilisation de la fonction 
				                        HOMOGEN est licite i.e. que B est non inversible*/
					DO;		                                    
						w = _SOL_[,1];	
						_fin_ = J(N-p,1,0);    /* On complète ce vecteur par des 0      */   
						_proj_ = w // _fin_;
		  			END;

				ELSE	    /* Si, malgré le test sur det(B), IML considère 
							que B est inversible, on reprend la méthode précédente     */ 
					DO;

						C = A[,p+1];           /* C = (p+1) ème colonne de A           */

						delta = SOLVE(B,-C);   /* on résoud B * delta = -C             */
						fin = J(N-p,1,0);
						fin[1,1] = 1;
    					_Proj_ = delta // fin; /* concaténation verticale              */
					END;
			END;
	END;

ELSE						/*_________________________Si Yx = N <= p__________________
    					 	On a Rang(A)< Yx <= p, on peut donc calculer HOMOGEN(A) 
							(A étant de dimension p,Yx)                                 */
	_Proj_ = HOMOGEN(A)[,1];

/*_________________________FIN DE LA MODIF DU 05 03 2003________________________________*/

/*______________________On calcule les Lambda1 et lambda2 postulants */
IF MAX(_proj_)>0 THEN
    DO;
      _bzh_ = LOC(_proj_>0)                ;
      l11   = (1-_p_[_bzh_])/_proj_[_bzh_] ;
      l21   = _p_[_bzh_]/_proj_[_bzh_]     ;
    END;
    ELSE
    DO;
      l11=9999999999999999999;
      l21=9999999999999999999;
    END;

IF MIN(_proj_)<0 THEN
    DO;
      _bzh_ = LOC(_proj_<0)                     ;
      l22   = (1-_p_[_bzh_])/ABS(_proj_[_bzh_]) ;
      l12   = _p_[_bzh_]/ABS(_proj_[_bzh_])     ;
    END;
    ELSE DO;
     l12=99999999999999999999;
     l22=99999999999999999999;
    END;
/*_________________________________Lambda1 & Lambda2 sont definis*/
l1=MIN(l11//l12);
l2=MIN(l21//l22);
/*________________________Une nouvelle direction est selectionnee*/
IF (UNIFORM(0)<l2/(l1+l2))
  THEN _p_=_p_+_proj_#l1;
  ELSE _p_=_p_-_proj_#l2;
/*___________________________________________________Echantillonnage */
 _Idlig_  = T(DO(1,NROW(_Xdilat_),1)) ;
 IF MAX(_P_) > 0.9999999 THEN
    DO ;
      OuiOui   = _Idlig_[LOC(_p_>0.9999999)];
      S = S//_Id_[OuiOui]  ;
    END ;
/*____________________________________Selection des futurs postulants*/
  IF NCOL(LOC(_p_>  0.0000001 & _p_< 0.9999999)) > 0 THEN 
    DO ; 
      Con_Rest = LOC(_p_>  0.0000001 & _p_< 0.9999999) ;
      Reste    = _Idlig_[Con_Rest];
      _Id_     = _Id_[Reste] ;

/* instruction de mémorisation mise en commentaire le 22/10/03*/
/*    _P2_     = _P_         ;                                */
/*     Modification du 14 03 2003  */
/*    _Metric_ = _Metric_[Reste] ; */

      _P_      = _P_[Reste] ;

/* Instructions mises en commentaire le 13/11/2003       */ 
/*    _Pi_     = _Pi_[Reste] ;                           */
/*    _Contr_  = _Contr_[Reste,] ;                       */

	  somme    = sum(_p_) ;
 	   Yx      = NROW(_Id_) ;

/*     Modification du 14 03 2003                        */ 
/*    _Xdilat_ = ((_Metric_##0.5)#(_PI_##(-1)))#_Contr_; */

/*     Modification du 24 04 2003                        */ 
/*	  _Xdilat_ = (_PI_##(-1))#_Contr_;                   */
	  _Xdilat_ = _Xdilat_[Reste,];

/*______________________________________________________________Modif du 26/12/2002    */ 
/*     _Rang_   = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;                              */
/*  Calcul du rang uniquement pour éviter une éventuelle sortie de boucle prématurée   */
/*  pour cause de rang initial (_Rang_ = Nbre de contraintes) trop élevé               */

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet           */
/*     	IF  Yx <= _Rang_  THEN  _Rang_ = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;       */
		IF  Yx <= _Rang_  THEN  
			DO;
				_Noyau_ = HOMOGEN(BLOCK(_Xdilat_,0)) ;
				_Rang_  = NROW(_Noyau_) - NCOL(_Noyau_) ;
		  	END;
 
    END ;
  ELSE 
	DO ; 
	  Yx=0 ;

/* Modification du 23/10/2003 :
/* Quand il ne reste plus aucun individu à la fin de la phase de vol, les matrices   */
/* sur lesquelles on travaillait doivent etre vides.                                 */
/* Auparavant, ces matrices restaient dans leur état à la fin du vol :               */
/* en particulier, les lignes de _P_ qui se rapportaient aux individus examinés lors */
/* de la dernière itération de la phase de vol n'étaient pas arrondies à 0 ou 1 dans */
/* le fichier en sortie ce qui provoquait des anomalies dans l'affichage de la       */
/* "somme des Pika" et du "Nb d'individus restants" du bilan de l'échantillonnage.   */
	
	  Y = {0} ;
      Reste = LOC(Y) ; 
      _Id_  = LOC(Y) ;
      _P_   = LOC(Y) ;
/* Instruction mise en commentaire le 13/11/2003                */ 
/*    _Contr_ = LOC(Y) ;                                        */
	  somme = 0 ;
	END  ;  

/****************************************************************/
/*										 Fin de la phase de vol */ 
/*									 et de la boucle principale */
/****************************************************************/
END ;
/*_______________________________________ Sauvegardes variées   */

/* Le 16 02 2004 : les tables Pistar et Reste ne sont utiles que 
   s'il reste des individus sur lesquels il faut statuer.
   Dans ce cas, ces 2 tables seront concaténées dans la table 
   Residu durant l'exécution de la macro %Sorties_avec_residu 
   en fin d'atterrissage.
   Sinon, dans les macros d'atterrissage, on passe directement à 
   l'exécution de la macro %Sorties_sans_residu.                */

IF Yx > 0 THEN 
	DO;
		CREATE PiStar VAR{PiStar} ;
		APPEND FROM _P_ ;
		CLOSE PiStar ; 
		CREATE Reste VAR{&Id} ;
		APPEND FROM _Id_ ;
		CLOSE Reste ;
	END;
/* Modification du 07/11/2003 : _Denomi_ n'existe que si Cout=CV*/
/*%IF %UPCASE(&ATTER) = "B" OR %UPCASE(&ATTER) = "C"            */
 
%IF (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C) AND %UPCASE(&Cout) = CV 
  %THEN %DO ;

  /* Le 09 03 2004 : Pour créer la table _Denomi_ il faut aussi 
   qu'aucun vrai total ne soit nul (car le calcul de tous les
   coefficients de variation est alors impossible)              */
			IF NCOL( LOC(_Denomi_ = 0) ) = 0  THEN
				DO; 
					/*CREATE _Denomi_ VAR{_Denom_} ; Correction du 07/11/2003*/
					CREATE _Denomi_ VAR{&Contr} ;
					APPEND FROM _Denomi_ ;
					CLOSE _Denomi_ ;
				END;
			ELSE
				DO;
					CREATE Totaux VAR{&Contr} ;
					APPEND FROM _Denomi_ ;
					CLOSE Totaux ;
				END;	
        %END ;

/* Modification du 07/11/2003 : si Cout = DIST, il faut aussi   */
/* sauvegarder _Metrick afin de pouvoir l'utiliser dans ATTERBC */
/* après etre sorti d'IML                                       */
 
%IF (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C) AND %UPCASE(&Cout) = DIST 
  %THEN %DO ; 
			CREATE Metrick FROM _Metrick;
			APPEND FROM _Metrick;
			CLOSE Metrick ;
        %END ;

/* Correction du 29/10/2004 : afin que lors d'un atterrissage               */
/* selon l'option A, il n'y ait pas 2 écritures trop rapprochées            */  
/* de la table IdEch pouvant provoquer un plantage, on ne crée ici          */
/* (fin de vol)la table IdEch que                                           */
/* 		- s'il n'y a pas d'atterrissage (Yx=0)                              */
/*		- ou, s'il y a atterrissage, seulement pour les options B et C      */
/* et toujours à condition qu'au moins un individu ait été échantillonné    */
/* en vol (ex>0).                                                           */
/* Pour ce faire les instructions suivantes sont mises en commentaires et   */
/* reportées dans le test de Yx=0 qui décide du lancement de l'atterrissage.*/

/*		ex = nrow(S) ;                                                      */ 
/*		IF ex > 0 THEN                                                      */
/* Le 09 03 2004 : Pour ne plus risquer d'interférer avec la table &Sortie
   spécifiée par l'utilisateur, on nomme IdEch, au lieu de &Sortie, la table
   qui contient les identifiants des individus retenus dans l'échantillon */
/*			DO  ;                                                            
/*				CREATE IdEch VAR{&Id};                                      */
/*				APPEND FROM S ;                                             */
/*				CLOSE IdEch   ;                                             */ 
/*			END ;                                                           */

/* Le 29 10 2004 : les tables n'étant utiles que pour les options B et C,   */
/* ne sont créées que si Atter=B ou C                                       */

%IF %UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C %THEN
	%DO; 
		CREATE Haine VAR{Som_P_} ;
		APPEND FROM Somme ;
		CLOSE Haine ;
		Y_Rest = NROW(_Id_) ;
		CREATE Alt VAR{Col1} ;
		APPEND FROM Y_Rest ;
		CLOSE Alt ; 

/* Le 07 11 2003, on remplace la table Cont qui n'est utilisée que par ATTERBC*/
/* par la table Xdilat qui remplace Cont dans ATTERBC.                        */
/*CREATE Cont FROM _Contr_;                                                   */
/*APPEND FROM _Contr_ ;                                                       */ 
/*CLOSE Cont ;                                                                */
		CREATE Xdilat FROM _Xdilat_;
		APPEND FROM _Xdilat_ ;
		CLOSE Xdilat ;
	%END;

ex = nrow(S) ; 

/*_______________________________________ Les options d'atterrissage 
			 ne sont utilisées que si il reste du monde dans l'avion */
IF Yx = 0 THEN 
  	DO ;
  		CREATE Staup VAR{Staup} ;
  		APPEND FROM Yx ;
/*		CLOSE Yx ;  correction du 16 02 2003                         */
  		CLOSE Staup ;

/* Le 29 10 2004 : on crée ici la table IdEch qui servira dans %Sorties_sans_residu */
		IF ex > 0 THEN
			DO  ;                                                            
				CREATE IdEch VAR{&Id};
				APPEND FROM S ;
				CLOSE IdEch   ; 
			END ;
  	END ;
ELSE 
  	DO ;
/* Modification du 30 01 2004 : la meme macro est utilisée pour les  */
/* options B et C (%ATTERBC).                                        */
/*	  %IF %UPCASE(&ATTER) = "A" %THEN %DO ; %ATTERA %END ;           */
/*%ELSE %IF %UPCASE(&ATTER) = "B" %THEN %DO ; %ATTERB %END ;         */ 
/*%ELSE %IF %UPCASE(&ATTER) = "C" %THEN %DO ; %ATTERC %END ;         */

	  %IF %UPCASE(&ATTER) = A %THEN %DO ; %ATTERA %END ;
%ELSE %IF (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C) %THEN 
			%DO ;

/* Le 29 10 2004 : on crée ici la table IdEch qui servira dans %Sorties_avec_residu */
/*    			   seulement pour les options B et C                                */	
				IF ex > 0 THEN
					DO  ;                                                            
						CREATE IdEch VAR{&Id};
						APPEND FROM S ;
						CLOSE IdEch   ; 
					END ;
				%ATTERBC 
			%END ; 

/* Le 30 01 2004 : _______________ Les sorties d'IML sont gérées  dans 
			   %ATTERA et %ATTERBC (où figure le END du DO précédent)*/        
/*                        et non plus dans %ATTERA, %ATTERB, %ATTERC */        
/*********************************************************************/

/* Le 30 01 2004 : modification de l'option sans atterrissage (Z)    */
/* Le 16 02 2004 : création de la macro %ATTERZ                      */ 
/*%ELSE %IF %UPCASE(&ATTER) = "Z" %THEN %DO ; END; QUIT; %END ;      */

/* Le 08 03 2004 : inactivation de l'option Z d'arret en fin de vol  */
/* %ELSE %IF %UPCASE(&ATTER) = Z %THEN %DO ; %ATTERZ %END ;          */

/*%IF &ATTER NE "Z" %THEN  Le 30 01 2004    */
/*%IF %UPCASE(&ATTER) NE "Z" %THEN          */
/*%DO ;                                     */
/*	DATA Residu ;                           */
/* 		MERGE PiStar Reste ;                */  
/*	RUN ;                                   */
/*	PROC SORT DATA=Residu  ; BY &Id ; RUN ; */
/*%END ;                                    */ 
/*%ELSE %DO ; DATA Residu ; &Id = "" ; Pistar = . ; OUTPUT ; %END ; Le 30 01 2004 */
/*%ELSE %DO ; DATA Residu ; &Id = . ; Pistar = . ; OUTPUT ; %END ;                */ 

/*_______________________ Création du fichier échantillon &Sortie   
   à partir du fichier &Datafic2._&Sortie créé par %Sorties_avec_residu
   ou par %Sorties_sans_residu selon qu'il reste ou non des individus
   à la fin de la phase de vol.                                      */

/* Le 09 03 2004 : envoi d'un message d'erreur si les fichiers 
   en sortie n'ont pas pu etre créés                                 */

%IF  %SYSFUNC(EXIST(&Datafic2._&Sortie)) %THEN
	%DO; 
		DATA &Sortie ;
			SET &Datafic2._&Sortie ;
			IF &Sortie = 1 ;
		RUN;

		/*_____________________________ On lance les commentaires           */
		%IF (%UPCASE(&Comment) = OUI OR %UPCASE(&Comment) = GRAPHE)	%THEN
			%DO ;
				%BOUILLON_Cub(DataCub=&Datafic2._&Sortie ,
              	  			  Id=&Id,
              	  			  Pi=&Pi,
			      			  Pond=&pond,
                  			  Contr=&contr,
							  Atter=&Atter ) 
			%END ;
	%END;
%ELSE
	%DO;
		%DO n=1 %TO 3 ;  %PUT;  %END ;
%PUT "***** LES FICHIERS EN SORTIE N'ONT PAS PU ETRE CREES                          ";
		%IF  %UPCASE(&Cout) = CV  AND  %SYSFUNC(EXIST(_Denomi_)) = 0  %THEN
		/* Le 10 03 2004 : la table totaux contient les totaux des variables 
		   d'équilibrage stockés dans une seule observation. Cette table est utilisée
		   pour constituer, dans listvartn, la liste des variables de vrai total nul
		   qui sera affichée par le message d'erreur.                               */
			%DO;
				PROC TRANSPOSE data=totaux out=Ttotaux;          run;
				DATA Ttotaux; set Ttotaux; if col1=0;            run;
				PROC TRANSPOSE data=Ttotaux out=TotauxNuls;      run;
				DATA TotauxNuls; set TotauxNuls (drop=_name_);   run;
				PROC CONTENTS data=TotauxNuls noprint out=VarTN; run;
				DATA _null_; set VarTN;
					CALL SYMPUT('nbvar',left(_n_));
					CALL SYMPUT('nomvar'!!left(_n_),name);
				RUN;
				%LET listvartn=;
				%DO n=1 %TO &nbvar;
					%LET nomvar&n = %CMPRES(&&nomvar&n);
					%LET listvartn = &listvartn &&nomvar&n;
				%END;
%PUT "***** UN ATTERRISSAGE AVEC COUT=CV EST IMPOSSIBLE A REALISER                  ";
%PUT "***** CAR LE VRAI TOTAL EST NUL POUR : &listvartn                             ";
%PUT "      ******************************                                          ";
				PROC DATASETS  NOLIST ;
  					DELETE Totaux Ttotaux TotauxNuls VarTN	 /  MEMTYPE=DATA ;
				RUN ;
				QUIT ;
			%END;
	%END;

/*____________   Bannière de fin  _________*/      
%DO n=1 %TO 3 ;  %PUT;  %END ;
%PUT *************************************************************;
%PUT ************ MACRO CUBE : Version du 31/01/2006  ************;
%PUT ************              compilée en V9.1       ************;
%PUT ************              compatible avec la V8  ************;
DATA heure; SET heure;
	fin=time();
	duree=fin-debut;
	h=hour(duree);
	mn=minute(duree);
	s=second(duree);

/* Prise en compte du cas où s est arrondi à 60                   */
	IF ROUND(s) = 60 THEN
		DO;
			mn = mn + 1 ;
			s = 0;
			IF mn = 60 THEN
				DO;
					h = h + 1 ;
					mn = 0 ;
				END;
		END;
	
put "************ DUREE D'EXECUTION :" h 3.0 " h " mn 2.0 " mn " s 2.0 " s ************";

RUN;

%PUT *************************************************************;
%DO n=1 %TO 3 ;  %PUT;  %END ;

/*_____________________________ Destruction des tables intermédiaires               */
/* Le 07 11 2003, on remplace la table Cont qui n'est utilisée que par ATTERBC      */
/* par la table Xdilat qui remplace Cont dans ATTERBC et on ajoute la table Metrick.*/

PROC DATASETS  NOLIST ;
  DELETE Xdilat Metrick Haine _Proba_ _Tutti_ 
		 reste residu Alt Tone Saplane PiStar one
	     hainet Staup _denomi_ heure IdEch BaseTriParId
		 /  MEMTYPE=DATA ;
RUN ;                                    
QUIT ;
%FINI:

%MEND CUBE;
/*__________________________________________________________________________________*/

%MACRO Sorties_avec_residu / STORE ;
/* Il restait des individus sur lesquels statuer à la fin de la phase de vol. */

/* Si des individus ont été échantillonnés, la table IdEch contient leurs 
   identifiants; sinon la table IdEch n'existe pas.                         */

/*___________________________ On récupère la fin de la phase de vol */
	DATA Residu ;
  		MERGE PiStar Reste ;
	RUN ;
	PROC SORT DATA=Residu  ; BY &Id ; RUN ;

/* Le 04 03 2004 : 
/* On n'utilise &Sortie que si &Sortie existe                        */
/* ******************************************                        */
/* Le 09 03 2004 : Pour ne plus risquer d'interférer avec la table &Sortie
   spécifiée par l'utilisateur, on nomme IdEch, au lieu de &Sortie, la table
   qui contient les identifiants des individus retenus dans l'échantillon */

	%IF %SYSFUNC(EXIST(IdEch)) %THEN
		%DO;
/*___________________________________________ On réunit les sorties  */
 
			PROC SORT DATA=IdEch ; BY &Id ; RUN ;

/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*			PROC SORT DATA=&DataFic; BY &Id ; RUN ;                  */

/* &Datafic2 = &Datafic sans la référence éventuelle à une librairie */
/*           = partie de &Datafic située après un éventuel "."       */
			DATA &Datafic2._&Sortie ;

/*MERGE &Datafic residu (in=t) IdEch (in=s) ; le 26 02 2004 : 
        Suppression de la variable logique t, inutile, qui provoquait
		l'absence, dans les fichiers de sortie, d'une éventuelle 
		variable t présente dans le fichier en entrée.
        Pour la meme raison utilisation d'un autre nom pour la 
		variable logique s relative à IdEch.                         */ 
/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/* 			MERGE &Datafic residu  IdEch (in=individu_retenu_dans_echantillon) ;*/
  			MERGE BaseTriParId residu  IdEch (in=individu_retenu_dans_echantillon) ;

  			BY &Id ;

/*&Sortie  = (s) ; le 26 02 2004 : on prend un autre nom pour la variable in. */ 
  			&Sortie  = (individu_retenu_dans_echantillon) ;

  			IF &Sortie = 1 AND PiStar=. THEN Pistar = 1 ;
    			ELSE IF &Sortie = 0 AND PiStar = . THEN PiStar = 0 ;
  			IF &SORTIE = 1 THEN &Pond    = 1/&Pi ;
    			ELSE &Pond = 0 ; 
/* 	IF &ID NE "" ; instruction mise en commentaire le 04 03 2004    */
 
/* Modification du 17/10/2003 :                                     */
/* Intégration dans l'échantillon des individus ayant &pi=1         */
  			IF &Pi = 1 THEN
  				DO;
  					Pistar = 1;
					&Sortie = 1;
					&Pond = 1;
 				END;

			RUN ;
		%END;
	%ELSE       /* Cas d'un échantillon vide (IdEch n'existe pas)    */
                /* ************************************************  */ 
		%DO;
/*________________ On réunit &DataFic et residu                      */
 
/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*			PROC SORT DATA=&DataFic; BY &Id ; RUN ;                  */

/* &Datafic2 = &Datafic sans la référence éventuelle à une librairie */
/*           = partie de &Datafic située après un éventuel "."       */
			DATA &Datafic2._&Sortie ;

/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*  			MERGE &Datafic residu  ;  		                     */
  				MERGE BaseTriParId residu  ;
  				BY &Id ;

  				&Sortie  = 0;

  				IF &Sortie = 1 AND PiStar=. THEN Pistar = 1 ;
    				ELSE IF &Sortie = 0 AND PiStar = . THEN PiStar = 0 ;
  				IF &SORTIE = 1 THEN &Pond    = 1/&Pi ;
    				ELSE &Pond = 0 ; 
/* 	IF &ID NE "" ; instruction mise en commentaire le 03 03 2004    */
 
/* Modification du 17/10/2003 :                                     */
/* Intégration dans l'échantillon des individus ayant &pi=1         */
  				IF &Pi = 1 THEN
  					DO;
  						Pistar = 1;
						&Sortie = 1;
						&Pond = 1;
 					END;
			RUN ;
		%END;	

%MEND Sorties_avec_residu ;
/*__________________________________________________________________________________*/

%MACRO Sorties_sans_residu / STORE ;
/* Il ne reste aucun individu sur lequel statuer à la fin de la phase de vol.       */

/* Si IdEch existe, IdEch contient les identifiants des individus sélectionnés      */
/* à la fin de la phase de vol (puisqu'il n'y a pas d'atterrissage).                */

/* Le 04 03 2004 : 
/* On n'utilise &Sortie que si &Sortie existe                                       */
/* ******************************************                                       */
/* Le 09 03 2004 : Pour ne plus risquer d'interférer avec la table &Sortie
   spécifiée par l'utilisateur, on nomme IdEch, au lieu de &Sortie, la table
   qui contient les identifiants des individus retenus dans l'échantillon           */

	%IF %SYSFUNC(EXIST(IdEch)) %THEN
		%DO;
/*___________________________________________ On réunit les sorties                 */
			PROC SORT DATA=IdEch ; BY &Id ; RUN ;

/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*			PROC SORT DATA=&DataFic; BY &Id ; RUN ;                  */

/* &Datafic2 = &Datafic sans la référence éventuelle à une librairie                */
/*           = partie de &Datafic située après un éventuel "."                      */
			DATA &Datafic2._&Sortie ;

/*				MERGE &Datafic  IdEch (in=s) ; le 26 02 2004
        La variable logique s qui provoquait l'absence, dans les fichiers de sortie,
		d'une éventuelle variable s présente dans le fichier en entrée, est remplacée
		par la variable	individu_retenu_dans_echantillon.                           */

/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*				MERGE &Datafic  IdEch (in=individu_retenu_dans_echantillon) ;*/
				MERGE BaseTriParId  IdEch (in=individu_retenu_dans_echantillon) ;
				BY &Id ;

/*				&Sortie  = (s) ; le 26 02 2004 : 
								 on prend un autre nom pour la variable in.         */ 
				&Sortie  = (individu_retenu_dans_echantillon) ;

				IF &Sortie = 1 THEN Pistar = 1 ;
				ELSE PiStar = 0 ;
				IF &SORTIE = 1 THEN &Pond  = 1/&Pi ;
 				ELSE &Pond = 0 ; 
/* 	IF &ID NE "" ; instruction mise en commentaire le 04 03 2004                    */
 
/* Modification du 17/10/2003 :                                                     */
/* Intégration dans l'échantillon des individus ayant &pi=1                         */
				IF &Pi = 1 THEN
					DO;
						Pistar = 1;
						&Sortie = 1;
						&Pond = 1;
					END;
			RUN ;
		%END;
	%ELSE	/* IdEch n'existe pas : aucun individu n'a été retenu dans l'échantillon*/
		%DO;

/* Le 29 10 2004 : on utilise la table BaseTriParId au lieu de       */
/* Datafic triée par Id                                              */ 
/*			PROC SORT DATA=&DataFic; BY &Id ; RUN ;                  */
			DATA &Datafic2._&Sortie ; SET BaseTriParId ;
				Pistar = 0;
				&Sortie = 0;
				&Pond = 0;
				IF &Pi = 1 THEN
					DO;
						Pistar = 1;
						&Sortie = 1;
						&Pond = 1;
					END;
			RUN ;
		%END;
				
%MEND Sorties_sans_residu ;
/*__________________________________________________________________________________*/

%MACRO ATTERZ / STORE ;

END ;    /* correspond au DO de %CUBE après lequel le pré-processeur macro 
            place les instructions de %ATTERZ (conditionnées par &Atter=Z).
            Par conséquent, les 2 instructions suivantes (QUIT et %IF) sont
            exécutées  meme s'il n'y a pas atterrissage (Yx=0).            */    
QUIT ;
%IF %SYSFUNC(EXIST(Staup)) %THEN
	%DO ;
		%Sorties_sans_residu 
	%END ;
%ELSE
	%DO ;
		%Sorties_avec_residu
	%END ;

%MEND ATTERZ ;
/*__________________________________________________________________________________*/

/****************************************************/
/* Ici on traite le non atterrissage (Atter = "A")  */
/* On enlève autant de contraintes que nécessaire   */
/* pour que le rang de la matrice des contraintes   */
/* reste inférieur au nombre d'individus demeurés   */ 
/* F TARDIEU : 30/07/2001                           */ 
/*************************************************************************************/
/*                             Modifications du 14 03 2003                           */
/* %DIMINU intervient, en diminuant le nombre de contraintes, seulement si           */
/* la méthode du cube ne s'applique plus, c'est à dire si :                          */
/* Yx = nbre d'individus restants <= rang (_Xdilat_), test placé au début de %DIMINU.*/
/* Mais, comme Yx = nbre de lignes de _Xdilat_, on a toujours Yx >= rang(_Xdilat_).  */
/* Par conséquent, dans %DIMINU, sous la condition du 1er test, on a toujours :      */
/* Yx = rang(_Xdilat_) = _Rang_.                                                     */
/* Le 2ème test de %DIMINU : IF _Rang_ > 1 porte donc aussi sur Yx, de sorte que     */
/* si Rang(_Xdilat_) = Yx = 1, il faut échantillonner le dernier individu            */
/* avant de clore le tirage de l'échantillon par Yx = 0.                             */
/*************************** Modification du 13/11/2003 ******************************/
/* Dans %DIMINU, la réduction du nombre de colonnes est appliquée à _Xdilat et non à */
/* _Contr_ car c'est le rang de _Xdilat_ qu'il faut diminuer.                        */
/* Implantation d'un mode de calcul plus rapide du rang d'une matrice.               */
/*************************************************************************************/
%MACRO DIMINU / STORE ;
IF Yx <= _Rang_ THEN
	DO ;
		IF (_Rang_ > 1) THEN
			DO ;

/* On fait porter la suppression des contraintes colinéaires sur _Xdilat_ et non sur  */
/* _Contr_ car c'est le rang de _Xdilat_ qui importe.                                 */
/*				_coco   = ncol(_Contr_) ;                                             */
/*				_Concon = _Contr_ ;                                                   */  
				_coco   = ncol(_Xdilat_) ;
				_Concon = _Xdilat_ ; 
				DO i = 1 TO _coco  ;
  			  		_ttest_ = _Concon[,1:(_coco-1)] ;

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet           */
/*			  		_Ranga  = ROUND(TRACE(GINV(_ttest_)*(_ttest_))) ;                  */
				    _Noyau_ = HOMOGEN(BLOCK(_ttest_,0)) ;
				    _Ranga  = NROW(_Noyau_) - NCOL(_Noyau_) ;

  			  		IF _Ranga < _Rang_  
  					THEN 
    					DO ;
	  						_inter1 = _Concon[,NCOL(_concon)] ; 
      						_inter2 = _Concon[,1:(_coco-1)] ;
							_Concon = _Inter1||_Inter2 ;
						END ;
  					ELSE 
    					DO ;
							_Concon = _ttest_ ;
							_coco = _coco - 1 ;
						END ;
				END ;
				IF NCOL(_Concon) = _Rang_ THEN 
					DO ;
/* Après suppression des colonnes colinéaires de _Xdilat_ (=_Concon) on supprime la   */
/* dernière colonne de _Concon ce qui diminue le rang de _Xdilat_.                    */  
/*						_Concon  =_Concon[,1:(_rang_-1)] ;                            */
/*						_Xdilat_ = _Xdilat_[,1:(_rang_-1)] ;                          */ 
						_Xdilat_ = _Concon[,1:(_rang_-1)] ; 
					END ; 
/*				_Contr_ = _Concon ;                                                   */

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet          */
/*				_Rang_  = ROUND(TRACE(GINV(_Contr_)*_Contr_)) ;                       */
/* On remplace _Contr_ par _Xdilat_                                                   */
/*				_Noyau_ = HOMOGEN(BLOCK(_Contr_,0)) ;                                 */
				_Noyau_ = HOMOGEN(BLOCK(_Xdilat_,0)) ;
				_Rang_  = NROW(_Noyau_) - NCOL(_Noyau_) ;

			END ;
		ELSE
			DO;
/*                           Modification du 14 03 2003                       */
/* S'il ne reste qu'un individu sur lequel on n'a pas pu statuer,             */
/* il faut l'échantillonner                                                   */				
				IF Yx = 1 THEN IF UNIFORM(0) < _p_[1] THEN S = S // _Id_[1];
 
				Yx = 0 ;
			END;
	END ;
%MEND DIMINU ;
/*__________________________________________________________________________________*/

/*************************************************************************************/
/* Macro %ATTERA lancée si l'option A d'atterrissage a été choisie.                  */
/*************************************************************************************/

/**************************** Modifications du 14 03 2003 ****************************/
/* L'algorithme de recherche d'un vecteur du noyau de la matrice des contraintes     */
/* utilisé dans %CUBE est repris dans la boucle principale de %ATTERA.               */
/* Comme _Metric_ est une matrice supprimée dans %CUBE, les instructions la contenant*/
/* sont modifiées en conséquence.                                                    */
/**************************** Modification du 24/04/2003 *****************************/
/* A la fin de chaque itération de la boucle principale, _Xdilat_ est déterminée,    */
/* comme l'est _Contr_, par extraction à partir de sa version précédente (au lieu    */
/* d'etre recalculée à partir de _Pi_ et de _Contr_).                                */ 
/*************************************************************************************/
/* Le 30/10/2003 : correction de l'orthographe du message envoyé dans la LOG au cas  */
/* où il n'y a pas de phase d'atterrissage.                                          */
/**************************** Modifications du 13/11/2003 ****************************/
/* Implantation d'un mode de calcul plus rapide du rang d'une matrice.               */
/* Dans la boucle principale, on supprime la mise à jour de la matrice _Contr_ des   */
/* contraintes non dilatées, car dans tous les traitements ultérieurs c'est la       */
/* matrice _Xdilat_ des contraintes dilatées par le poids de chaque individu qui     */
/* est utilisée (meme chose pour la matrice _Pi_ devenue inutile).                   */
/* Suppression des compteurs  _DimP_, _DimS_, _SumP_ et _SumPi_ inutilisés par la    */
/* suite.                                                                            */
/*************************************************************************************/
/* options nocenter ; option recopiée dans Bouillon_Cub le 16 02 2004         */
%MACRO ATTERA / STORE ;
%DIMINU
/*__________________________________ Boucle principale _______________________*/ 
DO WHILE ( Yx > _Rang_)   ;
/*               Modification du 14 03 2003           */
/* _Xdilat_ = ((_Metric_##0.5)#(_PI_##(-1)))#_Contr_; */

/* Instruction mise en commentaire le 13/11/2003 car  */ 
/* _Xdilat_ est déterminée par %DIMINU.               */ 
/* _Xdilat_ = (_PI_##(-1))#_Contr_;                   */ 

/*______________________________________On calcule la matrice des contraintes */

/* Le 13/11/2003 on remplace _Contr_ par _Xdilat_ */
/* _dim_    = NROW(_contr_)    ;                  */
   _dim_    = NROW(_Xdilat_)   ;

/* Instructions mises en commentaire le 13/11/2003       */ 
/* _DimP_   = NROW(_P_)        ;                         */
/* _DimS_   = NROW(S)          ;                         */
/* _SumP_   = SUM(_P_)         ;                         */
/* _SumPi_  = SUM(_Pi_)        ;                         */

/*_________________________DEBUT DE MODIFICATION DU 14 03 2003__________________________*/

/*_NbCon_  = NCOL(_Contr_)    ; */
/* Le 13/11/2003 on remplace _Contr_ par _Xdilat_ */
/*   p     = NCOL(_Contr_)    ;                   */
     p     = NCOL(_Xdilat_)   ;

/*_________________________On recherche directement un vecteur du noyau 
						   de la matrice (p,N) des contraintes A = _Xdilat_`            */
A = _Xdilat_`;
N = _dim_ ;

IF Yx > p THEN             /*____________________Si Yx = N > p__________________________*/ 
	DO; 
                           /* On fixe à 1 la (p+1) ème composante (et à 0 les N-p-1 autres)
                           du vecteur du noyau 
                          (ses p premières composantes formant un vecteur inconnu delta)*/

		un_à_p = DO(1,p,1);/* vecteur ligne ayant p composantes de 1 à p --> (1 2 ... p)*/
		B = A[,un_à_p];    /* B = p premières colonnes de A                             */
		det_B = det(B);    /* calcul du déterminant de B                                */

                           /* si un vecteur du noyau peut etre trouvé par cette méthode */

		IF det_B > 0.0000001 | det_B < -0.0000001 THEN 
			DO;
				C = A[,p+1];           /* C = (p+1) ème colonne de A                    */

				delta = SOLVE(B,-C);   /* on résoud B * delta = -C
	                                   SAS conseillant d'utiliser SOLVE plutot que INV  */
				fin = J(N-p,1,0);
				fin[1,1] = 1;
    			_Proj_ = delta // fin; /* concaténation verticale pour compléter delta  */
  			END;

                           /* si cette tentative a échoué (B supposée non inversible), 
                           on utilise la fonction HOMOGEN pour trouver un vecteur  
						   du noyau de B (on peut utiliser HOMOGEN car rang(B) < p )    */ 
		ELSE 
			DO;
				_SOL_ = HOMOGEN(B);
				IF NCOL(_SOL_) > 0 THEN	/* On s'assure que l'utilisation de la fonction 
				                        HOMOGEN est licite i.e. que B est non inversible*/
					DO;		                                    
						w = _SOL_[,1];	
						_fin_ = J(N-p,1,0);    /* On complète ce vecteur par des 0      */   
						_proj_ = w // _fin_;
		  			END;

				ELSE	    /* Si, malgré le test sur det(B), IML considère 
							que B est inversible, on reprend la méthode précédente     */ 
					DO;

						C = A[,p+1];           /* C = (p+1) ème colonne de A           */

						delta = SOLVE(B,-C);   /* on résoud B * delta = -C             */
						fin = J(N-p,1,0);
						fin[1,1] = 1;
    					_Proj_ = delta // fin; /* concaténation verticale              */
					END;
			END;
	END;

ELSE						/*_________________________Si Yx = N <= p__________________
    					 	On a Rang(A)< Yx <= p, on peut donc calculer HOMOGEN(A) 
							(A étant de dimension p,Yx)                                 */
	_Proj_ = HOMOGEN(A)[,1];


/*___On genere un vecteur V dont la projection ne doit pas avoir une norme nulle*/
/*_Norm_ = 0 ;                                                                  */
/*DO UNTIL (_Norm_ > 0) ;                                                       */
/*  _v_= NORMAL(REPEAT(0,_Dim_,1)) ;                                            */
/*_____________ On norme le vecteur V ______________________                    */
/*	_V_ = _V_#(((_v_`*_v_)##(0.5)))##(-1) ;                                     */
/*_________________________on en fait la projection sur l'espace des contraintes*/
/*    _Proj_ = _V_ - _Xdilat_*GINV(_Xdilat_`*_Xdilat_)*(_Xdilat_`*_V_);         */
/*    _Norm_ = _Proj_`*_Proj_ ;                                                 */
/*END ;                                                                         */

/*_________________________FIN DE MODIFICATION DU 14 03 2003____________________*/

/*_________________________________On calcule les Lambda1 et lambda2 postulants */
IF MAX(_proj_)>0 THEN
    DO;
      _bzh_ = LOC(_proj_>0)                ;
      l11   = (1-_p_[_bzh_])/_proj_[_bzh_] ;
      l21   = _p_[_bzh_]/_proj_[_bzh_]     ;
    END;
    ELSE
    DO;
      l11=99999999999999999999999;
      l21=99999999999999999999999;
    END;

IF MIN(_proj_)<0 THEN
    DO;
      _bzh_ = LOC(_proj_<0)                     ;
      l22   = (1-_p_[_bzh_])/ABS(_proj_[_bzh_]) ;
      l12   = _p_[_bzh_]/ABS(_proj_[_bzh_])     ;
    END;
    ELSE DO;
     l12=999999999999999999999999;
     l22=999999999999999999999999;
    END;
/*_________________________________Lambda1 & Lambda2 sont definis*/
l1=MIN(l11//l12);
l2=MIN(l21//l22);

/*________________________Une nouvelle direction est selectionnee*/
IF (UNIFORM(0)<l2/(l1+l2))
  THEN _p_=_p_+_proj_#l1;
  ELSE _p_=_p_-_proj_#l2;

/*_____________________________________________________________Echantillonnage */
  _Idlig_  = T(DO(1,NROW(_Xdilat_),1)) ;
  IF MAX(_P_) > 0.9999999 THEN
    DO ;
      OuiOui   = _Idlig_[LOC(_p_>0.9999999)];
      S = S//_Id_[OuiOui]  ;
    END ;

/*______________________________________________Selection des futurs postulants*/

  IF NCOL(LOC(_p_>  0.0000001 & _p_< 0.9999999)) > 0 THEN 
  DO ; 
  	  Con_Rest = LOC(_p_>  0.0000001 & _p_< 0.9999999)  ;
      Reste    = _Idlig_[Con_Rest];
      _Id_     = _Id_[Reste] ;

/* Instruction mise en commentaire le 13/11/2003       */ 
/*    _P2_     = _P_         ;                         */

/*     Modification du 14 03 2003  */
/*    _Metric_ = _Metric_[Reste] ; */

      _P_      = _P_[Reste] ;

/* Instructions mises en commentaire le 13/11/2003       */ 
/*    _Pi_     = _Pi_[Reste] ;                           */ 
/*    _Contr_  = _Contr_[Reste,] ;                       */
/*	  somme    = sum(_p_) ;                              */

 	   Yx      = NROW(_Id_) ;
 
/*     Modification du 14 03 2003                        */
/*    _Xdilat_ = ((_Metric_##0.5)#(_PI_##(-1)))#_Contr_; */

/*     Modification du 24 04 2003                        */ 
/*	  _Xdilat_ = (_PI_##(-1))#_Contr_;                   */
	  _Xdilat_ = _Xdilat_[Reste,];

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet           */
/*    _Rang_   = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;                               */
	  _Noyau_  = HOMOGEN(BLOCK(_Xdilat_,0)) ;
	  _Rang_   = NROW(_Noyau_) - NCOL(_Noyau_) ;
  END ; 
  ELSE Yx = 0 ;
%DIMINU 
/*___________________________________________________________ Reinitialisation */
END ;
/*_________________________________________ Fin de la boucle principale _______*/

/* Le 04 03 2004 :                        
   Si des individus ont été échantillonnés, la table &Sortie contient leurs 
   identifiants; sinon la table &Sortie n'existe pas.                          */
/* Le 09 03 2004 : Pour ne plus risquer d'interférer avec la table &Sortie
   spécifiée par l'utilisateur, on nomme IdEch, au lieu de &Sortie, la table
   qui contient les identifiants des individus retenus dans l'échantillon      */

/*CREATE Samba_A VAR{&Id};                                                     */
/*APPEND FROM S ;                                                              */
/*CLOSE Samba_A   ;                                                            */
nech = NROW(S);
IF nech > 0 THEN
	DO;
		CREATE IdEch VAR{&Id};
		APPEND FROM S ;
		CLOSE IdEch ;
	END;

END ;        /* correspond au DO de %CUBE après lequel le pré-processeur macro 
                place les instructions de %ATTERA (conditionnées par &Atter=A).
                Par conséquent, les 2 instructions suivantes (QUIT et %IF) sont
                exécutées  meme s'il n'y a pas atterrissage (Yx=0).            */
QUIT ;
%IF %SYSFUNC(EXIST(Staup)) %THEN
	%DO ;
		%Sorties_sans_residu 
	%END ;
%ELSE
	%DO ;
/*		DATA &Sortie ;       Instructions mises en commentaire le 04 03 2004        */
/*			SET Samba_A ;    car &Sortie est créée directement à partir de S        */
/*		RUN ;                                                                       */ 
		%Sorties_avec_residu
	%END ;
%MEND ATTERA ;
/*__________________________________________________________________________________*/

/******************************************************************************/
/* Macro %ATTERBC lancée pour les options B et C d'atterrissage (lance        */
/* %Gegene_Tous si Atter=B, %Gegene si Atter=C).                              */
/******************************************************************************/

/*----------------------------------------------------------
   Ce programme permet de générer une sorte de tableau
   disjonctif qui réprésente tous les échantillons
   possibles d'une taille fixée à partir de la somme
   des probablités d'inclusion associées aux individus
   restants ...........................................
   Si Atter = B
   c'est sur tous les Echant que LP va tourner
   Si Atter = C
   On tentera de préserver la taille fixe sous réserve
   que la somme des Pika soit un nombre entier.
   Dans le cas contraire on génèrera les Echant. pour les
   deux tailles qui encadrent la valeur de somme des Pika
   (la phase d'atterrissage tiendra compte des deux possibilités).

   Puis on passe la main au programme linéaire
   qui résoud la phase d'atterrissage du CUBE .........
   F TARDIEU : 30/07/2001
-------------------------------------------------------------*/

/*----------------------------------------------------------
   Pour diminuer le temps de calcul ainsi que l'espace mémoire nécessaire
   (ce qui permet d'augmenter le nombre maximum de contraintes utilisables
   pour un ordinateur donné), il est apparu préférable d'avoir recours
   le plus souvent possible à SAS de base plutot qu'à IML.
   En effet, un tableau peut etre stocké aussi bien sous la forme d'une
   table SAS que sous la forme d'une matrice (table et matrice pouvant avoir 
   le meme nom, car SAS fait la différence d'après l'instruction d'appel). 
   De plus, cela a facilité le regroupement des macros ATTERB et ATTERC dans
   la macro ATTERBC prenant en compte les options d'atterrissage B et C
   (pour l'option B, les échantillons à examiner étant maintenant aussi créés 
   sous forme d'une table SAS).
   B WEYTENS : 11/02/2004
-------------------------------------------------------------*/

%MACRO Gegene(Alt=,hain= ) / STORE ;
/* Constitution d'une table SAS décrivant sous forme d'un  */
/* tableau disjonctif tous les échantillons possibles d'une*/
/* taille donnée Haine tirés parmi Alt individus.          */  
/* Alt   = Nb d'ind. restants (Nb ind restants à traiter)  */
/* Haine = Nb d'ind. à échantillonner (Somme des Pika)     */

%LOCAL I J I2 ;
DATA Z&Hain ;
ARRAY Fixe (%EVAL(&Alt))
                %DO J=1 %TO %EVAL(&Alt) ;
                  Col&J
                %END ;  ;
ARRAY Z _NUMERIC_ ;
  Borne = 0 ;
  DO i = 0 TO %EVAL(&Alt)-1 ;
    Borne + 2**i ;
  END ;

/*                           Modification du 20/11/2003                             */
/*  Pour tenir compte du cas où la taille souhaitée de l'échantillon est 0 (Hain=0) */
/*  on commence la boucle en 0 pour écrire l'échantillon de taille nulle            */
/*  (qui n'est pas écrit si on commençe la boucle en 1).                            */
/*DO i = 1 TO Borne ;                                                               */
  DO i = 0 TO Borne ;

    Nb    = i  ;
    DO i2 = 1 TO %EVAL(&Alt)   ;
      Fixe(i2) = MOD(Nb,2)     ;
      Fix + MOD(Nb,2)          ;
      Div      = FLOOR(Nb/2)   ;
      IF Div < 1 THEN i2 = Borne + 1 ;
      Nb       = Div ;
    END ;
    IF Fix = %EVAL(&Hain) THEN 
       DO ;
         DO OVER Z ;
           IF Z = . THEN Z = 0 ;
         END ;
         OUTPUT ;
       END ;
    Fix = 0 ;
  END ;
DROP Div Fix Borne I I2 Nb  ;
RUN ;
%MEND Gegene ;

%MACRO Gegene_Tous(Alt=) / STORE ;
/* Constitution d'une table SAS décrivant sous la forme d'un */
/* tableau disjonctif tous les échantillons possibles d'une  */
/* taille quelconque tirés parmi Alt individus.              */  
/* Alt   = Nb d'ind. restants (Nb ind restants à traiter)    */

DATA Z&Alt ;
ARRAY Fixe (%EVAL(&Alt))
                %DO J=1 %TO %EVAL(&Alt) ;
                  Col&J
                %END ;  ;
ARRAY Z _NUMERIC_ ;
Borne = 2**%EVAL(&Alt) - 1 ;

  DO i = 0 TO Borne ;
    Nb    = i  ;
    DO i2 = 1 TO %EVAL(&Alt)   ;
      Fixe(i2) = MOD(Nb,2)     ;
      Div      = FLOOR(Nb/2)   ;
      IF Div < 1 THEN i2 = Borne + 1 ;  
      Nb       = Div ;
    END ;
    DO OVER Z ;
      IF Z = . THEN Z = 0 ;
    END ;
    OUTPUT ;
  END ;

DROP Div  Borne I I2 Nb  ;
RUN ;
%MEND Gegene_Tous ;

%MACRO Atterbc / STORE ;

END ;  /* correspond au DO de %CUBE après lequel le pré-processeur macro 
          place les instructions de %ATTERBC (conditionnées par &Atter=A ou B).
          Par conséquent, les 2 instructions suivantes (QUIT et %IF) sont
          exécutées  meme s'il n'y a pas atterrissage (Yx=0).                  */
QUIT ;

%IF %SYSFUNC(EXIST(Staup)) %THEN
  	%DO ;
		%Sorties_sans_residu
  	%END ;
%ELSE

/* Le 09 03 2004 : Dans le cas contraire, ie SI cout=cv ET SI la table _Denomi_
n'existe pas (pour cause de nullité d'un total), on ne lance pas l'atterrissage  */
	%IF  %UPCASE(&Cout) = DIST  OR  %SYSFUNC(EXIST(_Denomi_)) %THEN 
 
  	  %DO ;

/*______________ On a quitté momentanément IML Attention sauvegarde  */
/*______________ On stocke le nombre d'individus restants dans Alt   */
		DATA _NULL_ ;
   			SET Alt ;
   			CALL SYMPUT('Alt',Col1)     ;
		RUN ; 
/* destruction préventive de _tutti_ et des tables intermédiaires qui vont servir*/
    	PROC DATASETS  NOLIST ;
      		DELETE _Tutti_ Prob Ta Ta1 Ta2 Ta3 TTech 
			 		Plan Track Simplex /  MEMTYPE=DATA ;
    	RUN ;                                             
   		QUIT ;

/*______________ Pour l'option "B" d'atterrissage, la table _Tutti_ contient
	             tous les échantillons qu'il est possible de constituer à partir
				 des Alt individus restants                                      */

		%IF %UPCASE(&ATTER) = B %THEN 
			%DO ;   
				%Gegene_Tous(Alt=&Alt)

    			PROC DATASETS  NOLIST ;
      				CHANGE Z%SYSEVALF(&Alt)=_Tutti_ / MEMTYPE=DATA ;
    			RUN ;
				QUIT ;
			%END ;

/*______________ Pour l'option "C" d'atterrissage, la table _Tutti_ contient
	             tous les échantillons qu'il est possible de constituer à partir
				 des Alt individus restants et dont la taille soit égale à la
		         somme des Pika si cette somme est entière, ou, sinon, à l'un
		         quelconque des deux entiers qui l'encadrent.                     */

		%IF %UPCASE(&ATTER) = C %THEN 
			%DO ;   
				DATA _NULL_ ;
  					SET Haine ;
  					CALL SYMPUT('Haine',Som_P_) ;
					CALL SYMPUT('Hainet',ROUND(Som_P_,1)) ;
				RUN ;
				%Gegene(Alt=&Alt,Hain=&Hainet)
 
				PROC DATASETS  NOLIST ;
					CHANGE Z%SYSEVALF(&Hainet)=_Tutti_ / MEMTYPE=DATA ;
				RUN ;
				QUIT ;

/*______________ Somme des Pika n'est pas entier aux arrondis près */
/*______________ ce qui ne devrait pas arriver, mais bon !...      */

				DATA _NULL_ ;
/* LE 01/07/2003 :                                                    */ 
/* Initialisation de Autr_N qui ne sera conservée que si              */
/* ABS(XX-%SYSEVALF(&Haine)) < 0.00001                                */
	  				CALL SYMPUT('Autr_N',&Hainet) ;

	  				XX=ROUND(%SYSEVALF(&Haine),1) ;
	  				IF XX-%SYSEVALF(&Haine)< 0 
		 				THEN IF ABS(XX-%SYSEVALF(&Haine)) > 0.00001 
         					THEN CALL SYMPUT('Autr_N',%SYSEVALF(&Haine,CEIL)) ;
/* LE 01/07/2003 :                                                    */
/* Suppression du ELSE qui empechait de traiter correctement          */ 
/* le cas de l'arrondi par excès                                      */  
/*    ELSE IF XX-%SYSEVALF(&Haine)> 0                                 */
      				IF XX-%SYSEVALF(&Haine)> 0
		 				THEN IF ABS(XX-%SYSEVALF(&HAINE)) > 0.00001  
         					THEN CALL SYMPUT('Autr_N',%SYSEVALF(&Haine,FLOOR)) ; 
/* LE 01/07/2003 :                                                    */ 
/*    ELSE CALL SYMPUT('Autr_N',&Hainet) ;                            */
/* Cette instruction est placée en début d'étape pour etre activée    */
/* quand XX-%SYSEVALF(&Haine)=0 ou < 0.00001 en valeur absolue        */
    			RUN ; 

   				%IF &Hainet ^= &Autr_N %THEN
     				%DO  ;
       					%Gegene(Alt=&Alt,Hain=&Autr_N)

       					PROC APPEND BASE=_Tutti_ DATA=Z%SYSEVALF(&Autr_N) ;
       					RUN ;

/* Il faut détruire la table qui vient d'etre concaténée à _Tutti_    */
						PROC DATASETS  NOLIST ;
      						DELETE Z%SYSEVALF(&Autr_N) /  MEMTYPE=DATA ;
   		 				RUN ;
						QUIT ;
     				%END ;
			%END ;


/* Tech = T(_Base_)//SHAPE(1,1,NROW(_Base_)) ;              */
/* En vue de l'appel du programme linéaire (%ATTER),        */
/* on prépare la table TTech image de la transposée de Tech */
/* (_Tutti_ étant l'image de _Base_)                        */

		DATA TTech; SET _Tutti_ END=fin;
			Col=1;
			IF fin THEN CALL SYMPUT('n',_N_);
/* &n = nbre de lignes de TTech = nbre de col de Tech dans %ATTER            */
		RUN;

		PROC IML symsize=80000000 ;

/* allocation de la taille du symbolspace conseillée par SAS                 */ 
/* pour le calcul des coûts à partir d'une table.                            */
/* 80 000 000 est la valeur requise pour 19 contraintes et l'option B,       */
/* 19 = nombre maxi de contraintes pour un micro ayant 256 Mo de mémoire     */
/* (pour les ordinateurs ayant plus de 256 Mo de mémoire, il faut multiplier */
/* la symsize par 2,13 pour chaque contrainte supplémentaire au delà de 19). */ 
 
/*  La matrice _Base_ n'est plus utile car on va calculer le coût de chaque  */
/*  échantillon par lecture de la table _Tutti_                              */ 
/*	USE _Tutti_  ;            Matrice des échantillons à traiter qui         */
/*	READ ALL INTO _Base_ ;    est dans la table _Tutti_                      */

		USE PiStar    ;  /*Les prob. d'Inc cubesques              */ 
		READ ALL INTO _P_  ;

/* Le 07/11/2003 on utilise les contraintes dilatées              */
/*USE Cont ;               Les contraintes                        */ 
/*READ ALL INTO Cont ;                                            */ 
		USE Xdilat ;     /*Les contraintes dilatées               */ 
		READ ALL INTO _Xdilat_ ;

/* Le 07/11/2003, la table _Denomi_ n'existe que si cout=CV       */
/* et on la recopie dans une matrice de meme nom : _DenomI_       */  
/*USE _Denomi_ ;                                                  */   
/*READ ALL INTO _Denom_ ;                                         */

		%IF %UPCASE(&Cout) = CV   %THEN 
			%DO ;
				USE _Denomi_ ;
				READ ALL INTO _Denomi_ ; 
			%END ;

/* Le 07/11/2003, si Cout=DIST on recopie la table Metrick        */
/* dans la matrice _Metrick                                       */  

		%IF %UPCASE(&Cout) = DIST   %THEN 
			%DO ;
				USE Metrick ;
				READ ALL INTO _Metrick ; 
			%END ;

/*___________________ CALCUL DES COUTS DE CHAQUE ECHANTILLON                 */

/*___________________ Matrice des coûts si COUT=CV                           */

/******************** DEBUT ANCIEN CALCUL TOUT IML ***************************/
/*
/*  DO i = 1 TO NROW(_Base_) ;                                               */ 
/*  	Tpapika = Tpapika//_P_` ;                                            */
/*	END ;                                                                    */
/*                                                                           */
/* on duplique les vrais totaux (matrice ligne _Denomi_)                     */ 
/* autant de fois qu'il y a d'échantillons possibles                         */
/*                                                                           */
/*	Prep4  = SHAPE(_Denomi_,NROW(_Base_),NCOL(_Xdilat_));                    */
/*                                                                           */
/* Pour calculer l'écart aux vrais totaux, on utilise le fait qu'en fin de vol les 
  équations d'équilibrage sont vérifiées, ce qui fournit une expression des vrais 
  totaux simplifiant le calcul de l'écart dans lequel il ne reste que les individus 
  présents en fin de vol : écart =  _Base_*_Xdilat_  -  Tpapika*_Xdilat_     */
/*                                                                           */
/*	Prep5  = (( (_Base_ - Tpapika)*_Xdilat_ )##2)#((Prep4)##(-2));           */
/*	Prep6  = Prep5[,+];                                                      */
/*	Track = T(Prep6) ;                                                       */
/*                                                                           */
/******************** FIN ANCIEN CALCUL TOUT IML *****************************/

/*****************************************************************************/
/*    NOUVEAU CALCUL DES COUTS SI COUT=CV :                                  */
/*    ***********************************                                    */
/*    On lit séquentiellement la table _Tutti_ des échantillons à examiner,    
	  chaque échantillon étant stocké dans la matrice ligne _ech_,
	  les valeurs de Pistar étant stockées dans la matrice colonne _P_.      */
/*****************************************************************************/

		%IF %UPCASE(&Cout) = CV   %THEN 
  			%DO ;
  				USE _Tutti_  ; 
 				SETIN _Tutti_ POINT 0;
 
  				DO DATA;
  					READ NEXT INTO _ech_;
  					_cout_ech_contr_ = ( ( (_ech_-_P_`)*_Xdilat_ )##2 )#(_Denomi_##(-2)); 

					_cout_ech_ = sum(_cout_ech_contr_) ; 

/*  				Track = Track || _cout_ech_; Track devient une matrice colonne pour
	 							        éviter une transposition dans %ATTER */
					Track = Track // _cout_ech_;
  				END;
  			%END ;

/*___________________ Matrice des coûts si COUT=DIST                         */

		%IF %UPCASE(&Cout) = DIST %THEN 
			%DO ; 

/*Inter  = TCont`*GINV(TCont*TCont`)*Tcont ; Correction du 07 11 2003 sur Inter:
                                             ----------------------------------
  Il faut utiliser _Metrick ( = GINV(AA`) avec A = _Xdilat_` initial ) car la
  simplification qui permet d'utiliser le produit (_Base_-Tpapika)*_Xdilat_ 
  (avec _Xdilat_ en fin de vol) et son transposé n'est pas applicable à ce niveau.*/ 

				Inter  = _Xdilat_ * _Metrick * _Xdilat_` ;

/******************** ANCIEN CALCUL TOUT IML *********************************/
/*		Inter2 = (_Base_-tPapika)*Inter*(_Base_-tPapika)`;                   */
/*		Track = T(Diag(Inter2)*SHAPE(1,NROW(_Base_),1)) ;                    */
/*****************************************************************************/

/*****************************************************************************/
/*    NOUVEAU CALCUL DES COUTS SI COUT=DIST                                  */
/*    *************************************                                  */
/*****************************************************************************/
  				USE _Tutti_  ; 
 				SETIN _Tutti_ POINT 0;
 
  				DO DATA;
  					READ NEXT INTO _ech_;
  					_cout_ech_ =  (_ech_-_P_`)*Inter*(_ech_`-_P_);

/*  Track = Track || _cout_ech_;   Track devient une matrice colonne pour
  								   éviter une transposition dans %ATTER      */
					Track = Track // _cout_ech_;
  				END;

  			%END ;

/* Le 30 01 2004 : création de la table Track si comment=graphe              */

		%IF %UPCASE(&Comment) = GRAPHE  %THEN
			%DO;
				CREATE Track VAR{Track};
				APPEND FROM Track;
				CLOSE Track;
			%END; 

/*__________________ Mise en forme pour le programme linéaire de %ATTER      */

/* La table TTech image de la transposée de Tech a été créée juste avant     */ 
/* le lancement d'IML                                                        */ 
/* Tech = T(_Base_)//SHAPE(1,1,NROW(_Base_)) ;                               */

		Prob = _P_//{1} ;
		CREATE Prob FROM Prob;
		APPEND FROM Prob;
		CLOSE Prob;

/*		Rel = SHAPE('=',NCOL(_Base_)+1,1) ;*/
		Rel = SHAPE('=',%EVAL(&Alt)+1,1) ; 

/*_______________________________ Appel au programme linéaire    */

		%Atter(track,TTech,Rel,Prob,Plan)

		FREE / Plan ;

		USE _Tutti_  ;           /* Matrice des échantillons à traiter qui*/
		READ ALL INTO _Base_ ;   /* sont dans la table _Tutti_            */

		Possib  = _Base_[LOC(Plan>0),] ;
		Ppossib = Plan[LOC(Plan>0)] ;
		bbbase  = Ppossib||Possib ;
 
		FREE Possib PPossib ;

		CREATE One FROM bbbase ;
		APPEND FROM bbbase   ;
		CLOSE One ;

/*___________________________Création de la table Simplex si comment=graphe       */

/* S'il est possible d'éditer les sorties graphiques :                            */
/* Le nombre de lignes de _Base_, qui est aussi le nombre de lignes de Bill, et   */
/* par conséquent, le nombre d'observations de la table Simplex, ne doit pas      */
/* dépasser 32767 car c'est le nombre maximum de variables autorisé par SAS pour  */
/* la table S qui est la table transposée de la table Simplex dans %Bouillon_Cub. */

/* Le 29 01 2004, cette limitation est supprimée grace à une modification de      */
/* %Bouillon_Cub évitant d'avoir à transposer la table Simplex pour en calculer   */
/* le nombre de variables.                                                                     */
/* De plus, la table Simplex est créée par concaténation des tables Track (une    */
/* variable Track), _Tutti_ (&Alt variables col1 à col&Alt) et Plan (une variable */
/* Plan).                                                                         */
 
/*IF NROW(_Base_) < 32768 THEN                                                    */ 
/*	DO;                                                                           */
/* 		USE Track ;                                                               */         
/*		READ ALL INTO Track ;                                                     */
/*		CLOSE Track ;                                                             */

/*		Bill  = T(Track)||_Base_||Plan ; quand Track était une matrice ligne      */
/*		Bill  = Track||_Base_||Plan ;*/   /* avec Track matrice colonne           */

/*		CREATE Simplex FROM Bill ;                                                */  
/*		APPEND FROM Bill ;                                                        */        
/*		CLOSE Simplex ;                                                           */
/*	END;                                                                          */

/* Le 30 01 2004 : création de la table Plan si comment=graphe                    */
/* Le 19 03 2004 : ajout de la condition Atter=B ou C                             */

		%IF %UPCASE(&Comment) = GRAPHE  AND  
		   (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C)  %THEN
			%DO;
				CREATE Plan  VAR{Plan}  ;         
				APPEND FROM Plan ;
				CLOSE Plan ;
			%END; 

		QUIT ;

/* Le 30 01 2004 : si comment=graphe, création directe de la table Simplex à      */
/* partir des tables images de Track, _Base_ et Plan;                             */
/* Le 19 03 2004 : ajout de la condition Atter=B ou C                             */

		%IF %UPCASE(&Comment) = GRAPHE  AND
		   (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C)  %THEN
			%DO;
				DATA Simplex;
  					SET Track;
  					SET _Tutti_;
  					SET Plan;
				RUN;
			%END; 

		%TIR_LP

/*_____________________________ Destruction des tables intermédiaires */

		PROC DATASETS  NOLIST ;
  			DELETE Prob Ta Ta1 Ta2 Ta3 TTech 
		 		/  MEMTYPE=DATA ;          
		RUN ;
		QUIT ;
		%Sorties_avec_residu 
  	  %END ;
%MEND Atterbc ;
/*__________________________________________________________________________________*/

/************************************************************************************/
/*Ce programme résoud le programme linéaire                                         */
/*il est plus que très inspiré par le SAMPLE de la V8                               */
/*car SAS n'a pas fourni d'assistance sur ce thème                                  */ 
/* F TARDIEU : 30/07/2001                                                           */
/************************************************************************************/
/* Le 19 01 2004 :                                                                  */
/* Pour diminuer l'espace mémoire nécessaire on utilise des tables SAS pour stocker */
/* des matrices intermédiaires et on libère de l'espace dès que possible            */
/* (instructions FREE).                                                             */
/* Le paramètre coef est remplacé par son transposé Tcoef ce qui évite une          */
/* transposition.                                                                   */
/* Les matrices value, lhs et dual, inutilisées ailleurs, ne sont plus calculées    */
/* (le 23 01 2004 : rétablissement du comportement antérieur dans le cas où         */
/*  l'instruction STOP est exécutée, par réactivation d'une instruction mise en     */
/*  commentaire le 19/01/2004).                                                     */
/************************************************************************************/
/* Le 11 02 2004 :                                                                  */
/* Dans la macro %Atter qui résoud le programme linéaire (options B et C)           */
/* un test de non nullité est remplacé par un test de comparaison à 10E-10.         */
/* Sans effet sur l'option B (car la valeur testée est alors toujours nulle),       */
/* cette modification diminue de plus d'un tiers l'espérance du coût, selon le plan */
/* de sondage solution, en cas d'utilisation de l'option C (ex E), car, auparavant, */
/* on s'arretait à la phase 1 de la résolution du programme linéaire sans           */
/* rechercher la solution optimale.                                                 */
/************************************************************************************/

%MACRO Atter(obj, Tcoef, rel, rhs, activity) / STORE ;
/* Appel par :                               */
/*    %Atter(track,TTech,Rel,Prob,Plan)      */

      bound=1.0e10;
/*    n=ncol(&coef);*/
	  n=%EVAL(&n) ;  /* nbre d'échantillons possibles = NOBS(&Tcoef) = NCOL(&coef) */
/*    m=nrow(&coef);*/
	  m=%EVAL(&Alt) + 1 ; 
/*	   = nbre d'individus restants + 1 = NVAR(&Tcoef) = NROW(&coef) */

/*___________________________ On minimise donc on maximise l'opposée */
      o=-1;
/*___________________________ Construction des variables logiques    */

/*    rev=(&rhs<0)   ;     &rhs=Prob, non <0, donc rev=SHAPE(0,m,1)  */
/*    adj=(-1*rev)+^ rev;                     donc adj=SHAPE(1,m,1)  */

      eq=(&rel='=');         /* eq=artobj`                 */       
      logicals=I(m);         /* matrice identité d'ordre m */
/*    artobj=eq`;                                          */

/*    nl=ncol(logicals);  */
	  nl=m;
      nv=n+nl+2;
/*__________________________   Construction des 3 composantes de Ta,
	                          transposée de la matrice a des coefficients */

/*   a=((o*&obj)||repeat(0,1,nl)||{ -1 0 }) --> a1
	  //
        (repeat(0,1,n)||-artobj||{ 0 -1 }) --> a2
	  //
        ((adj#&coef)||(logicals||repeat(0,m,2)));  --> a3                 */

/*      ((adj#&coef)||logicals||repeat(0,m,2)); pour calculer en priorite 
	                                        les matrices de petite taille */

/*        adj=SHAPE(1,m,1) donc adj#&coef = &coef = T(&Tcoef)             */
/*                         donc Ta3 = &Tcoef // logicals // repeat(0,2,m) */

	  Ta1 = o*&obj // ( repeat(0,nl,1) // {-1, 0} ) ; free &obj ;
      CREATE Ta1 VAR{TA1};
      APPEND FROM Ta1;
      CLOSE Ta1;
	  Free Ta1;

	  Ta2 = repeat(0,n,1) // ( -eq // {0, -1} ) ;
      CREATE Ta2 VAR{TA2};
      APPEND FROM Ta2;
      CLOSE Ta2;

Quit;   

PROC IML ;
/* on ouvre une nouvelle session IML afin d'allouer                    */
/* un espace mémoire worksize plus élevé                               */

      USE &Tcoef ;             /* Transposée de Tech qui est dans la   */
      READ ALL INTO &Tcoef ;   /* table TTech                          */
 
	  m = %EVAL(&Alt) + 1 ; 
      logicals = I(m) ; 
	  Ta3 = &Tcoef // ( logicals // repeat(0,2,m) ) ;  Free &Tcoef ;

	  CREATE Ta3 FROM Ta3 ;
	  APPEND FROM Ta3;             
      CLOSE Ta3 ;

Quit;
/*__________________________   Construction de la table Ta, image de la
	                          transposée de la matrice a des coefficients */
DATA Ta;  
	  SET Ta1; 
	  SET Ta2; 
	  SET Ta3;
RUN;

PROC IML ;

/*__________________________   Construction  des coefficients     */

  	  USE Ta    ;         
  	  READ ALL INTO Ta ; 

	  a = Ta`;	  free Ta ;
/*__________________________________ rhs, lower bounds, and basis */
      bound=1.0e10;
      o=-1;
	  n=%EVAL(&n) ;  
	  m=%EVAL(&Alt) + 1 ; 
	  nl=m;
      nv=n+nl+2;

	  USE &rhs ;         
	  READ ALL INTO &rhs  ;
/*    rev=(&rhs<0)   ;     &rhs=Prob, non <0, donc rev=SHAPE(0,m,1)  */
/*    adj=(-1*rev)+^ rev;                     donc adj=SHAPE(1,m,1)  */
/*    b={0,0}//(adj#&rhs);                    donc b={0,0}//&rhs     */
      b={0,0}//&rhs;
 
      L=repeat(0,1,nv-2)||-bound||-bound;
      basis=nv-(0:nv-1);
/*__________________________________ Phase 1 - primal feasibility */
	  FREE / a b nv l basis bound o n ;

      CALL  lp(rc,x,y,a,b,nv,,l,basis);

/* Le 11 02 2004 : une valeur très proche de zéro pour x[nv] est considérée 
   comme nulle ce qui permet d'améliorer le plan de sondage obtenu avec l'option E
   (dans ce cas, l'exécution de l'instruction STOP avait pour conséquence
   la non exécution de la phase 2 (solution optimale) , d'où une perte de précision,
   pour 6 contraintes, d'environ 30% d'autant plus importante que le nombre de 
   contraintes est élevé)                                                          */
/*	  if x[nv] ^=0 then                                                            */

	  if ABS(x[nv]) > 0.0000000001 then                                                       
      do;
         stop;
      end;
/*___________________________________________ Solution optimale  */
      if rc <= 0 then 
      do ;
          u=repeat(.,1,nv-2)||{ . 0 };
          L=repeat(0,1,nv-2)||-bound||0;
	 	  FREE / a b nv u l basis o n ;

	      CALL LP(rc,x,y,a,b,nv-1,u,l,basis);
	  end ;
          value=o*x  [nv-1]; /*en commentaire le 19/01/04 car inutilisée;
		  mais réactivée le 23/01/04 pour que l'instruction suivante 
		  &activity= x [1:n] soit exécutée si x[nv] ^=0 ce qui provoque un STOP
		  ayant pour conséquence la non exécution du test if rc <= 0 et de
		  l'instruction qui suit ce test.                               */

          &activity= x [1:n] ;

/*        lhs=&coef*x[1:n];  en commentaire le 19/01/04 car inutilisée  */
/*        dual=y[3:m+2];     en commentaire le 19/01/04 car inutilisée  */
%mend Atter ;
/*__________________________________________________________________________________*/

/*__________________________________ Echantillonnage de la restitution
    									      du programme linéaire  */
%MACRO TIR_LP / STORE ;
/* Le 19 03 2004 : Si Simplex existe (Atter=B ou C, et Comment=Graphe), 
   on échantillonne directement dans Simplex afin de pouvoir y marquer
   (par Pris=Plan) l'échantillon tiré au sort (solution adoptée pour 
   éviter que la présence d'un échantillon de meme proba que l'échantillon 
   tiré ne provoque un deuxième point rouge dans le deuxième graphique,
   ce qui pouvait se produire car la variable Pris était issue d'un MERGE
   sur Plan=proba de chaque échantillon).                                           */
%IF %SYSFUNC(EXIST(Simplex)) %THEN
	%DO;
	DATA Simplex ;
		SET Simplex ;
		cum + Plan ;
		cum2 = LAG(cum) ;
		RETAIN cum2 0 ;
		CALL Symput('Limite',LEFT(PUT(ranuni(0),BEST12.))) ;
	RUN ;
	DATA One Simplex (DROP=cum cum2) ;
		SET Simplex ;
		IF cum2 < &limite <= cum THEN
			DO; 
				OUTPUT  One;
				Pris = Plan ;
				OUTPUT  Simplex;
			END;
		ELSE
			DO;
				OUTPUT  Simplex;
			END;
	RUN ;
	PROC TRANSPOSE DATA=One (DROP= Track Plan cum cum2 Pris) 
				   Out=Tone ;
	RUN ;
	%END;
%ELSE
	%DO;
	DATA One ;
		SET One ;
		cum + col1 ;
		cum2 = LAG(cum) ;
		RETAIN cum2 0 ;
		CALL Symput('Limite',LEFT(PUT(ranuni(0),BEST12.))) ;
	RUN ;
	DATA one  ;
		SET One ;
		IF cum2 < &limite <= cum THEN OUTPUT  ;
	RUN ;
	PROC TRANSPOSE DATA=One (DROP= col1 cum cum2) 
				   Out=Tone ;
	RUN ;
	%END;

/* Le 04 03 2004 : NECH_BC = nombre d'individus échantillonnés
				   pendant l'atterrissage (option B ou C)                           */
	%LET NECH_BC = 0 ; 
	DATA Tone ;
		MERGE Reste Tone ;
		If col1 = 1 ;
		KEEP &Id  ;
		CALL SYMPUT('NECH_BC',_N_) ;
	RUN ;

/* Le 03 03 2004 : on ne concatène les deux tables que si &Sortie existe   */
/* et si Tone a au moins une observation                                   */
/* Le 09 03 2004 : Pour ne plus risquer d'interférer avec la table &Sortie
   spécifiée par l'utilisateur, on nomme IdEch, au lieu de &Sortie, la table
   qui contient les identifiants des individus retenus dans l'échantillon  */

	%IF &NECH_BC NE 0 %THEN
		%DO;
			%IF %SYSFUNC(EXIST(IdEch)) %THEN
				%DO; 
					DATA IdEch ; 
   						SET IdEch Tone ;
					RUN ;
				%END;
			%ELSE
				%DO; 
					DATA IdEch ; 
 	  					SET Tone ;
					RUN ;
				%END;
		%END;
/* 	Si Nech_BC=0, il n'y a aucun identifiant à ajouter à IdEch                      */ 

%MEND TIR_LP ;
/*__________________________________________________________________________________*/

/*-------------------------------------------------------------------------*/
/* Les sorties de CUBE                                                     */
/* F TARDIEU 30/07/2001                                                    */
/*-------------------------------------------------------------------------*/
/* Le 21/10/2003 : Dans les graphiques, épaississement de la courbe        */
/* "taille des échantillons" et amélioration de la légende de l'axe des X. */
/*-------------------------------------------------------------------------*/
/* Le 30/10/2003 : Modification du commentaire en cas de somme des Pika non*/
/* entière et ajout d'un commentaire au cas où le nombre d'individus en    */
/* fin de vol est supérieur à la dimension de l'espace de contraintes.     */
/* Suppression de deux lignes blanches intempestives dans le commentaire   */
/* sur la colinéarité des contraintes.                                     */
/* Pour le calcul du rang on utilise 1/_P_ au lieu de _Pond_ car _Pond_ est*/
/* nulle pour les individus hors échantillons et ne doit etre utilisée que */
/* pour le calcul des estimateurs HT.                                      */
/*-------------------- Modification du 13/11/2003 -------------------------*/
/* Implantation d'un mode de calcul plus rapide du rang d'une matrice.     */
/*-------------------- Modification du 29/01/2004 -------------------------*/
/* Afin de pouvoir éditer les graphiques au-delà de 14 contraintes, on     */
/* évite d'avoir à transposer la table Simplex qui contient tous les       */
/* échantillons possibles (transposition impossible au-delà de 32767 obs). */
/*-------------------------------------------------------------------------*/	                          
/*----------------- Modifications du 13-15-16/02/2004 (SR)-----------------*/
/* Modification de l'affichage en output et des légendes graphiques        */
/*    Présentation générale 											   */
/*    Intitulés explicites des différentes sorties 					       */
/*    Affichage du nombre d'unités échantillonnées						   */
/*	  Affichage du lancement ou non de l'atterrissage					   */
/*-------------------------------------------------------------------------*/

%MACRO Bouillon_Cub (DataCub= ,
              Id=,
              Pi=,
			  Pond=,
              Contr=,
			  Atter= ) / STORE ; 
OPTIONS NODATE NOCENTER;
TITLE1  "            BILAN DE VOTRE ECHANTILLONNAGE                " ; 
TITLE2  "_______________________________________________________________";
PROC IML ;
  USE &DataCub   ;
  READ ALL VAR {&Contr} INTO  _Contr_  ;
  READ ALL VAR {&Pond}  INTO  _Pond_   ;
  /* Ne pas utiliser _Pond_ pour le calcul du rang
   car nulle pour les individus hors échantillon  */
  READ ALL VAR {&Pi}    INTO  _P_      ;
  READ ALL VAR {&Id}    INTO  _Id_     ;
  READ ALL VAR {PiStar} INTO _PiStar_  ; 
  READ ALL VAR {&sortie} INTO _sortie_  ;

Rest     = LOC(_Pistar_<1)                       ;
_Vol_    = SUM(_PiStar_[Rest])                   ;
_Alt_    = NCOL(LOC(_Pistar_>0))-NCOL(LOC(_PiStar_>=1)) ;	  
tire    = LOC(_sortie_) ;
_petitn_= Ncol(tire)  ;

/*_Xdilat_ = (_Contr_)#_Pond_ ;                  */

/*  Le 01 03 2004 : pour reconstituer _Xdilat_ (de façon à en calculer le rang) ,
	on se limite aux individus ayant des probas utiles, i.e. strictement
	comprise entre 0 et 1 (=individus présents au début de la phase de vol).
	Le fonction LOC n'acceptant pas les doubles inégalités on utilise l'inégalité
	x(x-1)<0 pour caractériser les nombres strictement compris entre 0 et 1.        */
/*_Xdilat_ = (_Contr_)#(_P_##(-1))                 ;                                 */
_Probas_utiles_ = LOC(_P_#(_P_ - 1) < 0) ; 
_Xdilat_ = (_Contr_[_Probas_utiles_,])#(_P_[_Probas_utiles_]##(-1))  ;

_Xdilat_Ech_ = (_Contr_)#_Pond_               ;/* Pour le calcul des estimateurs HT */

/* Utilisation de la méthode de calcul du rang fournie par Guillaume Chauvet        */
/* _Rang_   = ROUND(TRACE(GINV(_Xdilat_)*_Xdilat_)) ;                               */
_Noyau_ = HOMOGEN(BLOCK(_Xdilat_,0)) ;
_Rang_  = NROW(_Noyau_) - NCOL(_Noyau_) ;

_NbCon_  = NCOL(_Contr_)       ;

/*_________________ Verif sur somme des Pika ______________*/
Peu      = {0.00001} ;
Verif_   = ROUND(SUM(_PiStar_[Rest])) ;
IF (_Vol_ > Verif_ + peu ) | (_Vol_ < Verif_ - peu ) 
	THEN DO ; 
	Arrond = {1} ;			  
		Errare = 
{"Il reste à désigner un nombre non entier d'unités en fin de vol. ",
 "  Cela peut etre du à vos probabilités d'inclusion initiales,",
 "  ou à votre choix de ne pas contraindre la taille d'échantillon,",
 "  ou encore à la présence de valeurs individuelles très élevées",
 "  pour certaines contraintes (au delà de 10 puissance 8)",
  ""} ;  
		 END ;
	ELSE DO ; Arrond = {0} ; END ;				
 
/*_________________ Commentaires colinéarité des contraintes */	
com_col={"Certaines de vos contraintes sont colinéaires :",
			"Vos contraintes ne sont pas colinéaires : "};
com_con = {"Résumé des spécifications relatives aux contraintes   ",
	        "----------------------------------------------------",
			  "",
			  "    le nombre de variables d'équilibrage est    :     ",
  			  "    pour un espace des contraintes de dimension : "} ;
Nb_con  = _nbcon_//_rang_ ;
Nb_con  = CHAR(Nb_con,9,0); /* Conversion d'entiers au format*/
CarBlanc = {""};            /* caractère pour éditer un blanc*/
Nb_con = CarBlanc//CarBlanc//CarBlanc//Nb_con;/* en fin de 1ère ligne de Nb_con*/

/*____________________ Commentaire phase d'atterrissage      */
Com_res = {"A l'issue de la phase de vol                          ",
			  "----------------------------------------------------",
	  		  "Nombre d'individus sur lesquels il reste à statuer :  ",
			  "Nombre d'individus qu'il reste à échantillonner    :"}; 
		    
/*Blanc    = {.} ;*/
CarBlanc = {""};
_Alt2_  = CHAR(_Alt_,9,0);		
IF  arrond={0} 
	THEN DO ;	_Vol2_  = CHAR(_Vol_,9,0);		END;
	ELSE DO;    _Vol2_  = CHAR(_Vol_,9,2);		END; 
Nb_rest  = CarBlanc//CarBlanc//_Alt2_ //_Vol2_;
	
/*____Suspicion de dégénérescence de l'algorithme si Nb indiv*/
/*____restants > rang de la matrice des contraintes dilatées */
Dégén = {"Le nombre d'individus sur lesquels il reste à statuer en fin de vol     ",
         "est anormalement supérieur à la dimension de l'espace des contraintes.  ",
         "Il est possible que certaines contraintes dépassent 10 puissance 8"};
 
/*____________________ Commentaires qualité de l'équilibrage */
com_fin1 = {"Résultats obtenus  	                              ",
	  	    "----------------------------------------------------",
		    "Lancement de la phase d'atterrissage       :        "} ;
com_fin2 = {" ",
            "Nombre d'individus échantillonnés          :",
		    " ",
		    "1ère colonne : valeur réelle du total                ",
		    "2ème colonne : estimateur de Horvitz-Thompson du total",
		    "3ème colonne : écart relatif en pourcentage          "} ; 
nb=_petitn_;  
Nb  = CHAR(Nb,9,0); 
CarBlanc = {""};
 
IF (_Alt_= 0)
	THEN DO; 
		   	atterrir = {'      NON'} ; 
		   	com_fin = com_fin1 // com_fin2 ; 
		   	nb = CarBlanc // CarBlanc // atterrir // CarBlanc // nb ;
		 END;

	ELSE DO; 
		   	atterrir = {'      OUI'} ;			  
		  	option_atter = {"Option de la phase d'atterrissage          :"} ;
			option = {"        %UPCASE(&Atter)"} ;
			%IF (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C) %THEN
				%DO;
				  	fonction_cout = {"Critère de coût de la phase d'atterrissage :"} ;
					%IF %UPCASE(&Cout) = CV  %THEN
						%DO; cout = {"       CV"} ; %END;
					%ELSE
						%DO; cout = {"     DIST"} ; %END;
				  	com_fin = com_fin1 // option_atter // fonction_cout // com_fin2 ;
					nb = CarBlanc//CarBlanc//atterrir//option//cout//CarBlanc//nb ;
				%END;
			%ELSE
				%DO;
		  	com_fin = com_fin1 // option_atter // com_fin2 ;
			nb = CarBlanc // CarBlanc // atterrir // option // CarBlanc // nb ;
				%END;
		 END;

DO i=1 TO _NbCon_ ;
/*HT = HT||SUM(_Xdilat_[,i]) ;  après correction de _Xdilat_ on utilise _Xdilat_Ech_ */
  HT = HT||SUM(_Xdilat_Ech_[,i]) ;
  RE = RE||SUM(_Contr_[,i])  ;
END ;
_nom_={&contr};

TRE     = T(RE) ;
THT     = T(HT) ;
Uno     = SHAPE(1,NROW(TRE),1) ;
Cento   = SHAPE(100,NROW(TRE),1) ;

/* le 26 02 2004 : on affiche valeur manquante (.) si TRE=0 et THT<>0 */
/*                            et 0 si TRE=THT=0                       */
/*Rapp  = (  THT#(TRE##(-1)) - Uno)#Cento   ;                         */
  Rapp  = ( (THT-TRE)#(TRE##(-1)) )#Cento   ;

S       = SHAPE("|",NROW(TRE),1) ;	

/* On fait un peu joli ___________________________________ */ 
MATTRIB TRE
	ROWNAME = (_Nom_) 
	LABEL   = "Valeur réelle" ;
MATTRIB THT 
	ROWNAME = (_Nom_)
	LABEL   = "Valeur estimée" ; 	
MATTRIB Rapp 
	ROWNAME = (_Nom_)
	LABEL   = "Ecart relatif (en %)"
 	FORMAT  = 6.2 ;
MATTRIB S 
    LABEL = "" ; 
MATTRIB com_fin 
	LABEL = "" ;
MATTRIB com_con 
	LABEL = "" ;
MATTRIB nb_con 
	LABEL = "" ;
MATTRIB Com_res 
	LABEL = "" ;
MATTRIB Nb_Rest 
	LABEL = "" ;	
MATTRIB Nb 
	LABEL = "" ;  
MATTRIB Atterrir
	LABEL = "" ;
MATTRIB Option
	LABEL = "" ;
MATTRIB Cout
	LABEL = "" ;
MATTRIB Errare 
	LABEL = "Attention !...." ; 
MATTRIB Dégén 
	LABEL = " " ; 

/*_________________ Commentaires colinéarité des contraintes */	
/*IF _NbCon_ > _Rang_ THEN 
	PRINT (com_con[1,1]) ; 
	ELSE PRINT (com_con[2,1]) ;
PRINT (com_con[4:5,1]) nb_con ;  */
/* pour éviter les lignes blanches entre les deux PRINT      */
/* on recopie la ligne adéquate de com_col dans com_con      */
 IF _NbCon_ > _Rang_ THEN 
	com_con[3,1] = com_col[1,1] ; 
	ELSE com_con[3,1] = com_col[2,1] ;
PRINT com_con nb_con ;

/*____________________ Commentaire phase d'atterrissage      */
PRINT Com_res Nb_rest ;
IF Arrond[1,1] = 1 THEN  DO ; PRINT Errare ; END ;  

/*____Suspicion de dégénérescence de l'algorithme si Nb indiv*/
/*____restants > rang de la matrice des contraintes dilatées */
IF _Alt_ > _Rang_  THEN  PRINT (Dégén[1:3,1]);

/*____________________ Commentaires qualité de l'équilibrage */
PRINT Com_Fin nb;
PRINT TRE   S  THT   S  Rapp  ;
TITLE ;

/* Le 30 01 2004 : ajout aux commentaires sur la qualité de l'équilibrage          */
/* ABSCV = ABS(Rapp) ;          /* Valeurs Absolues des CV                         */
/* SABSCV = SUM(ABSCV) ;
/* Moyenne = SABSCV / _NbCon_ ; /* Moyenne des valeurs absolues des CV             */
/* MATTRIB Moyenne
	LABEL = "Moyenne des valeurs absolues des coefficients de variation" 
	FORMAT = 6.2 ;
PRINT moyenne ;
*/
QUIT;
 
/*************************************************************/
/*  Bilan graphique de l'échantillonnage de la phase de vol  */
/*************************************************************/
%IF (%UPCASE(&ATTER) = B OR %UPCASE(&ATTER) = C) 
	AND (%UPCASE(&Comment) = GRAPHE ) 
	AND (%SYSFUNC(EXIST(Simplex)))  
%THEN %DO ;

/* Le 29 01 2004 : suppression du calcul de nvar = nbre de variables     */
/* de la table Simplex, car cette table est la concaténation des tables  */
/* Track (1 var : Track), _Tutti_ (&Alt var : col1 à col&Alt) et Plan    */
/* (1 var : Plan), au lieu d'etre une table ayant nvar variables : col1  */
/* à col&nvar, ce qui permet de se passer de nvar en remplaçant :        */
/*   - col%EVAL(&NVar) par Plan                                          */
/*   - et col1 (de Simplex) par Track.                                   */
/* On évite ainsi d'avoir à transposer la table Simplex, opération       */
/* impossible si cette table a plus de 32767 observations, ce qui rendait*/
/* impossible l'éditiion des graphiques au-delà de 14 contraintes avec   */
/* l'option B d'atterrissage.                                            */
/*                                                                       */ 
/* PROC TRANSPOSE DATA=Simplex OUT=s;                                    */
/* RUN ;                                                                 */ 
/* DATA S ;                                                              */
/*   SET S ;                                                             */
/*   CALL SYMPUT('nvar',_n_) ;                                           */ 
/* RUN ;                                                                 */

DATA Simplex ; 
SET Simplex ;

/*	taille = Col2 %DO ik=3 %TO %EVAL(&Nvar-1) ;                          */ 
/*                  + col&Ik                                             */
	taille = Col1 %DO ik=2 %TO %EVAL(&Alt) ;   /* si %EVAL(&Alt)=1 on ne */
                    + col&Ik                   /* fait pas le %DO.       */ 
				  %END ;
	;
RUN ;

/* Le 19 03 2004 : Pour éviter la présence éventuelle d'un deuxième point rouge
   dans le graphique 2, à cause d'un échantillon ayant la meme proba que 
   l'échantillon tiré, la variable Pris de l'échantillon tiré est affectée dans
   %TIR_LP. 
   La PROC SORT et les deux étapes DATA suivantes sont donc mises en commentaire.   */
/*PROC SORT DATA=Simplex ;                                                          */ 
/*	BY col%EVAL(&NVar)  ;        */
/*	BY Plan  ;                                                                      */
/*RUN ;                                                                             */

/*DATA One ;                                                                        */ 
/*  SET One (KEEP = Col1);                                                          */
/*RENAME Col1 = col%EVAL(&NVar) ;*/
/*  RENAME Col1 = Plan ;                                                            */
/*RUN ;                                                                             */
 
/*DATA SImplex ;                                                                    */
/*  MERGE Simplex one (in=a) ;                                                      */
/*BY col%EVAL(&NVar) ;               */
/*IF a THEN Pris = col%EVAL(&NVar) ; */
/*  BY Plan ;                                                                       */
/*  IF a THEN Pris = Plan ;                                                         */
/*RUN ;                                                                             */

PROC SORT DATA=Simplex ;
 
/*  BY taille col1  DESCENDING col%EVAL(&NVar) ;     */
	BY taille Track DESCENDING Plan ;

RUN ;
DATA SImplex ;
  SET Simplex  ;
  I + 1 ;
/* Le 25 02 2004 création des variables utiles au graphique 2 :
	indic_premier_plan_non_nul et rang_dernier_plan_non_nul (I=numéro d'observation)*/
retain indic_premier_plan_non_nul 0 ; 
if plan>0 then 
	do;
		indic_premier_plan_non_nul = 1 ;
		call symput('rang_dernier_non_nul',I) ;
	end;

RUN ;

/*%LET Borne = %SYSEVALF(2**%EVAL(&NVAR-2)) ; en comm le 29 01 2004 car inutilisée  */

GOPTIONS RESET = GLOBAL  ;
TITLE1 H=1 
" " ;
TITLE2 H=1 
"Les différents échantillons envisagés par la phase d'atterrissage" ;
TITLE3 H=1
"selon leur taille, coût et probabilité de tirage ";
PROC GPLOT DATA=Simplex ;

/*PLOT (taille col%EVAL(&NVar) )*i / overlay  vref=0;    */
/*PLOT2 col1*i ;                                         */
  PLOT (taille Plan )*i / overlay  vref=0;
  PLOT2 Track*i ;

  SYMBOL1 I=STEPlJ l=33 w=2 C=BLUE   R=1 ;               
  SYMBOL2 V=Star   		  c=black  R=1 ;
  SYMBOL3 i=join   W=3      C=RED    R=1 ;

/*LABEL Col1 = "Fn de cout" ;                            */ 
  LABEL Track = "Fonction de coût" ;
  LABEL Taille = "Taille" ;
  LABEL i = "Numéro d'échantillon" ;
  Footnote "La hauteur des étoiles indique la probabilité de tirage des échantillons";
RUN ;
QUIT ;
GOPTIONS RESET = GLOBAL  ;

DATA _Null_ ;                                                                   
  SET SIMPLEX ;
  CALL SYMPUT('axeygrec',Taille) ;
RUN ;

TITLE1 H=1 
" " ;
TITLE2 H=1 
"L'échantillon tiré en phase d'atterrissage parmi les autres solutions";
TITLE3 H=1
"selon sa taille et sa probabilité de tirage "; 

PROC GPLOT DATA=Simplex ;

  PLOT taille*i /  vaxis = 0 to &axeygrec by 1 vref=0;

/*PLOT2 (col%EVAL(&Nvar) pris ) * i / overlay ;          */
  PLOT2 (Plan pris ) * i / overlay ;

  SYMBOL1 I=STEPlJ  l=33    w=2 C=BLUE  R=1 ;            
  SYMBOL2 V=Star    i=none	  C=black R=1 ;
  SYMBOL3 V=DOT   i=none  W=5   C=Red   R=1 ;
  LABEL i = "Numéro d'échantillon" ;
  Footnote  "L'échantillon choisi est repéré par le gros point rouge " ;
  LABEL Taille = "Taille" ;
/*LABEL col%Eval(&Nvar) = "Proba" ;         */
/*WHERE col%EVAL(&NVar) > 0 ;               */
  LABEL Plan = "Probabilité" ;

/* Le 25 02 2004 : on retient les échantillons situés entre le premier ayant
  	Plan>0 et le dernier ayant Plan>0 afin d'éviter que dans le graphique 2,
  	l'absence de tous les échantillons ayant Plan=0 ne provoque parfois une anomalie
	dans la courbe bleue des tailles d'échantillon (un décalage dans les points
   	de discontinuité de cette courbe)                                      */
/*WHERE Plan > 0 ;                                                         */

WHERE indic_premier_plan_non_nul = 1 and I <= &rang_dernier_non_nul ;

RUN ;
Footnote; /* pour effacer la footnote dans l'Output */
QUIT ;
	  %END ;
TITLE ;

/*_____________________________ Destruction des tables intermédiaires */

PROC DATASETS  NOLIST ;
  DELETE Plan Track Simplex	 /  MEMTYPE=DATA ;
RUN ;                             
QUIT ;

%MEND Bouillon_Cub ;
/*__________________________________________________________________________________*/
