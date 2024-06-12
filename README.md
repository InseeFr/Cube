# Cube

La macro SAS CUBE est un algorithme d’échantillonnage qui permet de tirer de manière aléatoire un échantillon équilibré sur un ensemble de totaux connus à partir d’informations auxiliaires disponibles dans la base de sondage. La méthode consiste à choisir un échantillon tel que les estimateurs d’Horvitz-Thompson des totaux des variables servant à l’équilibrage coïncident avec les vrais totaux.

La macro s’applique à partir de bases de sondage munies d’informations auxiliaires, qualitatives ou quantitatives, connues au niveau individuel.

Cette méthode permet d’améliorer la précision des estimateurs associés aux variables d’intérêt de l’enquête, dès lors que ces variables sont corrélées avec celles utilisées pour l’équilibrage.

Les principaux contributeurs à l'élaboration de cette macro sont Jean-Claude Deville et Yves Tillé pour la théorie de l'échantillonnage équilibré, et Frédéric Tardieu, Bernard Weytens et Guillaume Chauvet pour le développement de la macro CUBE permettant sa mise en œuvre.

La documentation disponible ici expose succinctement les aspects théoriques du tirage équilibré et détaille sa mise en oeuvre pratique, avec des exemples.

La compilation du code source mis à disposition ici s'effectue via les trois lignes de code suivantes :

    libname lib_cube 'Z:\Cube';
    options mstored sasmstore=lib_cube;
    %include 'Z:\Cube\Cube.sas';

où dans cet exemple, le code source de la macro (fichier Cube.sas) est stocké dans le répertoire « Z:\Cube », qui contiendra aussi la version compilée de la macro.

Pour utiliser ensuite cette version compilée de la macro dans un autre programme, il suffit de l'appeler en début de ce programme via les deux lignes de codes suivantes :

    libname lib_cube 'Z:\Cube';
    options mstored sasmstore=lib_cube;

Note : la macro CUBE utilise les modules SAS/IML et SAS/GRAPH du logiciel SAS.
