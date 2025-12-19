%% Ejercicio 1: Buen Fin

articulo(pantalon).
articulo(chamarra).
articulo(sombrilla).

color(azul).
color(rojo).
color(amarillo).

descuento(10).
descuento(25).
descuento(50).

distintos(X,Y,Z) :- X \= Y, X \= Z, Y \= Z.

chamarra_azul(Articulo, _) :- Articulo \= chamarra.
chamarra_azul(chamarra, azul).

rojo_descuento(C, _, _, _) :- C \= rojo.
rojo_descuento(_, _, A, _) :- A \= sombrilla.
rojo_descuento(rojo, D1, sombrilla, D2) :- D1 > D2.

pantalon_descuento(Articulo,_) :- Articulo \= pantalon.
pantalon_descuento(pantalon, Descuento) :- Descuento \= 10.

tuplas(T1,T2,T3) :-
    T1 = t(curry, Articulo1, Color1, Descuento1),
    T2 = t(kleene, Articulo2, Color2, Descuento2),
    T3 = t(russell, Articulo3, Color3, Descuento3),
    articulo(Articulo1),
    articulo(Articulo2),
    articulo(Articulo3),
    color(Color1),
    color(Color2),
    color(Color3),
    descuento(Descuento1),
    descuento(Descuento2),
    descuento(Descuento3),
    distintos(Articulo1, Articulo2, Articulo3),
    distintos(Color1,Color2,Color3),
    distintos(Descuento1,Descuento2,Descuento3),
    chamarra_azul(Articulo1,Color1),
    chamarra_azul(Articulo2,Color2),
    chamarra_azul(Articulo3,Color3),
    Articulo1 \= chamarra,
    Descuento3 = 25,
    rojo_descuento(Color1, Descuento1, Articulo1, Descuento1),
    rojo_descuento(Color1, Descuento1, Articulo2, Descuento2),
    rojo_descuento(Color1, Descuento1, Articulo3, Descuento3),
    rojo_descuento(Color2, Descuento2, Articulo1, Descuento1),
    rojo_descuento(Color2, Descuento2, Articulo2, Descuento2),
    rojo_descuento(Color2, Descuento2, Articulo3, Descuento3),
    rojo_descuento(Color3, Descuento3, Articulo1, Descuento1),
    rojo_descuento(Color3, Descuento3, Articulo2, Descuento2),
    rojo_descuento(Color3, Descuento3, Articulo3, Descuento3),
    pantalon_descuento(Articulo1,Descuento1),
    pantalon_descuento(Articulo2,Descuento2),
    pantalon_descuento(Articulo3,Descuento3),
    Articulo1 \= pantalon,
    Articulo2 \= pantalon.

%% Ejercicio 2:

particion(L1, L2, L3) :- length(L1, N),
                        Mitad is N // 2,  % División entera
                        auxiliar(L1, L2, L3, Mitad),
                        !.   

auxiliar([], [], [], _).
auxiliar([X|XS], [X|L2], L3, N) :- N > 0,
                                    N1 is N - 1,
                                    auxiliar(XS, L2, L3, N1).

auxiliar([X|XS], L2, [X|L3], N) :- N = 0,
                                    auxiliar(XS, L2, L3, N).

%% Ejercicio 3:

combina([], L, L).
combina(L, [], L).
combina([X|XS], [Y|YS], [X|L2]) :- X =< Y, combina(XS, [Y|YS], L2).
combina([X|XS], [Y|YS], [Y|L2]) :- X > Y, combina([X|XS], YS, L2).


%% Ejercicio 4:

%% Para este Ejercicio seguimos la idea del algoritmo de euclides
%% para el maximo comun divisor, donde sabemos que mcd(x,0) = x y
%% mcd(a,b) = mcd(b,a%b) (% es la operación mod).
%% Así, sabemos que Z es mcd de X y Y sii Z es mcd de Y y X%Y

gcd(X, 0, X).
gcd(X, Y, Z) :- Y > 0, Modulo is X mod Y, gcd(Y, Modulo, Z).

%% Dos números son cooprimos si mcd es 1.
coprimos(X, Y) :- gcd(X, Y, GCD), GCD == 1.

%% Ejercicio 5:

agrupa([],[]).
agrupa([E],[[E]]).
agrupa([X,Y|XS], [[X|L1]|L2]) :- X==Y, agrupa([Y|XS], [L1|L2]).
agrupa([X,Y|XS], [[X]|L2]) :- X\=Y, agrupa([Y|XS], L2).

%% Ejercicio 6:

pertenece(E,[E|_]).
pertenece(E,[_|XS]) :- pertenece(E,XS).

%% Ejercicio 7:

elimina(_,[],[]).
elimina(X,[X|XS],XS).
elimina(A,[X|XS],[X|YS]) :- elimina(A,XS,YS).

%% Ejercicio 8:

% Base de conocimientos con las puertas entre cuartos
puerta(a, b).
puerta(b, a).
puerta(b, c).
puerta(b, e).
puerta(c, b).
puerta(c, d).
puerta(d, c).
puerta(d, e).
puerta(e, d).
puerta(e, b).
puerta(e, f).
puerta(e, g).
puerta(g, e).

camino(X, Y, XS) :-
    camino_aux(X, Y, [X], XS).

camino_aux(Y, Y, V, XS) :-
    reverse(V, XS).

camino_aux(X, Y, V, XS) :-
    puerta(X, N),
    \+ pertenece(N, V), 
    camino_aux(N, Y, [N|V], XS).
