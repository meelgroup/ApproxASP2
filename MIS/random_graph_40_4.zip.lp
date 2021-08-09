{ in(X,Y) : edge(X,Y) } = 1 :- node(Y), not first(Y).

first(X) :- X = #min { Y: node(Y) }.

connected(1, Y) :- in(1, Y).
connected(X, Y) :- connected(X, Z), in(Z, Y).

:- node(Y), first(X), X != Y, not connected(X, Y).

#show in/2.
#show connected/2.
node(1).
node(2).
node(3).
node(4).
node(5).
node(6).
node(7).
node(8).
node(9).
node(10).
node(11).
node(12).
node(13).
node(14).
node(15).
node(16).
node(17).
node(18).
node(19).
node(20).
node(21).
node(22).
node(23).
node(24).
node(25).
node(26).
node(27).
node(28).
node(29).
edge(20, 1).
edge(13, 1).
edge(1, 8).
edge(1, 10).
edge(23, 2).
edge(16, 2).
edge(2, 19).
edge(2, 1).
edge(10, 3).
edge(13, 3).
edge(3, 26).
edge(3, 12).
edge(17, 4).
edge(26, 4).
edge(4, 16).
edge(4, 15).
edge(8, 5).
edge(9, 5).
edge(5, 8).
edge(5, 21).
edge(7, 6).
edge(18, 6).
edge(6, 8).
edge(6, 17).
edge(2, 7).
edge(9, 7).
edge(7, 25).
edge(7, 27).
edge(14, 8).
edge(24, 8).
edge(8, 26).
edge(8, 23).
edge(20, 9).
edge(23, 9).
edge(9, 17).
edge(9, 16).
edge(1, 10).
edge(23, 10).
edge(10, 14).
edge(10, 27).
edge(21, 11).
edge(25, 11).
edge(11, 22).
edge(11, 12).
edge(22, 12).
edge(26, 12).
edge(12, 26).
edge(12, 23).
edge(22, 13).
edge(7, 13).
edge(13, 19).
edge(13, 5).
edge(12, 14).
edge(9, 14).
edge(14, 7).
edge(14, 6).
edge(10, 15).
edge(24, 15).
edge(15, 3).
edge(15, 9).
edge(3, 16).
edge(21, 16).
edge(16, 21).
edge(16, 13).
edge(9, 17).
edge(10, 17).
edge(17, 10).
edge(17, 25).
edge(11, 18).
edge(25, 18).
edge(18, 6).
edge(18, 28).
edge(21, 19).
edge(26, 19).
edge(19, 7).
edge(19, 25).
edge(25, 20).
edge(16, 20).
edge(20, 5).
edge(20, 25).
edge(11, 21).
edge(19, 21).
edge(21, 9).
edge(21, 19).
edge(2, 22).
edge(15, 22).
edge(22, 11).
edge(22, 24).
edge(20, 23).
edge(10, 23).
edge(23, 16).
edge(23, 27).
edge(7, 24).
edge(26, 24).
edge(24, 9).
edge(24, 25).
edge(19, 25).
edge(23, 25).
edge(25, 4).
edge(25, 3).
edge(12, 26).
edge(15, 26).
edge(26, 21).
edge(26, 23).
edge(22, 27).
edge(18, 27).
edge(27, 23).
edge(27, 16).
edge(14, 28).
edge(26, 28).
edge(28, 22).
edge(28, 29).
edge(8, 29).
edge(14, 29).
edge(29, 4).
edge(29, 15).
