{ in(X,Y) : edge(X,Y) } = 1 :- node(Y), not first(Y).

first(X) :- X = #min { Y: node(Y) }.

connected(1, Y) :- in(1, Y).
connected(X, Y) :- connected(X, Z), in(Z, Y).

%:- node(Y), first(X), X != Y, not connected(X, Y).

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
edge(10, 1).
edge(16, 1).
edge(14, 1).
edge(1, 13).
edge(1, 3).
edge(1, 18).
edge(17, 2).
edge(13, 2).
edge(1, 2).
edge(2, 1).
edge(2, 9).
edge(2, 17).
edge(19, 3).
edge(12, 3).
edge(4, 3).
edge(3, 6).
edge(3, 19).
edge(3, 4).
edge(16, 4).
edge(1, 4).
edge(13, 4).
edge(4, 17).
edge(4, 5).
edge(4, 9).
edge(18, 5).
edge(9, 5).
edge(11, 5).
edge(5, 7).
edge(5, 8).
edge(5, 17).
edge(9, 6).
edge(11, 6).
edge(8, 6).
edge(6, 17).
edge(6, 18).
edge(6, 10).
edge(10, 7).
edge(14, 7).
edge(4, 7).
edge(7, 15).
edge(7, 16).
edge(7, 13).
edge(14, 8).
edge(12, 8).
edge(3, 8).
edge(8, 18).
edge(8, 1).
edge(8, 6).
edge(16, 9).
edge(2, 9).
edge(3, 9).
edge(9, 10).
edge(9, 16).
edge(9, 8).
edge(3, 10).
edge(8, 10).
edge(11, 10).
edge(10, 3).
edge(10, 12).
edge(10, 6).
edge(17, 11).
edge(3, 11).
edge(8, 11).
edge(11, 8).
edge(11, 7).
edge(11, 9).
edge(9, 12).
edge(11, 12).
edge(4, 12).
edge(12, 1).
edge(12, 19).
edge(12, 2).
edge(7, 13).
edge(14, 13).
edge(18, 13).
edge(13, 5).
edge(13, 8).
edge(13, 18).
edge(19, 14).
edge(9, 14).
edge(6, 14).
edge(14, 4).
edge(14, 10).
edge(14, 12).
edge(2, 15).
edge(16, 15).
edge(13, 15).
edge(15, 13).
edge(15, 1).
edge(15, 3).
edge(6, 16).
edge(2, 16).
edge(10, 16).
edge(16, 3).
edge(16, 11).
edge(16, 7).
edge(16, 17).
edge(9, 17).
edge(11, 17).
edge(17, 10).
edge(17, 1).
edge(17, 9).
edge(6, 18).
edge(15, 18).
edge(14, 18).
edge(18, 2).
edge(18, 11).
edge(18, 6).
edge(3, 19).
edge(15, 19).
edge(7, 19).
edge(19, 11).
edge(19, 1).
edge(19, 6).
