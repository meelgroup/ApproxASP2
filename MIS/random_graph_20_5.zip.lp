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
edge(7, 1).
edge(12, 1).
edge(1, 5).
edge(1, 2).
edge(1, 19).
edge(16, 2).
edge(15, 2).
edge(2, 18).
edge(2, 3).
edge(2, 6).
edge(8, 3).
edge(18, 3).
edge(3, 8).
edge(3, 9).
edge(3, 17).
edge(2, 4).
edge(17, 4).
edge(4, 11).
edge(4, 5).
edge(4, 14).
edge(11, 5).
edge(10, 5).
edge(5, 7).
edge(5, 13).
edge(5, 18).
edge(7, 6).
edge(11, 6).
edge(6, 2).
edge(6, 9).
edge(6, 11).
edge(6, 7).
edge(1, 7).
edge(7, 10).
edge(7, 15).
edge(7, 9).
edge(9, 8).
edge(16, 8).
edge(8, 3).
edge(8, 4).
edge(8, 13).
edge(17, 9).
edge(10, 9).
edge(9, 12).
edge(9, 17).
edge(9, 5).
edge(14, 10).
edge(3, 10).
edge(10, 17).
edge(10, 7).
edge(10, 16).
edge(2, 11).
edge(1, 11).
edge(11, 15).
edge(11, 12).
edge(11, 5).
edge(19, 12).
edge(2, 12).
edge(12, 4).
edge(12, 7).
edge(12, 11).
edge(3, 13).
edge(15, 13).
edge(13, 10).
edge(13, 5).
edge(13, 16).
edge(13, 14).
edge(9, 14).
edge(14, 18).
edge(14, 11).
edge(14, 8).
edge(17, 15).
edge(2, 15).
edge(15, 3).
edge(15, 9).
edge(15, 6).
edge(13, 16).
edge(5, 16).
edge(16, 8).
edge(16, 10).
edge(16, 3).
edge(7, 17).
edge(6, 17).
edge(17, 13).
edge(17, 2).
edge(17, 18).
edge(3, 18).
edge(16, 18).
edge(18, 13).
edge(18, 15).
edge(18, 3).
edge(3, 19).
edge(9, 19).
edge(19, 1).
edge(19, 15).
edge(19, 12).
