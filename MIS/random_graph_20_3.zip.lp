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
edge(19, 1).
edge(1, 17).
edge(1, 16).
edge(12, 2).
edge(2, 11).
edge(2, 19).
edge(17, 3).
edge(3, 19).
edge(3, 2).
edge(6, 4).
edge(4, 12).
edge(4, 9).
edge(18, 5).
edge(5, 17).
edge(5, 15).
edge(16, 6).
edge(6, 12).
edge(6, 4).
edge(6, 7).
edge(7, 8).
edge(7, 1).
edge(15, 8).
edge(8, 5).
edge(8, 16).
edge(11, 9).
edge(9, 18).
edge(9, 12).
edge(19, 10).
edge(10, 12).
edge(10, 4).
edge(12, 11).
edge(11, 2).
edge(11, 7).
edge(1, 12).
edge(12, 7).
edge(12, 6).
edge(15, 13).
edge(13, 17).
edge(13, 14).
edge(16, 14).
edge(14, 19).
edge(14, 7).
edge(6, 15).
edge(15, 8).
edge(15, 17).
edge(2, 16).
edge(16, 5).
edge(16, 6).
edge(7, 17).
edge(17, 11).
edge(17, 3).
edge(13, 18).
edge(18, 3).
edge(18, 13).
edge(11, 19).
edge(19, 5).
edge(19, 13).
