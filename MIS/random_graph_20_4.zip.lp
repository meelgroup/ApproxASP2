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
edge(18, 1).
edge(15, 1).
edge(1, 13).
edge(1, 11).
edge(9, 2).
edge(4, 2).
edge(2, 3).
edge(2, 7).
edge(15, 3).
edge(5, 3).
edge(3, 1).
edge(3, 7).
edge(18, 4).
edge(6, 4).
edge(4, 13).
edge(4, 15).
edge(19, 5).
edge(16, 5).
edge(5, 18).
edge(5, 1).
edge(12, 6).
edge(14, 6).
edge(6, 8).
edge(6, 12).
edge(6, 7).
edge(17, 7).
edge(7, 10).
edge(7, 15).
edge(10, 8).
edge(1, 8).
edge(8, 19).
edge(8, 9).
edge(12, 9).
edge(2, 9).
edge(9, 5).
edge(9, 13).
edge(16, 10).
edge(2, 10).
edge(10, 17).
edge(10, 8).
edge(3, 11).
edge(7, 11).
edge(11, 16).
edge(11, 10).
edge(8, 12).
edge(19, 12).
edge(12, 13).
edge(12, 9).
edge(9, 13).
edge(15, 13).
edge(13, 11).
edge(13, 7).
edge(5, 14).
edge(18, 14).
edge(14, 17).
edge(14, 6).
edge(5, 15).
edge(16, 15).
edge(15, 14).
edge(15, 10).
edge(8, 16).
edge(3, 16).
edge(16, 6).
edge(16, 8).
edge(19, 17).
edge(15, 17).
edge(17, 19).
edge(17, 11).
edge(17, 18).
edge(1, 18).
edge(18, 11).
edge(18, 5).
edge(8, 19).
edge(11, 19).
edge(19, 5).
edge(19, 13).
