{ in(X,Y) : edge(X,Y) } = 1 :- node(Y), not first(Y).

first(X) :- X = #min { Y: node(Y) }.

connected(1, Y) :- in(1, Y).
connected(X, Y) :- connected(X, Z), in(Z, Y).

:- node(Y), first(X), X != Y, not connected(X, Y).
#show in/2.
% Nodes
node(1..6).
% (Directed) Edges
edge(1,(2;3;4)).  edge(2,(4;5;6)).  edge(3,(1;4;5)).
edge(4,(1;2)).    edge(5,(3;4;6)).  edge(6,(2;3;5)).