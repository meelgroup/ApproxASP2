%%
1 { path(X,Y) : edge(X,Y) } 1 :- vtx(Y), not start(Y).

reached(X) :- start(X).
reached(Y) :- reached(X), path(X,Y), { path(X,Z) : edge(X,Z), Z != Y } 0.

:- vtx(X), not reached(X).

#show path/2.
vtx(1). vtx(2). vtx(3). vtx(4). vtx(5). vtx(6). vtx(7). vtx(8). vtx(9). vtx(10). vtx(11). vtx(12). vtx(13). vtx(14). edge(1,2). edge(1,3). edge(1,4). edge(1,5). edge(3,5). edge(1,6). edge(3,6). edge(3,7). edge(4,7). edge(5,7). edge(6,7). edge(1,8). edge(2,8). edge(3,8). edge(4,8). edge(6,8). edge(3,9). edge(5,9). edge(6,9). edge(8,9). edge(1,10). edge(4,10). edge(5,10). edge(6,10). edge(7,10). edge(8,10). edge(9,10). edge(3,11). edge(4,11). edge(5,11). edge(7,11). edge(10,11). edge(1,12). edge(3,12). edge(5,12). edge(7,12). edge(8,12). edge(2,13). edge(3,13). edge(5,13). edge(6,13). edge(7,13). edge(10,13). edge(11,13). edge(12,13). edge(4,14). edge(5,14). edge(8,14). edge(9,14). edge(10,14). edge(11,14). edge(12,14). edge(14,12). edge(14,11). edge(14,10). edge(14,9). edge(14,8). edge(14,5). edge(14,4). edge(13,12). edge(13,11). edge(13,10). edge(13,7). edge(13,6). edge(13,5). edge(13,3). edge(13,2). edge(12,8). edge(12,7). edge(12,5). edge(12,3). edge(12,1). edge(11,10). edge(11,7). edge(11,5). edge(11,4). edge(11,3). edge(10,9). edge(10,8). edge(10,7). edge(10,6). edge(10,5). edge(10,4). edge(10,1). edge(9,8). edge(9,6). edge(9,5). edge(9,3). edge(8,6). edge(8,4). edge(8,3). edge(8,2). edge(8,1). edge(7,6). edge(7,5). edge(7,4). edge(7,3). edge(6,3). edge(6,1). edge(5,3). edge(5,1). edge(4,1). edge(3,1). edge(2,1). start(7).