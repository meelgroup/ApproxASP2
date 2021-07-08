%%
1 { assigned(X,P) : part(P) } 1 :- number(X).
:- assigned(X,P), assigned(Y,P), X <= Y, assigned(X+Y,P).

#show assigned/2.
number(1). number(2). number(3). number(4). number(5). number(6). number(7). number(8). part(1). part(2). part(3). part(4). part(5). part(6). part(7). part(8). part(9). 