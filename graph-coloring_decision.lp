1 { chosenColour(N,C) : colour(C) } 1 :- node(N).
 :- link(U,V), U < V, chosenColour(U,C), chosenColour(V,C).
 
node(1). node(2). node(3). node(4). node(5). node(6). node(7). node(8). node(9). node(10). node(11). node(12). link(1,3). link(2,3). link(3,4). link(1,5). link(4,5). link(1,6). link(2,6). link(3,6). link(1,7). link(4,7). link(5,7). link(1,8). link(2,8). link(3,8). link(4,8). link(5,8). link(7,8). link(1,9). link(5,9). link(6,9). link(8,9). link(2,10). link(3,10). link(4,10). link(5,10). link(7,10). link(1,11). link(2,11). link(3,11). link(4,11). link(5,11). link(8,11). link(10,11). link(4,12). link(5,12). link(6,12). link(7,12). link(9,12). link(10,12). link(12,10). link(12,9). link(12,7). link(12,6). link(12,5). link(12,4). link(11,10). link(11,8). link(11,5). link(11,4). link(11,3). link(11,2). link(11,1). link(10,7). link(10,5). link(10,4). link(10,3). link(10,2). link(9,8). link(9,6). link(9,5). link(9,1). link(8,7). link(8,5). link(8,4). link(8,3). link(8,2). link(8,1). link(7,5). link(7,4). link(7,1). link(6,3). link(6,2). link(6,1). link(5,4). link(5,1). link(4,3). link(3,2). link(3,1).
colour(red0).
colour(green0).
colour(blue0).
colour(yellow0).
colour(cyan0).
colour(white0).
colour(black0).
%colour(grey0).
