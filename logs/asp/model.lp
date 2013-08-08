% Simplest Model: 

% This model uses two variable: 
% is_car(Position,Type),
% is_option(Position,Option)
% The constraints are modelled with cardinality constraints

% Definitions

class(C) :- class_count(C,_). 
first(1).
last(N) :- N = #sum[class_count(_,K) = K ].
pos(F..L) :- first(F), last(L). 
next(D,DD) :- pos(D;DD), DD = D+1. 

window(1 .. N) :- N = #max[ option_window(_,W) = W ].
window(1,D,D) :- pos(D).
window(N,D1,D2) :- window(N;N-1), window(N-1,D1,D2).
window(N,DN,D1) :- window(N;N-1), window(N-1,DN,D2),next(D1,D2). 
              
% Model 

1 { is_car(P,C) : class(C) } 1 :- pos(P). 

:- class_count(C,S), not S { is_car(P,C) } S. 

is_option(P,O) :- is_car(P,C), class_option(C,O).

:- pos(P), option_window(O,W), option_max(O,M), 
   M+1 { is_option(PP,O) : window(W,P,PP) }.

% symmetry breaking

:- first(F), last(L), is_car(F,A), is_car(L,B), 
   A > B. 

% redundant constraints on options

:-  option_max(O,_), 
    N = #sum [class_count(A,C) = C : class_option(A,O)], 
    not N { is_option(_,O) } N. 

#hide.
#show is_car/2. 
#show is_option/2. 
