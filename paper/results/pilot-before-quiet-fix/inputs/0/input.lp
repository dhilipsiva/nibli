dog("Ada").
animal(X) :- dog(X).
alive(X) :- animal(X).
answer(0) :- alive("Ada").
answer(1) :- alive("Bea").
#show answer/1.
