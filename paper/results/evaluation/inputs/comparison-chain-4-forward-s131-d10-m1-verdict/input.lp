earlier("N3","N4").
earlier("N0","N3").
earlier("N1","N0").
earlier("N4","N2").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N1","N2").
#show answer/1.
