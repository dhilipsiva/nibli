earlier("N4","N3").
earlier("N2","N0").
earlier("N1","N2").
earlier("N0","N4").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N1","N3").
#show answer/1.
