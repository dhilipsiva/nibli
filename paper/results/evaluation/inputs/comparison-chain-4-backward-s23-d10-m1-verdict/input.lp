earlier("N1","N3").
earlier("N4","N1").
earlier("N3","N0").
earlier("N0","N2").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N2","N4").
#show answer/1.
