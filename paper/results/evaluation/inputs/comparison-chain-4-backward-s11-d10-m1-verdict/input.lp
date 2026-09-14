earlier("N2","N0").
earlier("N1","N4").
earlier("N0","N1").
earlier("N4","N3").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N3","N2").
#show answer/1.
