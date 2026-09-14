earlier("N0","N2").
earlier("N4","N1").
earlier("N3","N4").
earlier("N1","N0").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N2","N3").
#show answer/1.
