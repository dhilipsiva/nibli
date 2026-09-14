earlier("N3","N2").
earlier("N7","N3").
earlier("N6","N5").
earlier("N8","N0").
earlier("N5","N7").
earlier("N2","N8").
earlier("N1","N4").
earlier("N0","N1").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N6","N4").
#show answer/1.
