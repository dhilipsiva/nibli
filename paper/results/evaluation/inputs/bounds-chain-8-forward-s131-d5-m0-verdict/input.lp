earlier("N1","N3").
earlier("N4","N6").
earlier("N0","N4").
earlier("N8","N5").
earlier("N2","N7").
earlier("N3","N0").
earlier("N7","N1").
earlier("N6","N8").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N2","N5").
#show answer/1.
