earlier("N3","N1").
earlier("N0","N8").
earlier("N2","N6").
earlier("N7","N2").
earlier("N1","N5").
earlier("N6","N4").
earlier("N8","N7").
earlier("N4","N3").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N5","N0").
#show answer/1.
