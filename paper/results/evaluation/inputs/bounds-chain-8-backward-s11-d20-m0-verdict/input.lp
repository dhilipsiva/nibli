earlier("N1","N5").
earlier("N6","N0").
earlier("N2","N6").
earlier("N3","N8").
earlier("N5","N4").
earlier("N4","N3").
earlier("N0","N1").
earlier("N8","N7").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N7","N2").
#show answer/1.
