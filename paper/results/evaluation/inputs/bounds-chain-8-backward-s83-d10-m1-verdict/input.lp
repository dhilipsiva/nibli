earlier("N8","N7").
earlier("N2","N4").
earlier("N4","N6").
earlier("N1","N0").
earlier("N6","N3").
earlier("N5","N2").
earlier("N0","N8").
earlier("N3","N1").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N7","N5").
#show answer/1.
