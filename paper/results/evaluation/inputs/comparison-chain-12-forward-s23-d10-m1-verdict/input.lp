earlier("N2","N8").
earlier("N6","N11").
earlier("N11","N0").
earlier("N7","N9").
earlier("N8","N3").
earlier("N1","N4").
earlier("N9","N5").
earlier("N10","N2").
earlier("N5","N10").
earlier("N0","N1").
earlier("N3","N6").
earlier("N4","N12").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N7","N12").
#show answer/1.
