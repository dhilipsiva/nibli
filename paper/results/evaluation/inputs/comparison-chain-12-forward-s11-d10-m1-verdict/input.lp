earlier("N10","N12").
earlier("N12","N8").
earlier("N5","N0").
earlier("N1","N3").
earlier("N8","N7").
earlier("N2","N5").
earlier("N6","N9").
earlier("N0","N6").
earlier("N4","N1").
earlier("N11","N10").
earlier("N9","N4").
earlier("N3","N11").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N2","N7").
#show answer/1.
