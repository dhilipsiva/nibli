earlier("N6","N2").
earlier("N11","N0").
earlier("N4","N10").
earlier("N3","N8").
earlier("N8","N4").
earlier("N5","N11").
earlier("N1","N12").
earlier("N2","N1").
earlier("N0","N6").
earlier("N9","N3").
earlier("N10","N5").
earlier("N12","N7").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N7","N9").
#show answer/1.
