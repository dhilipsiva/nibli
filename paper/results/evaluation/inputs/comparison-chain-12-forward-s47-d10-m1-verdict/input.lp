earlier("N6","N1").
earlier("N8","N6").
earlier("N11","N0").
earlier("N9","N3").
earlier("N0","N10").
earlier("N12","N7").
earlier("N2","N12").
earlier("N3","N4").
earlier("N1","N5").
earlier("N10","N9").
earlier("N4","N2").
earlier("N7","N8").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N11","N5").
#show answer/1.
