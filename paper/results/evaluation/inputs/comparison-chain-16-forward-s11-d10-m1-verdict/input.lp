earlier("N4","N6").
earlier("N10","N15").
earlier("N7","N16").
earlier("N3","N9").
earlier("N9","N8").
earlier("N1","N12").
earlier("N13","N2").
earlier("N5","N4").
earlier("N0","N10").
earlier("N6","N1").
earlier("N11","N0").
earlier("N8","N7").
earlier("N15","N13").
earlier("N2","N3").
earlier("N12","N11").
earlier("N16","N14").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N5","N14").
#show answer/1.
