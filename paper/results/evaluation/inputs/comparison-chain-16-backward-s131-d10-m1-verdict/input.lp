earlier("N0","N4").
earlier("N14","N15").
earlier("N16","N2").
earlier("N11","N10").
earlier("N6","N1").
earlier("N9","N5").
earlier("N15","N0").
earlier("N4","N6").
earlier("N3","N13").
earlier("N5","N16").
earlier("N1","N8").
earlier("N12","N11").
earlier("N7","N3").
earlier("N2","N14").
earlier("N13","N9").
earlier("N8","N12").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N10","N7").
#show answer/1.
