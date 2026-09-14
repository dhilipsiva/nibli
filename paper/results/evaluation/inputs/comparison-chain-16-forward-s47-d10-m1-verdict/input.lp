earlier("N16","N3").
earlier("N2","N11").
earlier("N6","N2").
earlier("N4","N5").
earlier("N1","N10").
earlier("N14","N13").
earlier("N10","N15").
earlier("N3","N14").
earlier("N12","N0").
earlier("N7","N8").
earlier("N0","N16").
earlier("N8","N6").
earlier("N9","N7").
earlier("N13","N4").
earlier("N15","N12").
earlier("N5","N9").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N1","N11").
#show answer/1.
