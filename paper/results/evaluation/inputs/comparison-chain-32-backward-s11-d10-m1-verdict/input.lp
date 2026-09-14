earlier("N3","N25").
earlier("N22","N7").
earlier("N17","N0").
earlier("N25","N19").
earlier("N31","N5").
earlier("N20","N15").
earlier("N18","N27").
earlier("N13","N23").
earlier("N0","N10").
earlier("N27","N16").
earlier("N1","N24").
earlier("N12","N8").
earlier("N23","N1").
earlier("N32","N22").
earlier("N30","N3").
earlier("N5","N6").
earlier("N15","N31").
earlier("N9","N30").
earlier("N7","N26").
earlier("N8","N2").
earlier("N29","N28").
earlier("N2","N4").
earlier("N6","N18").
earlier("N21","N13").
earlier("N11","N12").
earlier("N24","N32").
earlier("N10","N11").
earlier("N16","N14").
earlier("N4","N9").
earlier("N19","N20").
earlier("N26","N17").
earlier("N14","N29").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N28","N21").
#show answer/1.
