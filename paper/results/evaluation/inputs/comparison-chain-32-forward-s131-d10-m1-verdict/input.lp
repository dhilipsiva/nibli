earlier("N5","N31").
earlier("N11","N3").
earlier("N16","N24").
earlier("N23","N20").
earlier("N26","N4").
earlier("N24","N23").
earlier("N3","N27").
earlier("N14","N7").
earlier("N15","N14").
earlier("N31","N19").
earlier("N0","N9").
earlier("N18","N11").
earlier("N25","N8").
earlier("N8","N13").
earlier("N27","N0").
earlier("N13","N32").
earlier("N12","N2").
earlier("N19","N18").
earlier("N21","N30").
earlier("N17","N28").
earlier("N22","N15").
earlier("N30","N17").
earlier("N6","N1").
earlier("N7","N5").
earlier("N4","N10").
earlier("N28","N25").
earlier("N2","N16").
earlier("N29","N21").
earlier("N1","N26").
earlier("N32","N22").
earlier("N10","N29").
earlier("N9","N12").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N6","N20").
#show answer/1.
