earlier("N24","N15").
earlier("N30","N1").
earlier("N4","N22").
earlier("N26","N28").
earlier("N18","N14").
earlier("N15","N11").
earlier("N10","N18").
earlier("N21","N26").
earlier("N0","N30").
earlier("N16","N8").
earlier("N28","N2").
earlier("N32","N25").
earlier("N19","N23").
earlier("N6","N5").
earlier("N11","N7").
earlier("N12","N16").
earlier("N29","N6").
earlier("N25","N27").
earlier("N2","N9").
earlier("N13","N4").
earlier("N31","N20").
earlier("N7","N32").
earlier("N14","N17").
earlier("N20","N29").
earlier("N27","N3").
earlier("N8","N10").
earlier("N5","N24").
earlier("N17","N13").
earlier("N23","N12").
earlier("N3","N0").
earlier("N9","N31").
earlier("N1","N19").
earlier(A,C) :- earlier(A,B), earlier(B,C).
answer(0) :- earlier("N21","N22").
#show answer/1.
