dog("Ada").
dog("Bea").
cat("Bea").
animal(X) :- dog(X), not cat(X).
answer(0) :- animal("Ada").
answer(1) :- animal("Bea").
answer(2) :- animal("Cyd").
#show answer/1.
