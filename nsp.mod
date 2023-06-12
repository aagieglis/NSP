int P = 10;  
int D = 21;
{string} Z = {"z1", "z2", "z3"};

// Koszty pracy na poszczególnych zmianach dla każdej pielęgniarki
tuple NurseShift {	
  int nurse;
  string shift;
  int cost;
}
{NurseShift} NurseShifts = {
  <1, "z1", 10>,
  <1, "z2", 8>,
  <1, "z3", 0>,
  <2, "z1", 9>,
  <2, "z2", 7>,
  <2, "z3", 0>,
  <3, "z1", 11>,
  <3, "z2", 9>,
  <3, "z3", 0>,
  <4, "z1", 12>,
  <4, "z2", 6>,
  <4, "z3", 0>,
  <5, "z1", 8>,
  <5, "z2", 9>,
  <5, "z3", 0>,
  <6, "z1", 10>,
  <6, "z2", 11>,
  <6, "z3", 0>,
  <7, "z1", 10>,
  <7, "z2", 8>,
  <7, "z3", 0>,
  <8, "z1", 9>,
  <8, "z2", 7>,
  <8, "z3", 0>,
  <9, "z1", 11>,
  <9, "z2", 9>,
  <9, "z3", 0>,
  <10, "z1", 11>,
  <10, "z2", 6>,
  <10, "z3", 0>};

// Zmienne decyzyjne
dvar boolean S[p in 1..P][d in 1..D][z in Z];

// Funkcja celu
minimize sum(p in 1..P, d in 1..D, z in Z) S[p][d][z] * first({ns.cost | ns in NurseShifts : ns.nurse == p && ns.shift == z});

// Ograniczenia
subject to {
    // Każdego dnia, na pierwszej i drugiej zmianie
  // zawsze muszą być co najmniej 3 pielęgniarki
  forall(z in Z)
    forall(d in 1..2)
      sum(p in 1..P) S[p][d][z] >= 3;
  
  // Każda pielęgniarka musi mieć zaplanowaną dokładnie jedną zmianę na każdy dzień.
  forall(p in 1..P, d in 1..D)
    sum(z in Z) S[p][d][z] == 1;

  // Pielęgniarka która byłana drugiej (nocnej) zmianie,
  // nie może w kolejny dzień pracować napierwszej (porannej) zmianie.
  forall(p in 1..P, d in 1..(D-1))
    S[p][d]["z2"] + S[p][d+1]["z1"] <= 1;

  // Żadna pielęgniarka nie może pracować siedem dni pod rząd.
  forall(p in 1..P, d in 1..(D-6))
  	sum(i in 0..6, z in Z) S[p][d+i][z] <= 7;

  // Żadna pielęgniarka nie może mieć więcej niż trzy dni wolnego pod rząd
  forall(p in 1..P, d in 1..(D-3))
  	sum(i in 0..3) S[p][d+i]["z3"] <= 3;
}
