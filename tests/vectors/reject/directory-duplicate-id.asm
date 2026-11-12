# Susz 1 test vector: a section id given twice.
section MAIN
19 0 1                  # frontier name 0: the anonymous name
19 1 1                  # frontier level 0: level zero
1 0 s:"Nat"             # name 1: Nat
19 0 1                  # frontier name 1: Nat
1 1 s:"zero"            # name 2: Nat.zero
2 1 7                   # name 3: Nat.7
1 0 s:"u"               # name 4: u
1 0 s:"T"               # name 5: T
19 0 1                  # frontier name 2: T
1 0 s:"Ind"             # name 6: Ind
1 6 s:"mk"              # name 7: Ind.mk
1 6 s:"rec"             # name 8: Ind.rec
1 0 s:"Q"               # name 9: Q
1 0 s:"L"               # name 10: L
1 0 s:"S"               # name 11: S
1 0 s:"Z"               # name 12: Z
19 0 1                  # frontier name 3: Z
3 0                     # level 1: succ zero
19 1 1                  # frontier level 1
6 4                     # level 2: param u
4 1 2                   # level 3: max 1 2
5 2 1                   # level 4: imax 2 1
8 1                     # expr 0: Sort 1
19 2 1                  # frontier expr 0
9 1 0                   # expr 1: const Nat []
19 2 1                  # frontier expr 1
@d0 18 0 1 0 2 0        # decl 0: axiom Nat : expr 0
14 nat:0                # expr 2: 0
@d1 18 1 2 0 2 1 2 1 0 1 2      # decl 1: def Nat.zero : expr 1 := expr 2, regular 1, safe, all [2]
8 0                     # expr 3: Prop
12 0 0 3 1              # expr 4: forall (_ : expr 1), expr 3
15 s:"ok"               # expr 5: "ok"
7 0                     # expr 6: bvar 0
10 3 1                  # expr 7: app expr 4 expr 6
11 3 4 7 2              # expr 8: fun [u : expr 1] => expr 6
13 4 8 3 1              # expr 9: let u : expr 1 := expr 6; expr 8
@d2 18 5 1 6 1 4 10 0 0 0 1 6 1 7 0 0 0 1 7 1 4 9 0 6 0 0 0 1 8 0 6 0 1 6 0 0 1 1 1 7 0 2 1   # decl 2: inductive Ind, Ind.mk, Ind.rec
16 6 0 1                # expr 10: proj Ind 0 expr 9
@d3 18 4 9 0 8 0        # decl 3: quot Q : expr 3, type
8 3                     # expr 11: Sort (max 1 2)
8 4                     # expr 12: Sort (imax 2 1)
9 6 1 2                 # expr 13: const Ind [u]
@d4 18 3 10 1 4 1 2 0 1 10      # decl 4: opaque L.{u} : expr 13 := expr 12, all [L]
@d5 18 2 11 0 11 10 0   # decl 5: theorem S : expr 3 := expr 4 (in MAIN)
@d6 18 6 5 0 11 len:t cnt:t 1 5 # decl 6: theorem T : expr 3, proof in block t
@d7 18 0 12 0 14 1      # decl 7: unsafe axiom Z : expr 0
section PROOFS
block t decl=6
9 1 1 1                 # t0: const Nat [level 1]
8 1                     # t1: Sort (level 1)
10 2 3                  # t2: app t0 expr 0
11 1 0 1 5              # t3: fun {_ : t2} => expr 1
16 1 0 1                # t4: proj Nat 0 t3
14 nat:256              # t5: 256
15 s:"a\0b\xf0\x9f\x8d\x8e"     # t6: NUL and a 4-byte character
7 3                     # t7: bvar 3
13 0 1 2 8              # t8: let _ : t7 := t6; t0
12 2 1 1 10             # t9: forall {{Nat : t8}}, expr 0 (the value)
section INDEX
8                       # decl-count
0 rel:MAIN:d0           # entry 0
1 rel:d0:d1             # entry 1
5 rel:d1:d2             # entry 2
4 rel:d2:d3             # entry 3
3 rel:d3:d4             # entry 4
2 rel:d4:d5             # entry 5
6 rel:d5:d6 len:t       # entry 6
0 rel:d6:d7             # entry 7
ntcount                 # name-count
nt L 4
nt Q 3
nt S 5
nt T 6
nt Z 7
nt Ind 2
nt Ind.mk 2
nt Ind.rec 2
nt Nat 0
nt Nat.zero 1
section SOURCE id=5
x:7b2274657374223a747275657d    # {"test":true}
counts 13 5 14 8
