# Susz 1 test vector: keys out of order.
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
19 0 1                  # frontier name 3: Ind
1 6 s:"mk"              # name 7: Ind.mk
19 0 1                  # frontier name 4: Ind.mk
1 6 s:"rec"             # name 8: Ind.rec
1 0 s:"u_1"             # name 9: u_1
1 0 s:"Eq"              # name 10: Eq
1 10 s:"refl"           # name 11: Eq.refl
19 0 1                  # frontier name 5: Eq.refl
1 0 s:"Quot"            # name 12: Quot
1 0 s:"String"          # name 13: String
19 0 1                  # frontier name 6: String
1 0 s:"L"               # name 14: L
1 0 s:"S"               # name 15: S
1 0 s:"Z"               # name 16: Z
19 0 1                  # frontier name 7: Z
3 0                     # level 1: succ zero
19 1 1                  # frontier level 1
6 4                     # level 2: param u
4 1 2                   # level 3: max 1 2
5 2 1                   # level 4: imax 2 1
6 9                     # level 5: param u_1
8 1                     # expr 0: Sort 1
19 2 1                  # frontier expr 0
9 1 0                   # expr 1: const Nat []
19 2 1                  # frontier expr 1
@d0 18 0 1 0 2 0        # decl 0: axiom Nat : expr 0
14 nat:0                # expr 2: 0
@d1 18 1 2 0 2 1 2 1 0 1 2      # decl 1: def Nat.zero : expr 1 := expr 2, regular 1, safe, all [2]
8 0                     # expr 3: Prop
7 0                     # expr 4: bvar 0
7 1                     # expr 5: bvar 1
7 2                     # expr 6: bvar 2
9 6 1 2                 # expr 7: const Ind [u]
9 7 1 2                 # expr 8: const Ind.mk [u]
12 0 0 8 2              # expr 9: forall (_ : Nat), Ind.{u}
8 5                     # expr 10: Sort u_1
12 0 0 4 1              # expr 11: forall (_ : Ind.{u}), Sort u_1
10 4 8                  # expr 12: app Ind.mk.{u} (bvar 0)
10 8 1                  # expr 13: app (bvar 1) expr 12
12 0 0 13 1             # expr 14: forall (_ : Nat), expr 13 (the minor premise)
10 9 11                 # expr 15: app (bvar 2) (bvar 0)
12 0 0 9 1              # expr 16: forall (_ : Ind.{u}), expr 15
12 0 0 3 1              # expr 17: forall (_ : expr 14), expr 16
12 1 0 7 1              # expr 18: forall {_ : expr 11}, expr 17 (the recursor's type)
10 14 15                # expr 19: app (bvar 1) (bvar 0)
11 0 0 19 1             # expr 20: fun (_ : Nat) => expr 19
11 0 0 7 1              # expr 21: fun (_ : expr 14) => expr 20
11 1 0 11 1             # expr 22: fun {_ : expr 11} => expr 21 (the rule's right side)
@d2 18 5 1 6 1 4 23 0 0 0 1 6 1 7 0 0 0 1 7 1 4 14 0 6 0 0 1 1 8 2 9 4 5 0 1 6 0 0 1 1 1 7 1 1 0   # decl 2: inductive Ind.{u} : Type, Ind.mk : Nat -> Ind, Ind.rec.{u_1, u}
8 2                     # expr 23: Sort u
12 0 0 19 21            # expr 24: forall (_ : bvar 1), Prop
12 0 0 21 1             # expr 25: forall (_ : bvar 0), expr 24
12 1 0 3 1              # expr 26: forall {_ : Sort u}, expr 25 (Eq's type)
9 10 1 2                # expr 27: const Eq [u]
10 1 23                 # expr 28: app expr 27 (bvar 1)
10 1 25                 # expr 29: app expr 28 (bvar 0)
10 1 26                 # expr 30: app expr 29 (bvar 0)
12 0 0 27 1             # expr 31: forall (_ : bvar 0), expr 30
12 1 0 9 1              # expr 32: forall {_ : Sort u}, expr 31 (Eq.refl's type)
@d3 18 5 1 10 1 4 7 0 2 1 1 10 1 11 0 0 0 1 11 1 4 1 0 10 0 2 0 0   # decl 3: inductive Eq.{u}, Eq.refl.{u}, no recursor
12 0 0 8 10             # expr 33: forall (_ : expr 25), Sort u
12 1 0 11 1             # expr 34: forall {_ : Sort u}, expr 33 (Quot's type)
@d4 18 4 12 1 4 1 0     # decl 4: quot Quot.{u} : expr 34, type
@d5 18 0 13 0 35 0      # decl 5: axiom String : expr 0
10 27 31                # expr 35: app Ind.mk.{u} (bvar 0)
13 0 35 34 1            # expr 36: let _ : Nat := 0; expr 35
@d6 18 3 14 1 4 30 1 0 1 14     # decl 6: opaque L.{u} : Ind.{u} := expr 36, all [L]
9 10 1 1                # expr 37: const Eq [level 1]
10 1 37                 # expr 38: app expr 37 Nat
9 2 0                   # expr 39: const Nat.zero []
10 2 1                  # expr 40: app expr 38 expr 39
10 1 39                 # expr 41: app expr 40 0
9 11 1 1                # expr 42: const Eq.refl [level 1]
10 1 42                 # expr 43: app expr 42 Nat
10 1 42                 # expr 44: app expr 43 0
@d7 18 2 15 0 4 1 1 15  # decl 7: theorem S : Nat.zero = 0 := Eq.refl 0 (in MAIN)
14 nat:256              # expr 45: 256
10 8 1                  # expr 46: app expr 38 256
10 1 2                  # expr 47: app expr 46 256
@d8 18 6 5 0 1 len:t cnt:t 1 5  # decl 8: theorem T : 256 = 256, proof in block t
15 s:"ok"               # expr 48: "ok"
8 3                     # expr 49: Sort (max 1 2)
8 4                     # expr 50: Sort (imax 2 1)
16 6 0 15               # expr 51: proj Ind 0 expr 36
@d9 18 0 16 0 52 1      # decl 9: unsafe axiom Z : expr 0
section PROOFS
block t decl=8
9 4 1 1                 # t0: const Ind.mk [level 1]
8 1                     # t1: Sort (level 1)
12 3 0 1 1              # t2: forall [_ : t1], t1
7 0                     # t3: bvar 0
11 3 0 5 1              # t4: fun [_ : expr 0] => t3
15 s:"a\0b\xf0\x9f\x8d\x8e"     # t5: NUL and a 4-byte character
9 6 0                   # t6: const String []
9 5 1 1                 # t7: const Eq.refl [level 1]
10 1 10                 # t8: app t7 expr 1
10 9 6                  # t9: app t0 t3
16 3 0 1                # t10: proj Ind 0 t9
10 3 1                  # t11: app t8 t10
11 2 7 14 1             # t12: fun {{Z : expr 1}} => t11
14 nat:256              # t13: 256
10 2 1                  # t14: app t12 t13
13 0 9 10 1             # t15: let _ : t6 := t5; t14
13 0 14 12 1            # t16: let _ : t2 := t4; t15 (the value)
section INDEX
10                      # decl-count
0 rel:MAIN:d0           # entry 0
1 rel:d0:d1             # entry 1
5 rel:d1:d2             # entry 2
5 rel:d2:d3             # entry 3
4 rel:d3:d4             # entry 4
0 rel:d4:d5             # entry 5
3 rel:d5:d6             # entry 6
2 rel:d6:d7             # entry 7
6 rel:d7:d8 len:t       # entry 8
0 rel:d8:d9             # entry 9
ntcount                 # name-count
nt L 6
nt T 8
nt S 7
nt Z 9
nt Eq 3
nt Eq.refl 3
nt Ind 2
nt Ind.mk 2
nt Ind.rec 2
nt Nat 0
nt Nat.zero 1
nt Quot 4
nt String 5
section SOURCE
x:7b2274657374223a747275657d    # {"test":true}
counts 17 6 52 10
