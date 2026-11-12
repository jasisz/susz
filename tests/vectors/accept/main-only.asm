# Susz 1 test vector: MAIN only (no PROOFS); varint, nat and string edges.
section MAIN
1 0 s:"A"               # name 1: A
2 1 18446744073709551615        # name 2: A.(2^64 - 1)
8 0                     # expr 0: Prop
18 0 1 0 1 0            # decl 0: axiom A : Prop
7 0                     # bvar 0
7 127                   # bvar 127
7 128                   # bvar 128
7 9223372036854775808   # bvar 2^63
7 18446744073709551615  # bvar 2^64 - 1
14 nat:0                # 0
14 nat:255              # 255
14 nat:256              # 256
14 nat:18446744073709551616     # 2^64
14 nat:1606938044258990275541962092341162602522202993782792835301376   # 2^200
15 s:"\0"               # NUL
15 s:"\xf4\x8f\xbf\xbf"         # U+10FFFF
counts 3 1 13 1
