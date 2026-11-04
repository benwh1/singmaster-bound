import Singmaster

/-!
Run with `lake run`. It prints the main theorem and the axioms its proof uses.

`MRSTT` (Theorem 2.3 of the paper, Theorem 1.3 of Matomäki, Radziwiłł, Shao, Tao and
Teräväinen) is a *hypothesis* of the theorem, not an axiom, so it appears in the statement
rather than in the axiom list.
-/

#check @Singmaster.statement_of_mrstt
#print axioms Singmaster.statement_of_mrstt
