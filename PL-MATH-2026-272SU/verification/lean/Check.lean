import OC.Count

/-! Statements and axioms of the main results. -/

-- Shankar's Conjecture 4.1: exactly `catalan n` extremal families
#check @OC.conjecture_4_1
-- Classification: extremal even families = families built by adjacent insertions
#check @OC.extremal_iff_cat
-- Shankar's Theorem 1.4 (the bound), reproved
#check @OC.EvenFam.card_le
-- `c` counts common unit edges
#check @OC.c_eq_card_inter
-- Theorem C and Lemma D of the write-up
#check @OC.thmC
#check @OC.lemD

#print axioms OC.conjecture_4_1
#print axioms OC.extremal_iff_cat
#print axioms OC.EvenFam.card_le
