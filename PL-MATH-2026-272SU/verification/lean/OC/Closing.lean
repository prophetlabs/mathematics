import OC.Prefix

/-!
# The first closing step (Lemmas 3 and 4 of the write-up)

Context: `F` is extremal, every word of length `m` is a prefix of `F`, and
`m + 1 ≤ 2n`.  A word `x` of length `m` *takes* the letter `a` if `x ++ [a]` is a
prefix.  At split `m + 1` the class of `x ++ [a]` has one prefix if `x` takes both
letters and two prefixes if `x` takes only `a`; this gives the closing pairs.
-/

namespace OC
open Finset

structure Ctx (F : Finset (List Bool)) (n m : ℕ) : Prop where
  hE : EvenFam F n
  hF : F.card = 2 ^ n
  hall : ∀ x : List Bool, x.length = m → x ∈ pre F m
  hmt : m + 1 ≤ 2 * n

/-- `X` takes only E, `X'` takes only N, and `X E`, `X' N` lie in one class at `m + 1`. -/
def ClosingPair (F : Finset (List Bool)) (m : ℕ) (X X' : List Bool) : Prop :=
  X.length = m ∧ X'.length = m ∧ X ++ [false] ∈ pre F (m + 1) ∧ X ++ [true] ∉ pre F (m + 1) ∧
    X' ++ [true] ∈ pre F (m + 1) ∧ X' ++ [false] ∉ pre F (m + 1) ∧
    key F (m + 1) (X ++ [false]) = key F (m + 1) (X' ++ [true])

namespace Ctx
variable {F : Finset (List Bool)} {n m : ℕ} (C : Ctx F n m)
include C

lemma len_m {x : List Bool} (hx : x.length = m) (a : Bool) : (x ++ [a]).length = m + 1 := by
  simp [hx]

/-- every word of length `m` takes some letter -/
lemma takes_some {x : List Bool} (hx : x.length = m) : ∃ a, x ++ [a] ∈ pre F (m + 1) := by
  obtain ⟨y, hy⟩ := (mem_pre_iff_ext hx).mp (C.hall x hx)
  have hy' := mem_ext.mp hy
  have hl : y ≠ [] := by
    rintro rfl
    have := C.hE.len _ hy'
    simp [hx] at this
    have := C.hmt
    omega
  obtain ⟨b, y', rfl⟩ := List.exists_cons_of_ne_nil hl
  refine ⟨b, (mem_pre_iff_ext (C.len_m hx b)).mpr ⟨y', mem_ext.mpr ?_⟩⟩
  simpa using hy'

/-- the class of `x` at `m` is `{x}`; hence `|ext x| · 2^m = 2^n` -/
lemma ext_card {x : List Bool} (hx : x.length = m) : 2 ^ n = 2 ^ m * (ext F x).card := by
  have hm : m ≤ 2 * n := by have := C.hmt; omega
  have hxp := C.hall x hx
  have h1 : (P F m (key F m x)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨x, ?_⟩
    ext z
    rw [P_key_mem, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hk⟩
      obtain ⟨w', hw', rfl⟩ := mem_pre.mp hz
      obtain ⟨w, hw, rfl⟩ := mem_pre.mp hxp
      apply C.hE.single C.hF hm C.hall hw' hw
      rw [← key_self_take w', hk, key_self_take]
    · rintro rfl; exact ⟨hxp, rfl⟩
  have := C.hE.E2_pre C.hF hm hxp hx
  rw [h1, mul_one] at this
  exact this

lemma ext_split {x : List Bool} (hx : x.length = m) :
    (ext F x).card = (ext F (x ++ [false])).card + (ext F (x ++ [true])).card :=
  card_ext_split C.hE (by have := C.hmt; omega)

lemma ext_empty {x : List Bool} {a : Bool} (hx : x.length = m) (h : x ++ [a] ∉ pre F (m + 1)) :
    (ext F (x ++ [a])).card = 0 := by
  rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rwa [← mem_pre_iff_ext (C.len_m hx a)]

/-- the class at `m + 1` of a closer's extension has two prefixes -/
lemma card_closer {x : List Bool} {a : Bool} (hx : x.length = m) (ha : x ++ [a] ∈ pre F (m + 1))
    (hna : x ++ [!a] ∉ pre F (m + 1)) : (P F (m + 1) (key F (m + 1) (x ++ [a]))).card = 2 := by
  have e2 := C.hE.E2_pre C.hF C.hmt ha (C.len_m hx a)
  have e1 := C.ext_card hx
  have hs := C.ext_split hx
  have h0 := C.ext_empty hx hna
  have hext : (ext F (x ++ [a])).card = (ext F x).card := by
    cases a <;> simp at h0 <;> simp [h0] at hs <;> omega
  rw [hext, pow_succ, mul_assoc, mul_comm 2, ← mul_assoc, ← e1] at e2
  have : 0 < 2 ^ n := by positivity
  nlinarith

/-- the class at `m + 1` of an opener's extension has one prefix -/
lemma card_opener {x : List Bool} (hx : x.length = m) (h0 : x ++ [false] ∈ pre F (m + 1))
    (h1 : x ++ [true] ∈ pre F (m + 1)) (a : Bool) :
    (P F (m + 1) (key F (m + 1) (x ++ [a]))).card = 1 := by
  have ha : x ++ [a] ∈ pre F (m + 1) := by cases a <;> assumption
  have e2 := C.hE.E2_pre C.hF C.hmt ha (C.len_m hx a)
  have e1 := C.ext_card hx
  have hs := C.ext_split hx
  have n0 := (mem_pre_iff_ext (C.len_m hx false)).mp h0
  have n1 := (mem_pre_iff_ext (C.len_m hx true)).mp h1
  have c0 := n0.card_pos
  have c1 := n1.card_pos
  have hmem : x ++ [a] ∈ P F (m + 1) (key F (m + 1) (x ++ [a])) := P_key_mem.mpr ⟨ha, rfl⟩
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  have hlt : (ext F (x ++ [a])).card < (ext F x).card := by cases a <;> omega
  have : 2 ^ n * (P F (m + 1) (key F (m + 1) (x ++ [a]))).card < 2 ^ n * 2 := by
    rw [e2, pow_succ, e1]
    have : 0 < 2 ^ m := by positivity
    nlinarith
  have : (P F (m + 1) (key F (m + 1) (x ++ [a]))).card < 2 :=
    lt_of_mul_lt_mul_left this (Nat.zero_le _)
  omega

/-- Lemma 3 at the first closing step: a closer has a unique partner taking the other letter. -/
lemma partner {x : List Bool} {a : Bool} (hx : x.length = m) (ha : x ++ [a] ∈ pre F (m + 1))
    (hna : x ++ [!a] ∉ pre F (m + 1)) :
    ∃ x', x'.length = m ∧ x' ++ [!a] ∈ pre F (m + 1) ∧ x' ++ [a] ∉ pre F (m + 1) ∧
      key F (m + 1) (x' ++ [!a]) = key F (m + 1) (x ++ [a]) := by
  have h2 := C.card_closer hx ha hna
  have hmem : x ++ [a] ∈ P F (m + 1) (key F (m + 1) (x ++ [a])) := P_key_mem.mpr ⟨ha, rfl⟩
  obtain ⟨z', hz', hne⟩ := Finset.exists_mem_ne
    (s := P F (m + 1) (key F (m + 1) (x ++ [a]))) (by rw [h2]; norm_num) (x ++ [a])
  obtain ⟨hz'p, hz'k⟩ := P_key_mem.mp hz'
  have hz'l : z'.length = m + 1 := by
    obtain ⟨w, hw, rfl⟩ := mem_pre.mp hz'p
    exact C.hE.len_take hw C.hmt
  obtain ⟨x', b, rfl, hx'⟩ := exists_snoc hz'l
  -- the letter of the partner is the other one
  have hb : b = !a := by
    by_contra hb
    have hba : b = a := by cases a <;> cases b <;> simp_all
    subst hba
    have hxx : x' ≠ x := fun h => hne (by rw [h])
    obtain ⟨y, hy⟩ := (mem_pre_iff_ext (C.len_m hx b)).mp ha
    have hw₁ := mem_ext.mp hy
    have hw₂ := C.hE.transfer C.hF C.hmt (C.len_m hx b) hz'p hz'k.symm hw₁
    have hm : m ≤ 2 * n := by have := C.hmt; omega
    have hd : (x ++ [b] ++ y).drop m = (x' ++ [b] ++ y).drop m := by
      simp [List.drop_append, hx, hx']
    have hkk := C.hE.key_of_drop hm hw₁ hw₂ hd
    have := C.hE.single C.hF hm C.hall hw₁ hw₂ hkk
    simp [List.take_append, hx, hx'] at this
    exact hxx this.symm
  subst hb
  refine ⟨x', hx', hz'p, ?_, hz'k⟩
  intro hx'a
  -- otherwise `x'` would take both letters and its class would have one prefix
  have h0 : x' ++ [false] ∈ pre F (m + 1) := by cases a <;> simp_all
  have h1 : x' ++ [true] ∈ pre F (m + 1) := by cases a <;> simp_all
  have := C.card_opener hx' h0 h1 (!a)
  rw [hz'k, h2] at this
  omega

lemma closing_of_false {x : List Bool} (hx : x.length = m) (h0 : x ++ [false] ∈ pre F (m + 1))
    (h1 : x ++ [true] ∉ pre F (m + 1)) : ∃ X', ClosingPair F m x X' := by
  obtain ⟨x', hx', a1, a2, hk⟩ := C.partner (a := false) hx h0 (by simpa using h1)
  exact ⟨x', hx, hx', h0, h1, by simpa using a1, a2, hk.symm⟩

lemma closing_of_true {x : List Bool} (hx : x.length = m) (h1 : x ++ [true] ∈ pre F (m + 1))
    (h0 : x ++ [false] ∉ pre F (m + 1)) : ∃ X, ClosingPair F m X x := by
  obtain ⟨x', hx', a1, a2, hk⟩ := C.partner (a := true) hx h1 (by simpa using h0)
  exact ⟨x', hx', hx, by simpa using a1, a2, h1, h0, hk⟩

/-- every closer is in a closing pair -/
lemma closer_in_pair {x : List Bool} (hx : x.length = m)
    (hc : ¬ (x ++ [false] ∈ pre F (m + 1) ∧ x ++ [true] ∈ pre F (m + 1))) :
    (∃ X', ClosingPair F m x X') ∨ (∃ X, ClosingPair F m X x) := by
  obtain ⟨a, ha⟩ := C.takes_some hx
  cases a
  · exact Or.inl (C.closing_of_false hx ha (fun h => hc ⟨ha, h⟩))
  · exact Or.inr (C.closing_of_true hx ha (fun h => hc ⟨h, ha⟩))

lemma pair_unique_right {X X₁ X₂ : List Bool} (h₁ : ClosingPair F m X X₁)
    (h₂ : ClosingPair F m X X₂) : X₁ = X₂ := by
  obtain ⟨hX, hX₁, a0, a1, b1, -, k1⟩ := h₁
  obtain ⟨-, hX₂, -, -, b2, -, k2⟩ := h₂
  have h2 := C.card_closer (a := false) hX a0 (by simpa using a1)
  obtain ⟨p, q, hpq, hP⟩ := Finset.card_eq_two.mp h2
  have m0 : X ++ [false] ∈ P F (m + 1) (key F (m + 1) (X ++ [false])) := P_key_mem.mpr ⟨a0, rfl⟩
  have m1 : X₁ ++ [true] ∈ P F (m + 1) (key F (m + 1) (X ++ [false])) :=
    P_key_mem.mpr ⟨b1, k1.symm⟩
  have m2 : X₂ ++ [true] ∈ P F (m + 1) (key F (m + 1) (X ++ [false])) :=
    P_key_mem.mpr ⟨b2, k2.symm⟩
  rw [hP] at m0 m1 m2
  simp only [Finset.mem_insert, Finset.mem_singleton] at m0 m1 m2
  have n1 : X₁ ++ [true] ≠ X ++ [false] := by intro h; simpa using congrArg List.getLast? h
  have n2 : X₂ ++ [true] ≠ X ++ [false] := by intro h; simpa using congrArg List.getLast? h
  have : X₁ ++ [true] = X₂ ++ [true] := by
    rcases m0 with e | e <;> rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2 <;>
      first
      | exact e1.trans e2.symm
      | exact absurd (e1.trans e.symm) n1
      | exact absurd (e2.trans e.symm) n2
  exact List.append_cancel_right this

lemma pair_unique_left {X₁ X₂ X' : List Bool} (h₁ : ClosingPair F m X₁ X')
    (h₂ : ClosingPair F m X₂ X') : X₁ = X₂ := by
  obtain ⟨hX₁, hX', a1, -, b0, b1, k1⟩ := h₁
  obtain ⟨hX₂, -, a2, -, -, -, k2⟩ := h₂
  have h2 := C.card_closer (a := true) hX' b0 (by simpa using b1)
  obtain ⟨p, q, hpq, hP⟩ := Finset.card_eq_two.mp h2
  have m0 : X' ++ [true] ∈ P F (m + 1) (key F (m + 1) (X' ++ [true])) := P_key_mem.mpr ⟨b0, rfl⟩
  have m1 : X₁ ++ [false] ∈ P F (m + 1) (key F (m + 1) (X' ++ [true])) :=
    P_key_mem.mpr ⟨a1, k1⟩
  have m2 : X₂ ++ [false] ∈ P F (m + 1) (key F (m + 1) (X' ++ [true])) :=
    P_key_mem.mpr ⟨a2, k2⟩
  rw [hP] at m0 m1 m2
  simp only [Finset.mem_insert, Finset.mem_singleton] at m0 m1 m2
  have n1 : X₁ ++ [false] ≠ X' ++ [true] := by intro h; simpa using congrArg List.getLast? h
  have n2 : X₂ ++ [false] ≠ X' ++ [true] := by intro h; simpa using congrArg List.getLast? h
  have : X₁ ++ [false] = X₂ ++ [false] := by
    rcases m0 with e | e <;> rcases m1 with e1 | e1 <;> rcases m2 with e2 | e2 <;>
      first
      | exact e1.trans e2.symm
      | exact absurd (e1.trans e.symm) n1
      | exact absurd (e2.trans e.symm) n2
  exact List.append_cancel_right this

lemma pair_ht {X X' : List Bool} (h : ClosingPair F m X X') : ht X = ht X' + 1 := by
  obtain ⟨hX, hX', -, -, -, -, k⟩ := h
  have := key_ht k
  have e1 : (X ++ [false]).take (m + 1) = X ++ [false] := List.take_of_length_le (by simp [hX])
  have e2 : (X' ++ [true]).take (m + 1) = X' ++ [true] := List.take_of_length_le (by simp [hX'])
  rw [e1, e2] at this
  simpa using this

/-- condition (C) of Lemma 4 -/
lemma pair_parity {X X' : List Bool} (h : ClosingPair F m X X') {v : List Bool} (hv : v ∈ F) :
    c (X ++ [false]) (v.take (m + 1)) % 2 = c (X' ++ [true]) (v.take (m + 1)) % 2 := by
  obtain ⟨hX, hX', -, -, -, -, k⟩ := h
  have := key_parity k hv
  have e1 : (X ++ [false]).take (m + 1) = X ++ [false] := List.take_of_length_le (by simp [hX])
  have e2 : (X' ++ [true]).take (m + 1) = X' ++ [true] := List.take_of_length_le (by simp [hX'])
  rwa [e1, e2] at this

lemma pair_ne {X X' : List Bool} (h : ClosingPair F m X X') : X ≠ X' := by
  have := C.pair_ht h
  intro e; rw [e] at this; omega

/-- Lemma 4(b): a closing pair satisfies the parity condition (∗∗). -/
lemma pair_PC {X X' : List Bool} (h : ClosingPair F m X X') : PC m X X' := by
  have hX := h.1
  have hX' := h.2.1
  intro p hp h1 h2
  obtain ⟨b, hb⟩ := C.takes_some hp
  obtain ⟨v, hv, hvt⟩ := mem_pre.mp hb
  have e := C.pair_parity h hv
  rw [hvt, c_snoc _ _ _ _ (by rw [hX, hp]), c_snoc _ _ _ _ (by rw [hX', hp])] at e
  have n1 : ht X ≠ ht p := fun e => h1 e.symm
  have n2 : ht X' ≠ ht p := fun e => h2 e.symm
  simp [n1, n2] at e
  rw [c_comm p X, c_comm p X']
  exact e

/-- Lemma 4(a), segregation: no opener has the N-count of a member of a closing pair. -/
lemma segregation {X X' : List Bool} (h : ClosingPair F m X X') {v : List Bool}
    (hv : v.length = m) (h0 : v ++ [false] ∈ pre F (m + 1)) (h1 : v ++ [true] ∈ pre F (m + 1)) :
    ht v ≠ ht X ∧ ht v ≠ ht X' := by
  have hX := h.1
  have hX' := h.2.1
  have hht := C.pair_ht h
  obtain ⟨v0, hv0, e0⟩ := mem_pre.mp h0
  obtain ⟨v1, hv1, e1⟩ := mem_pre.mp h1
  have p0 := C.pair_parity h hv0
  have p1 := C.pair_parity h hv1
  rw [e0, c_snoc _ _ _ _ (by rw [hX, hv]), c_snoc _ _ _ _ (by rw [hX', hv])] at p0
  rw [e1, c_snoc _ _ _ _ (by rw [hX, hv]), c_snoc _ _ _ _ (by rw [hX', hv])] at p1
  have n1 : ht X' ≠ ht X := by omega
  have n2 : ht X ≠ ht X' := by omega
  constructor
  · intro hh
    simp [hh, n1] at p0 p1
    omega
  · intro hh
    simp [hh, n2] at p0 p1
    omega

/-- the two members of a closing pair have the same extensions -/
lemma pair_transfer {X X' : List Bool} (h : ClosingPair F m X X') (y : List Bool) :
    X ++ [false] ++ y ∈ F ↔ X' ++ [true] ++ y ∈ F := by
  obtain ⟨hX, hX', a0, -, b0, -, k⟩ := h
  constructor
  · exact C.hE.transfer C.hF C.hmt (C.len_m hX false) b0 k
  · exact C.hE.transfer C.hF C.hmt (C.len_m hX' true) a0 k.symm

end Ctx

end OC
