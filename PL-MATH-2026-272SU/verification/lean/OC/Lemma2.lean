import OC.Lemma1

/-!
# Lemma 2: structure of an even family at every split

For a family `F` of paths `(0,0) → (n,n)` with pairwise even intersections and a
split point `t ≤ 2n`, group the words of `F` by the *signature* of their length-`t`
prefix: its N-count together with the set of `v ∈ F` whose prefix shares an odd
number of edges with it.  The prefix sets `P k` and suffix sets `Q k` of the classes
satisfy the hypotheses of Lemma 1 (the suffix sets after reversal), which gives
Shankar's bound `|F| ≤ 2^n`; if `|F| = 2^n` every class is a full product
`P k × Q k`, `2^n |P k| = 2^t |Q k|`, and `∑ |P k|² = 2^t`.
-/

namespace OC
open Finset

/-- A family of paths from `(0,0)` to `(n,n)` with pairwise even intersections. -/
structure EvenFam (F : Finset (List Bool)) (n : ℕ) : Prop where
  len : ∀ w ∈ F, w.length = 2 * n
  hn : ∀ w ∈ F, ht w = n
  even : ∀ w ∈ F, ∀ v ∈ F, c w v % 2 = 0

/-- common edges of two suffixes, counted from the end -/
def cs (y y' : List Bool) : ℕ := ce y y' ((ht y' : ℤ) - ht y)

@[simp] lemma ht_reverse (x : List Bool) : ht x.reverse = ht x := by
  simp [ht, List.count_reverse]

lemma ce_reverse (y y' : List Bool) (h : y.length = y'.length) (d : ℤ) :
    ce y.reverse y'.reverse d = ce y y' ((ht y' : ℤ) - ht y - d) := by
  induction y generalizing y' d with
  | nil =>
    cases y' with
    | nil => simp
    | cons b z' => simp at h
  | cons a z ih =>
    cases y' with
    | nil => simp at h
    | cons b z' =>
      have hl : z.length = z'.length := by simpa using h
      simp only [List.reverse_cons]
      rw [ce_append _ _ _ _ _ (by simpa using hl), ih z' hl, ce_cons, ce_cons, ce_nil_left,
        add_zero, add_comm]
      congr 1
      · simp only [ht_reverse]
        by_cases hab : a = b
        · subst hab
          have e : ((ht (a :: z') : ℤ) - ht (a :: z) - d = 0) ↔ (d + ht z - ht z' = 0) := by
            cases a <;> simp <;> omega
          simp only [true_and, e]
        · simp [hab]
      · congr 1
        cases a <;> cases b <;> simp [bz] <;> ring

lemma c_reverse (y y' : List Bool) (h : y.length = y'.length) :
    c y.reverse y'.reverse = cs y y' := by
  unfold c cs; rw [ce_reverse y y' h]; simp

section EvenFamFacts
variable {F : Finset (List Bool)} {n : ℕ}

lemma EvenFam.ht_take_add (hE : EvenFam F n) {w : List Bool} (hw : w ∈ F) (t : ℕ) :
    ht (w.take t) + ht (w.drop t) = n := by
  rw [← ht_append, List.take_append_drop]; exact hE.hn w hw

lemma EvenFam.len_take (hE : EvenFam F n) {w : List Bool} (hw : w ∈ F) {t : ℕ} (ht : t ≤ 2 * n) :
    (w.take t).length = t := by
  rw [List.length_take, hE.len w hw]; omega

lemma EvenFam.len_drop (hE : EvenFam F n) {w : List Bool} (hw : w ∈ F) (t : ℕ) :
    (w.drop t).length = 2 * n - t := by
  rw [List.length_drop, hE.len w hw]

/-- Fact 1 (splitting at `t`), mod 2. -/
lemma EvenFam.split_parity (hE : EvenFam F n) {w v : List Bool} (hw : w ∈ F) (hv : v ∈ F)
    {t : ℕ} (ht : t ≤ 2 * n) :
    (c (w.take t) (v.take t) + cs (w.drop t) (v.drop t)) % 2 = 0 := by
  have e := hE.even w hw v hv
  have hs : c w v = c (w.take t) (v.take t) + cs (w.drop t) (v.drop t) := by
    conv_lhs => rw [← List.take_append_drop t w, ← List.take_append_drop t v]
    unfold c cs
    rw [ce_append _ _ _ _ _ (by rw [hE.len_take hw ht, hE.len_take hv ht])]
    congr 1
    have h1 := hE.ht_take_add hw t
    have h2 := hE.ht_take_add hv t
    congr 1
    omega
  rw [← hs]; exact e

end EvenFamFacts

/-- the signature of the length-`t` prefix of `w` -/
def key (F : Finset (List Bool)) (t : ℕ) (w : List Bool) : ℕ × Finset (List Bool) :=
  (ht (w.take t), F.filter (fun v => c (w.take t) (v.take t) % 2 = 1))

/-- the class with signature `k` -/
def fib (F : Finset (List Bool)) (t : ℕ) (k : ℕ × Finset (List Bool)) : Finset (List Bool) :=
  F.filter (fun w => key F t w = k)

def Ks (F : Finset (List Bool)) (t : ℕ) : Finset (ℕ × Finset (List Bool)) := F.image (key F t)

/-- prefix set of a class -/
def P (F : Finset (List Bool)) (t : ℕ) (k : ℕ × Finset (List Bool)) : Finset (List Bool) :=
  (fib F t k).image (List.take t)

/-- suffix set of a class -/
def Q (F : Finset (List Bool)) (t : ℕ) (k : ℕ × Finset (List Bool)) : Finset (List Bool) :=
  (fib F t k).image (List.drop t)

section Signatures
variable {F : Finset (List Bool)} {n : ℕ}

lemma mem_fib {t : ℕ} {k} {w : List Bool} : w ∈ fib F t k ↔ w ∈ F ∧ key F t w = k := by
  simp [fib]

lemma mem_P {t : ℕ} {k} {x : List Bool} :
    x ∈ P F t k ↔ ∃ w ∈ F, key F t w = k ∧ w.take t = x := by
  simp [P, fib, and_assoc]

lemma mem_Q {t : ℕ} {k} {y : List Bool} :
    y ∈ Q F t k ↔ ∃ w ∈ F, key F t w = k ∧ w.drop t = y := by
  simp [Q, fib, and_assoc]

/-- equal signatures give equal parities against every prefix -/
lemma key_parity {t : ℕ} {w₁ w₂ v : List Bool} (hk : key F t w₁ = key F t w₂) (hv : v ∈ F) :
    c (w₁.take t) (v.take t) % 2 = c (w₂.take t) (v.take t) % 2 := by
  have h := congrArg (fun k => v ∈ k.2) hk
  simp only [key, Finset.mem_filter, hv, true_and, eq_iff_iff] at h
  rcases Nat.mod_two_eq_zero_or_one (c (w₁.take t) (v.take t)) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (c (w₂.take t) (v.take t)) with h2 | h2 <;>
  simp_all

lemma key_ht {t : ℕ} {w₁ w₂ : List Bool} (hk : key F t w₁ = key F t w₂) :
    ht (w₁.take t) = ht (w₂.take t) := congrArg Prod.fst hk

lemma key_of_take {t : ℕ} {w₁ w₂ : List Bool} (h : w₁.take t = w₂.take t) :
    key F t w₁ = key F t w₂ := by
  simp [key, h]

/-- the suffix also determines the signature -/
lemma EvenFam.key_of_drop (hE : EvenFam F n) {t : ℕ} (ht : t ≤ 2 * n) {w₁ w₂ : List Bool}
    (h₁ : w₁ ∈ F) (h₂ : w₂ ∈ F) (h : w₁.drop t = w₂.drop t) : key F t w₁ = key F t w₂ := by
  have a1 := hE.ht_take_add h₁ t
  have a2 := hE.ht_take_add h₂ t
  rw [h] at a1
  unfold key
  congr 1
  · omega
  · apply Finset.filter_congr
    intro v hv
    have p1 := hE.split_parity h₁ hv ht
    have p2 := hE.split_parity h₂ hv ht
    rw [h] at p1
    omega

end Signatures

end OC
