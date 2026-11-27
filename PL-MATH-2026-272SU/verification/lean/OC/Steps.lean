import OC.Closing

/-!
# Steps 1 and 2 of Section 4.7

Step 1: the zigzag pair never closes.  Step 2: every word of length `m` is a closer
paired with its sibling, the heavier sibling taking E.
-/

namespace OC
open Finset

lemma zig_head (r : ℕ) : (zig r).head? = some true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [zig]
    rcases h : zig r with _ | ⟨b, l⟩
    · simp [h] at ih
    · simp [h] at ih ⊢; exact ih

lemma zag_head (r : ℕ) : (zag r).head? = some false := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [zag]
    rcases h : zag r with _ | ⟨b, l⟩
    · simp [h] at ih
    · simp [h] at ih ⊢; exact ih

lemma head_append_of_ne_nil {l l' : List Bool} (h : l ≠ []) : (l ++ l').head? = l.head? := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => rfl

namespace Ctx
variable {F : Finset (List Bool)} {n m : ℕ} (C : Ctx F n m)
include C

/-- the shape of a closing pair, from Lemma 4 and Theorem C -/
lemma pair_shape {X X' : List Bool} (h : ClosingPair F m X X') :
    (∃ u, X = u ++ [true] ∧ X' = u ++ [false]) ∨ (∃ r, m = 2 * r + 1 ∧ X = zig r ∧ X' = zag r) := by
  have hht := C.pair_ht h
  rcases thmC m X X' h.1 h.2.1 (C.pair_ne h) (C.pair_PC h) with
    ⟨u, α, rfl, rfl⟩ | ⟨r, hr, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · left
    cases α
    · exfalso; simp at hht; omega
    · exact ⟨u, rfl, rfl⟩
  · exact Or.inr ⟨r, hr, rfl, rfl⟩
  · exfalso; simp at hht; omega

lemma closer_of_pair_left {X X' : List Bool} (h : ClosingPair F m X X') :
    ¬ (X ++ [false] ∈ pre F (m + 1) ∧ X ++ [true] ∈ pre F (m + 1)) :=
  fun hh => h.2.2.2.1 hh.2

lemma closer_of_pair_right {X X' : List Bool} (h : ClosingPair F m X X') :
    ¬ (X' ++ [false] ∈ pre F (m + 1) ∧ X' ++ [true] ∈ pre F (m + 1)) :=
  fun hh => h.2.2.2.2.2.1 hh.1

/-- a closer and an opener never share an N-count -/
lemma no_mix {y v : List Bool} (hy : y.length = m)
    (hyc : ¬ (y ++ [false] ∈ pre F (m + 1) ∧ y ++ [true] ∈ pre F (m + 1)))
    (hv : v.length = m) (h0 : v ++ [false] ∈ pre F (m + 1)) (h1 : v ++ [true] ∈ pre F (m + 1)) :
    ht v ≠ ht y := by
  rcases C.closer_in_pair hy hyc with ⟨Y', hp⟩ | ⟨Y, hp⟩
  · exact (C.segregation hp hv h0 h1).1
  · exact (C.segregation hp hv h0 h1).2

/-- Step 1: the zigzag pair does not close. -/
lemma no_zigzag (R : ℕ) (hR : 1 ≤ R) (hm : m = 2 * R + 1) (h : ClosingPair F m (zig R) (zag R)) :
    False := by
  obtain ⟨r, rfl⟩ : ∃ r, R = r + 1 := ⟨R - 1, by omega⟩
  have hX := h.1
  have hX' := h.2.1
  -- the zigzags with their last letters flipped
  set s1 := zig r ++ [true, true] with hs1
  set s2 := zag r ++ [false, false] with hs2
  have l1 : s1.length = m := by simp [hs1, hm]; ring
  have l2 : s2.length = m := by simp [hs2, hm]; ring
  have zR : zig (r + 1) = zig r ++ [true, false] := rfl
  have aR : zag (r + 1) = zag r ++ [false, true] := rfl
  have hz1 : (zig r).head? = some true := zig_head r
  have hz2 : (zag r).head? = some false := zag_head r
  have nz : zig r ≠ [] := by intro e; simp [e] at hz1
  have na : zag r ≠ [] := by intro e; simp [e] at hz2
  -- s1 takes both letters
  have op1 : s1 ++ [false] ∈ pre F (m + 1) ∧ s1 ++ [true] ∈ pre F (m + 1) := by
    by_contra hc
    rcases C.closer_in_pair l1 hc with ⟨Y', hp⟩ | ⟨Y, hp⟩
    · rcases C.pair_shape hp with ⟨u, hu, rfl⟩ | ⟨r', hr', hu, -⟩
      · have : u = zig r ++ [true] := by
          have := hu; simp only [hs1] at this
          exact (List.append_cancel_right (by simpa using this.symm))
        subst this
        exact h.2.2.2.1 (by simpa [zR] using hp.2.2.2.2.1)
      · have : r' = r + 1 := by omega
        subst this
        rw [zR, hs1] at hu
        simp at hu
    · rcases C.pair_shape hp with ⟨u, -, hu⟩ | ⟨r', hr', -, hu⟩
      · simp only [hs1] at hu
        have := congrArg List.getLast? hu
        simp at this
      · have : r' = r + 1 := by omega
        subst this
        have e := congrArg List.head? hu
        rw [hs1, head_append_of_ne_nil nz, hz1, aR, head_append_of_ne_nil na, hz2] at e
        simp at e
  -- s2 takes both letters
  have op2 : s2 ++ [false] ∈ pre F (m + 1) ∧ s2 ++ [true] ∈ pre F (m + 1) := by
    by_contra hc
    rcases C.closer_in_pair l2 hc with ⟨Y', hp⟩ | ⟨Y, hp⟩
    · rcases C.pair_shape hp with ⟨u, hu, -⟩ | ⟨r', hr', hu, -⟩
      · simp only [hs2] at hu
        have := congrArg List.getLast? hu
        simp at this
      · have : r' = r + 1 := by omega
        subst this
        have e := congrArg List.head? hu
        rw [hs2, head_append_of_ne_nil na, hz2, zR, head_append_of_ne_nil nz, hz1] at e
        simp at e
    · rcases C.pair_shape hp with ⟨u, rfl, hu⟩ | ⟨r', hr', -, hu⟩
      · have : u = zag r ++ [false] := by
          have := hu; simp only [hs2] at this
          exact (List.append_cancel_right (by simpa using this.symm))
        subst this
        exact h.2.2.2.2.2.1 (by simpa [aR] using hp.2.2.1)
      · have : r' = r + 1 := by omega
        subst this
        rw [aR, hs2] at hu
        simp at hu
  have ht1 : ht s1 = r + 3 := by simp [hs1]
  have ht2 : ht s2 = r := by simp [hs2]
  -- every word of N-count `r + 1` is a closer
  have cl : ∀ w : List Bool, w.length = m → ht w = r + 1 →
      ¬ (w ++ [false] ∈ pre F (m + 1) ∧ w ++ [true] ∈ pre F (m + 1)) := by
    intro w hw hwh hc
    have := (C.segregation h hw hc.1 hc.2).2
    simp at this
    exact this hwh
  -- every word of N-count `r + 1` ending in N is `zag (r + 1)`
  have forced : ∀ u : List Bool, (u ++ [true]).length = m → ht (u ++ [true]) = r + 1 →
      u ++ [true] = zag (r + 1) := by
    intro u hu hh
    rcases C.closer_in_pair hu (cl _ hu hh) with ⟨Y', hp⟩ | ⟨Y, hp⟩
    · rcases C.pair_shape hp with ⟨u', hu', rfl⟩ | ⟨r', hr', hu', -⟩
      · -- the partner would be a closer of N-count `r`, next to the opener `s2`
        have hu'' : u = u' := List.append_cancel_right hu'
        subst hu''
        have := C.no_mix hp.2.1 (C.closer_of_pair_right hp) l2 op2.1 op2.2
        rw [ht2] at this
        simp at hh this
        exact absurd hh.symm this
      · have : r' = r + 1 := by omega
        subst this
        rw [hu'] at hh
        simp at hh
    · rcases C.pair_shape hp with ⟨u', -, hu'⟩ | ⟨r', hr', -, hu'⟩
      · have := congrArg List.getLast? hu'
        simp at this
      · have : r' = r + 1 := by omega
        subst this
        exact hu'
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- m = 3: an explicit parity clash
    subst hr0
    have hm3 : m = 3 := by omega
    subst hm3
    have hENE : ¬ ([false, true, false] ++ [false] ∈ pre F 4 ∧ [false, true, false] ++ [true] ∈ pre F 4) :=
      cl [false, true, false] rfl rfl
    rcases C.closer_in_pair rfl hENE with ⟨Y', hp⟩ | ⟨Y, hp⟩
    · rcases C.pair_shape hp with ⟨u, hu, -⟩ | ⟨r', hr', hu, -⟩
      · have := congrArg List.getLast? hu; simp at this
      · have : r' = 1 := by omega
        subst this; simp [zig] at hu
    · rcases C.pair_shape hp with ⟨u, rfl, hu⟩ | ⟨r', hr', -, hu⟩
      · have hu' : u = [false, true] := by
          have := congrArg List.dropLast hu; simpa using this.symm
        subst hu'
        obtain ⟨v, hv, hvt⟩ := mem_pre.mp h.2.2.1
        have e := C.pair_parity hp hv
        rw [hvt] at e
        revert e
        decide
      · have : r' = 1 := by omega
        subst this; simp [zag] at hu
  · -- r ≥ 1: two different words would both be `zag (r + 1)`
    have e1 := forced (mkp r (r + 2)) (by simp [hm]; ring) (by simp)
    have e2 := forced (false :: mkp r (r + 1)) (by simp [hm]; ring) (by simp)
    have := e1.trans e2.symm
    obtain ⟨r0, rfl⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by omega⟩
    simp [mkp, List.replicate_succ] at this

/-- every closing pair is a sibling pair -/
lemma pair_sib {X X' : List Bool} (h : ClosingPair F m X X') :
    ∃ u, X = u ++ [true] ∧ X' = u ++ [false] := by
  rcases C.pair_shape h with hs | ⟨r, hr, rfl, rfl⟩
  · exact hs
  · rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; exact ⟨[], rfl, rfl⟩
    · exact absurd h (fun h => C.no_zigzag r hpos hr h)

/-- the closers of N-count `j` -/
def HasCloser (F : Finset (List Bool)) (m j : ℕ) : Prop :=
  ∃ y : List Bool, y.length = m ∧ ht y = j ∧ ¬ (y ++ [false] ∈ pre F (m + 1) ∧ y ++ [true] ∈ pre F (m + 1))

lemma all_of_has {j : ℕ} (hj : HasCloser F m j) {x : List Bool} (hx : x.length = m) (hxj : ht x = j) :
    ¬ (x ++ [false] ∈ pre F (m + 1) ∧ x ++ [true] ∈ pre F (m + 1)) := by
  obtain ⟨y, hy, hyj, hyc⟩ := hj
  intro hc
  exact C.no_mix hy hyc hx hc.1 hc.2 (hxj.trans hyj.symm)

lemma has_down {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ m) (hj : HasCloser F m j) : HasCloser F m (j - 1) := by
  set w := mkp (j - 1) (m - j) ++ [true] with hw
  have wl : w.length = m := by simp [hw]; omega
  have wh : ht w = j := by simp [hw]; omega
  rcases C.closer_in_pair wl (C.all_of_has hj wl wh) with ⟨Y', hp⟩ | ⟨Y, hp⟩
  · obtain ⟨u, hu, rfl⟩ := C.pair_sib hp
    refine ⟨u ++ [false], hp.2.1, ?_, C.closer_of_pair_right hp⟩
    rw [hu] at wh; simp at wh ⊢; omega
  · obtain ⟨u, -, hu⟩ := C.pair_sib hp
    have := congrArg List.getLast? hu
    simp [hw] at this

lemma has_up {j : ℕ} (h2 : j + 1 ≤ m) (hj : HasCloser F m j) : HasCloser F m (j + 1) := by
  set w := mkp j (m - j - 1) ++ [false] with hw
  have wl : w.length = m := by simp [hw]; omega
  have wh : ht w = j := by simp [hw]
  rcases C.closer_in_pair wl (C.all_of_has hj wl wh) with ⟨Y', hp⟩ | ⟨Y, hp⟩
  · obtain ⟨u, hu, -⟩ := C.pair_sib hp
    have := congrArg List.getLast? hu
    simp [hw] at this
  · obtain ⟨u, rfl, hu⟩ := C.pair_sib hp
    refine ⟨u ++ [true], hp.1, ?_, C.closer_of_pair_left hp⟩
    rw [hu] at wh; simp at wh ⊢; omega

/-- Step 2: every word of length `m` is a closer paired with its sibling. -/
theorem all_siblings (hnot : ∃ z : List Bool, z.length = m + 1 ∧ z ∉ pre F (m + 1))
    {x : List Bool} (hx : x.length = m) :
    (∃ u, x = u ++ [true] ∧ ClosingPair F m x (u ++ [false])) ∨
    (∃ u, x = u ++ [false] ∧ ClosingPair F m (u ++ [true]) x) := by
  -- a first closer
  obtain ⟨z, hz, hzn⟩ := hnot
  obtain ⟨x0, a, rfl, hx0⟩ := exists_snoc hz
  have hc0 : ¬ (x0 ++ [false] ∈ pre F (m + 1) ∧ x0 ++ [true] ∈ pre F (m + 1)) := by
    rintro ⟨h0, h1⟩; cases a <;> simp_all
  have start : HasCloser F m (ht x0) := ⟨x0, hx0, rfl, hc0⟩
  have hx0m : ht x0 ≤ m := hx0 ▸ ht_le_length x0
  have down : ∀ d, d ≤ ht x0 → HasCloser F m (ht x0 - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using start
    | succ d ih =>
      intro hd
      have := C.has_down (j := ht x0 - d) (by omega) (by omega) (ih (by omega))
      rwa [show ht x0 - d - 1 = ht x0 - (d + 1) by omega] at this
  have up : ∀ d, ht x0 + d ≤ m → HasCloser F m (ht x0 + d) := by
    intro d
    induction d with
    | zero => intro _; simpa using start
    | succ d ih =>
      intro hd
      exact C.has_up (j := ht x0 + d) (by omega) (ih (by omega))
  have hasx : HasCloser F m (ht x) := by
    have hxm : ht x ≤ m := hx ▸ ht_le_length x
    rcases le_total (ht x) (ht x0) with hle | hle
    · have := down (ht x0 - ht x) (by omega)
      rwa [show ht x0 - (ht x0 - ht x) = ht x by omega] at this
    · have := up (ht x - ht x0) (by omega)
      rwa [show ht x0 + (ht x - ht x0) = ht x by omega] at this
  rcases C.closer_in_pair hx (C.all_of_has hasx hx rfl) with ⟨Y', hp⟩ | ⟨Y, hp⟩
  · obtain ⟨u, rfl, rfl⟩ := C.pair_sib hp
    exact Or.inl ⟨u, rfl, hp⟩
  · obtain ⟨u, rfl, rfl⟩ := C.pair_sib hp
    exact Or.inr ⟨u, rfl, hp⟩

end Ctx

end OC
