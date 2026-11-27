import OC.Steps

/-!
# The classification of extremal even families (Step 3 and the induction)

`Cat n F` says that `F` is obtained from `{ε}` by `n` successive insertions of the
pair `NE`/`EN` at two adjacent positions.  These are exactly the families `F_M` of
noncrossing perfect matchings `M` (see `Matching.lean`).

Main theorem (`extremal_iff_cat`): a family `F` of paths `(0,0) → (n,n)` has pairwise
even intersections and `2^n` members if and only if `Cat n F`.
-/

namespace OC
open Finset

/-- insert the adjacent pair `a, !a` at position `i` -/
def insPair (i : ℕ) (a : Bool) (w : List Bool) : List Bool := w.take i ++ [a, !a] ++ w.drop i

/-- insert `NE` or `EN` at position `i` into every word of `G` -/
def InsFam (i : ℕ) (G : Finset (List Bool)) : Finset (List Bool) :=
  G.biUnion (fun w => {insPair i true w, insPair i false w})

/-- the families obtained from `{ε}` by successive adjacent insertions -/
inductive Cat : ℕ → Finset (List Bool) → Prop
  | zero : Cat 0 {[]}
  | step {n : ℕ} {G : Finset (List Bool)} (i : ℕ) : i ≤ 2 * n → Cat n G → Cat (n + 1) (InsFam i G)

/-- inserting an adjacent pair changes the number of common edges by 0 or 2 -/
lemma c_ins (u₁ u₂ y₁ y₂ : List Bool) (a₁ a₂ : Bool) (hu : u₁.length = u₂.length) :
    c (u₁ ++ [a₁, !a₁] ++ y₁) (u₂ ++ [a₂, !a₂] ++ y₂) =
      c (u₁ ++ y₁) (u₂ ++ y₂) + (if a₁ = a₂ ∧ ht u₁ = ht u₂ then 2 else 0) := by
  unfold c
  rw [List.append_assoc, List.append_assoc, ce_append _ _ _ _ _ hu, ce_append _ _ _ _ _ hu,
    ce_append [a₁, !a₁] [a₂, !a₂] y₁ y₂ _ rfl]
  have h1 : ht [a₁, !a₁] = 1 := by cases a₁ <;> rfl
  have h2 : ht [a₂, !a₂] = 1 := by cases a₂ <;> rfl
  rw [h1, h2]
  simp only [Nat.cast_one, add_sub_cancel_right]
  have hc : ce [a₁, !a₁] [a₂, !a₂] (0 + ↑(ht u₁) - ↑(ht u₂)) =
      if a₁ = a₂ ∧ ht u₁ = ht u₂ then 2 else 0 := by
    cases a₁ <;> cases a₂ <;> simp [ce_cons, bz] <;> split_ifs <;> omega
  rw [hc]; ring

lemma length_insPair (i : ℕ) (a : Bool) {w : List Bool} (h : i ≤ w.length) :
    (insPair i a w).length = w.length + 2 := by
  simp [insPair, List.length_take, List.length_drop]; omega

lemma ht_insPair (i : ℕ) (a : Bool) (w : List Bool) : ht (insPair i a w) = ht w + 1 := by
  have : ht w = ht (w.take i) + ht (w.drop i) := by rw [← ht_append, List.take_append_drop]
  cases a <;> simp [insPair, this] <;> ring

lemma insPair_inj {i : ℕ} {a a' : Bool} {g g' : List Bool} (hg : i ≤ g.length) (hg' : i ≤ g'.length)
    (h : insPair i a g = insPair i a' g') : a = a' ∧ g = g' := by
  have lt : (g.take i).length = i := by simp [List.length_take]; omega
  have lt' : (g'.take i).length = i := by simp [List.length_take]; omega
  unfold insPair at h
  rw [List.append_assoc, List.append_assoc] at h
  have e1 := congrArg (List.take i) h
  have e2 := congrArg (List.drop i) h
  rw [List.take_left' lt, List.take_left' lt'] at e1
  rw [List.drop_left' lt, List.drop_left' lt'] at e2
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at e2
  refine ⟨e2.1, ?_⟩
  rw [← List.take_append_drop i g, ← List.take_append_drop i g', e1, e2.2.2]

lemma card_InsFam {i : ℕ} {G : Finset (List Bool)} (hG : ∀ g ∈ G, i ≤ g.length) :
    (InsFam i G).card = 2 * G.card := by
  unfold InsFam
  rw [Finset.card_biUnion]
  · rw [Finset.sum_const_nat (m := 2), mul_comm]
    intro g hg
    rw [Finset.card_pair]
    intro h
    have := (insPair_inj (hG g hg) (hG g hg) h).1
    simp at this
  · intro g hg g' hg' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    apply hne
    rcases hw with rfl | rfl <;> rcases hw' with h | h <;>
      exact (insPair_inj (hG g hg) (hG g' hg') h).2

/-- the converse direction: every `Cat` family is even and has `2^n` members -/
theorem cat_extremal : ∀ {n : ℕ} {F : Finset (List Bool)}, Cat n F → EvenFam F n ∧ F.card = 2 ^ n := by
  intro n F h
  induction h with
  | zero =>
    refine ⟨⟨?_, ?_, ?_⟩, by simp⟩ <;> simp
  | @step n G i hi _ ih =>
    obtain ⟨hE, hG⟩ := ih
    have hlen : ∀ g ∈ G, i ≤ g.length := fun g hg => by rw [hE.len g hg]; exact hi
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro w hw
      simp only [InsFam, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hw
      obtain ⟨g, hg, rfl | rfl⟩ := hw <;> rw [length_insPair _ _ (hlen g hg), hE.len g hg] <;> ring
    · intro w hw
      simp only [InsFam, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hw
      obtain ⟨g, hg, rfl | rfl⟩ := hw <;> rw [ht_insPair, hE.hn g hg]
    · intro w hw v hv
      simp only [InsFam, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hw hv
      obtain ⟨g, hg, hw⟩ := hw
      obtain ⟨g', hg', hv⟩ := hv
      have lt : (g.take i).length = (g'.take i).length := by
        simp [List.length_take, hE.len g hg, hE.len g' hg']
      have key : ∀ a a' : Bool, c (insPair i a g) (insPair i a' g') % 2 = 0 := by
        intro a a'
        unfold insPair
        rw [c_ins _ _ _ _ _ _ lt, List.take_append_drop, List.take_append_drop]
        have := hE.even g hg g' hg'
        split_ifs <;> omega
      rcases hw with rfl | rfl <;> rcases hv with rfl | rfl <;> exact key _ _
    · rw [card_InsFam hlen, hG]; ring

/-- **Main theorem** (classification): every extremal even family is a `Cat` family. -/
theorem extremal_cat : ∀ (n : ℕ) (F : Finset (List Bool)), EvenFam F n → F.card = 2 ^ n → Cat n F := by
  intro n
  induction n with
  | zero =>
    intro F hE hF
    have hsub : F ⊆ {[]} := fun w hw => by
      have := hE.len w hw
      simpa [List.length_eq_zero_iff] using this
    have : F = {[]} := Finset.eq_of_subset_of_card_le hsub (by simp [hF])
    subst this
    exact Cat.zero
  | succ n ih =>
    intro F hE hF
    classical
    have hne : F.Nonempty := by
      rw [← Finset.card_pos, hF]; positivity
    -- the first closing step `m + 1`
    let AllPref : ℕ → Prop := fun j => ∀ x : List Bool, x.length = j → x ∈ pre F j
    have hw2 : ¬ AllPref (n + 1 + 1) := by
      intro h
      obtain ⟨w, hw, hwt⟩ := mem_pre.mp (h (List.replicate (n + 2) true) (by simp))
      have h1 := hE.ht_take_add hw (n + 2)
      rw [hwt] at h1
      simp [ht, List.count_replicate] at h1
      omega
    have hex : ∃ j, ¬ AllPref (j + 1) := ⟨n + 1, hw2⟩
    set m := Nat.find hex with hmdef
    have hm1 : ¬ AllPref (m + 1) := Nat.find_spec hex
    have hmle : m ≤ n + 1 := Nat.find_min' hex hw2
    have hm : AllPref m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0]
        intro x hx
        obtain ⟨w, hw⟩ := hne
        rw [List.length_eq_zero_iff.mp hx]
        exact mem_pre.mpr ⟨w, hw, List.take_zero⟩
      · have := Nat.find_min hex (show m - 1 < m by omega)
        rw [show m - 1 + 1 = m by omega] at this
        exact not_not.mp this
    have C : Ctx F (n + 1) m := ⟨hE, hF, hm, by omega⟩
    have hnot : ∃ z : List Bool, z.length = m + 1 ∧ z ∉ pre F (m + 1) := by
      by_contra hc
      push Not at hc
      exact hm1 hc
    -- `m ≥ 1`
    have hm0 : 1 ≤ m := by
      rcases C.all_siblings hnot (x := List.replicate m true) (by simp) with ⟨u, hu, -⟩ | ⟨u, hu, -⟩ <;>
      · have := congrArg List.length hu
        simp at this
        omega
    set i := m - 1 with hidef
    have hi1 : i + 1 = m := by omega
    -- every word of `F` has a flippable pair at positions `i, i + 1`
    have decomp : ∀ w ∈ F, ∃ a : Bool, w = w.take i ++ [a, !a] ++ w.drop (i + 2) ∧
        w.take i ++ [!a, a] ++ w.drop (i + 2) ∈ F := by
      intro w hw
      have hwl := hE.len w hw
      have hxl : (w.take m).length = m := hE.len_take hw (by omega)
      have hmlt : m < w.length := by omega
      have htake : w.take (m + 1) = w.take m ++ [w[m]] := List.take_succ_eq_append_getElem hmlt
      have hpre : w.take m ++ [w[m]] ∈ pre F (m + 1) := mem_pre.mpr ⟨w, hw, htake⟩
      have hsplit : w = w.take m ++ [w[m]] ++ w.drop (m + 1) := by
        rw [← htake, List.take_append_drop]
      have hti : (w.take m).take i = w.take i := by rw [List.take_take]; congr 1; omega
      rcases C.all_siblings hnot hxl with ⟨u, hu, hp⟩ | ⟨u, hu, hp⟩
      · -- `w.take m = u N` takes only E
        have hb : w[m] = false := by
          by_contra hb
          have : w[m] = true := by simpa using hb
          rw [this] at hpre
          exact hp.2.2.2.1 hpre
        have hui : u = w.take i := by
          rw [← hti, hu, List.take_left' (by have := congrArg List.length hu; simp at this; omega)]
        refine ⟨true, ?_, ?_⟩
        · conv_lhs => rw [hsplit]
          rw [hb, hu, ← hui, show i + 2 = m + 1 by omega]
          simp
        · have hw' : w.take m ++ [false] ++ w.drop (m + 1) ∈ F := by
            rw [hb] at hsplit; rw [← hsplit]; exact hw
          have := (C.pair_transfer hp (w.drop (m + 1))).mp hw'
          rw [← hui, show i + 2 = m + 1 by omega]
          simpa using this
      · -- `w.take m = u E` takes only N
        have hb : w[m] = true := by
          by_contra hb
          have : w[m] = false := by simpa using hb
          rw [this] at hpre
          exact hp.2.2.2.2.2.1 hpre
        have hui : u = w.take i := by
          rw [← hti, hu, List.take_left' (by have := congrArg List.length hu; simp at this; omega)]
        refine ⟨false, ?_, ?_⟩
        · conv_lhs => rw [hsplit]
          rw [hb, hu, ← hui, show i + 2 = m + 1 by omega]
          simp
        · have hw' : w.take m ++ [true] ++ w.drop (m + 1) ∈ F := by
            rw [hb] at hsplit; rw [← hsplit]; exact hw
          have := (C.pair_transfer hp (w.drop (m + 1))).mpr hw'
          rw [← hui, show i + 2 = m + 1 by omega]
          simpa using this
    -- contract
    set G := F.image (fun w => w.take i ++ w.drop (i + 2)) with hGdef
    have hlenw : ∀ w ∈ F, (w.take i).length = i := fun w hw => hE.len_take hw (by omega)
    have hFG : F = InsFam i G := by
      ext w
      simp only [InsFam, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, hGdef,
        Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨a, ha, -⟩ := decomp w hw
        refine ⟨w.take i ++ w.drop (i + 2), ⟨w, hw, rfl⟩, ?_⟩
        have e : insPair i a (w.take i ++ w.drop (i + 2)) = w := by
          unfold insPair
          rw [List.take_left' (hlenw w hw), List.drop_left' (hlenw w hw)]
          exact ha.symm
        cases a
        · exact Or.inr e.symm
        · exact Or.inl e.symm
      · rintro ⟨g, ⟨w0, hw0, rfl⟩, hw⟩
        obtain ⟨a0, ha0, hs0⟩ := decomp w0 hw0
        have e : ∀ b, insPair i b (w0.take i ++ w0.drop (i + 2)) =
            w0.take i ++ [b, !b] ++ w0.drop (i + 2) := by
          intro b; unfold insPair
          rw [List.take_left' (hlenw w0 hw0), List.drop_left' (hlenw w0 hw0)]
        rcases hw with rfl | rfl
        · rw [e]
          cases a0
          · simpa using hs0
          · rw [← ha0]; exact hw0
        · rw [e]
          cases a0
          · rw [← ha0]; exact hw0
          · simpa using hs0
    have hGE : EvenFam G n := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hg
        have := hE.len w hw
        simp [List.length_take, List.length_drop, this]
        omega
      · intro g hg
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨a, ha, -⟩ := decomp w hw
        have h1 := hE.hn w hw
        rw [ha] at h1
        have h2 : ht [a, !a] = 1 := by cases a <;> rfl
        simp only [ht_append, h2] at h1
        simp only [ht_append]
        omega
      · intro g hg g' hg'
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hg'
        obtain ⟨a, ha, -⟩ := decomp w hw
        obtain ⟨a', ha', -⟩ := decomp w' hw'
        have e := hE.even w hw w' hw'
        rw [ha, ha', c_ins _ _ _ _ _ _ (by rw [hlenw w hw, hlenw w' hw'])] at e
        split_ifs at e <;> omega
    have hGlen : ∀ g ∈ G, i ≤ g.length := fun g hg => by rw [hGE.len g hg]; omega
    have hGc : G.card = 2 ^ n := by
      have := card_InsFam hGlen
      rw [← hFG, hF, pow_succ] at this
      omega
    rw [hFG]
    exact Cat.step i (by omega) (ih G hGE hGc)

/-- **Classification of the extremal even families.** -/
theorem extremal_iff_cat (n : ℕ) (F : Finset (List Bool)) :
    (EvenFam F n ∧ F.card = 2 ^ n) ↔ Cat n F :=
  ⟨fun h => extremal_cat n F h.1 h.2, cat_extremal⟩

end OC
