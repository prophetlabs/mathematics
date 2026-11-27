import OC.ThmC
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum

/-!
# Lemma 1 (Shankar's Lemma 2.3, for words of any length)

Let `A i` (`i : ι`) be pairwise disjoint sets of words of length `m` such that
1. the words of each `A i` have the same N-count;
2. `c x y ≡ m (mod 2)` for `x, y ∈ A i`;
3. for `i ≠ j`, `c x y mod 2` is constant on `A i × A j`.
Then `∑ i, |A i|² ≤ 2^m`.
-/

namespace OC
open Finset

/-- the words of `A` ending in `a`, with that last letter removed -/
def Bpart (a : Bool) (A : Finset (List Bool)) : Finset (List Bool) :=
  (A.filter (fun x => x.getLast? = some a)).image List.dropLast

lemma mem_Bpart {a : Bool} {A : Finset (List Bool)} {u : List Bool} :
    u ∈ Bpart a A ↔ u ++ [a] ∈ A := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at hx
    rw [List.dropLast_append_getLast? a (Option.mem_def.mpr hx.2)]
    exact hx.1
  · intro h
    exact Finset.mem_image.mpr
      ⟨u ++ [a], Finset.mem_filter.mpr ⟨h, List.getLast?_concat⟩, List.dropLast_concat⟩

lemma card_split (A : Finset (List Bool)) (hA : ∀ x ∈ A, x ≠ []) :
    A.card = (Bpart false A).card + (Bpart true A).card := by
  have inj : ∀ a : Bool, Set.InjOn List.dropLast
      ((A.filter (fun x => x.getLast? = some a) : Finset (List Bool)) : Set (List Bool)) := by
    intro a x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
    rw [← List.dropLast_append_getLast? a (Option.mem_def.mpr hx.2),
      ← List.dropLast_append_getLast? a (Option.mem_def.mpr hy.2), hxy]
  unfold Bpart
  rw [card_image_of_injOn (inj false), card_image_of_injOn (inj true),
    ← Finset.card_filter_add_card_filter_not (s := A) (fun x => x.getLast? = some false)]
  congr 2
  apply Finset.filter_congr
  intro x hx
  obtain ⟨y, b, rfl⟩ : ∃ y b, x = y ++ [b] := by
    rcases List.eq_nil_or_concat x with h | ⟨y, b, h⟩
    · exact absurd h (hA x hx)
    · exact ⟨y, b, by rw [h, List.concat_eq_append]⟩
  cases b <;> simp

/-- The square-sum bound. -/
theorem lemma1 (m : ℕ) : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Finset (List Bool)),
    (∀ i, ∀ x ∈ A i, x.length = m) →
    (∀ i j, i ≠ j → Disjoint (A i) (A j)) →
    (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, ht x = ht y) →
    (∀ i, ∀ x ∈ A i, ∀ y ∈ A i, c x y % 2 = m % 2) →
    (∀ i j, i ≠ j → ∀ x ∈ A i, ∀ x' ∈ A i, ∀ y ∈ A j, ∀ y' ∈ A j, c x y % 2 = c x' y' % 2) →
    ∑ i, (A i).card ^ 2 ≤ 2 ^ m := by
  induction m with
  | zero =>
    intro ι _ _ A hlen hdisj _ _ _
    have hsub : ∀ i, A i ⊆ {[]} := fun i x hx => by
      simpa [List.length_eq_zero_iff] using hlen i x hx
    have hle : ∀ i, (A i).card ≤ 1 := fun i => (card_le_card (hsub i)).trans (by simp)
    calc ∑ i, (A i).card ^ 2 ≤ ∑ i, (A i).card := sum_le_sum fun i _ => by
            calc (A i).card ^ 2 = (A i).card * (A i).card := sq _
              _ ≤ 1 * (A i).card := Nat.mul_le_mul_right _ (hle i)
              _ = (A i).card := one_mul _
      _ = (univ.biUnion A).card := (card_biUnion (fun i _ j _ hij => hdisj i j hij)).symm
      _ ≤ 1 := (card_le_card (biUnion_subset.mpr fun i _ => hsub i)).trans (by simp)
  | succ m ih =>
    intro ι _ _ A hlen hdisj h1 h2 h3
    -- the two families of truncated sets, indexed by ι ⊕ ι
    let I : ι → Prop := fun i => (Bpart false (A i)).Nonempty ∧ (Bpart true (A i)).Nonempty
    let G : Bool → ι ⊕ ι → Finset (List Bool) := fun a =>
      Sum.elim (fun i => Bpart a (A i)) (fun i => if I i then Bpart (!a) (A i) else ∅)
    let idx : ι ⊕ ι → ι := Sum.elim id id
    let lt : Bool → ι ⊕ ι → Bool := fun a => Sum.elim (fun _ => a) (fun _ => !a)
    have memG : ∀ a k u, u ∈ G a k → u ++ [lt a k] ∈ A (idx k) := by
      intro a k u hu
      rcases k with i | i
      · exact mem_Bpart.mp hu
      · simp only [G, Sum.elim_inr] at hu
        split_ifs at hu with hI
        · exact mem_Bpart.mp hu
        · simp at hu
    have memI : ∀ a i u, u ∈ G a (Sum.inr i) → I i := by
      intro a i u hu
      simp only [G, Sum.elim_inr] at hu
      split_ifs at hu with hI
      · exact hI
      · simp at hu
    have lenG : ∀ a k, ∀ u ∈ G a k, u.length = m := by
      intro a k u hu
      have := hlen _ _ (memG a k u hu)
      simpa using this
    have h1G : ∀ a k, ∀ x ∈ G a k, ∀ y ∈ G a k, ht x = ht y := by
      intro a k x hx y hy
      have := h1 _ _ (memG a k x hx) _ (memG a k y hy)
      simpa using this
    have h2G : ∀ a k, ∀ x ∈ G a k, ∀ y ∈ G a k, c x y % 2 = m % 2 := by
      intro a k x hx y hy
      have e := h2 _ _ (memG a k x hx) _ (memG a k y hy)
      rw [c_snoc _ _ _ _ (by rw [lenG a k x hx, lenG a k y hy])] at e
      have hh := h1G a k x hx y hy
      simp [hh] at e
      omega
    -- the key disjointness step: `u E ∈ A i`, `u N ∈ A j` and `j` has both parts is impossible
    have mixed : ∀ (a : Bool) (i j : ι) (u : List Bool), u ++ [a] ∈ A i → u ++ [!a] ∈ A j →
        I j → False := by
      intro a i j u hu hu' hIj
      by_cases hij : i = j
      · subst hij
        have := h1 i _ hu _ hu'
        cases a <;> simp at this
      · obtain ⟨z, hz⟩ : (Bpart a (A j)).Nonempty := by
          cases a
          · exact hIj.1
          · exact hIj.2
        have hz' := mem_Bpart.mp hz
        have lu : u.length = m := by simpa using hlen _ _ hu
        have lz : z.length = m := by simpa using hlen _ _ hz'
        have e3 := h3 i j hij _ hu _ hu _ hz' _ hu'
        have e2 := h2 j _ hu' _ hz'
        have e1 := h1 j _ hu' _ hz'
        rw [c_snoc _ _ _ _ (by rw [lu, lz]), c_snoc _ _ _ _ rfl, c_self, lu] at e3
        rw [c_snoc _ _ _ _ (by rw [lu, lz])] at e2
        cases a <;> simp at e1 e2 e3 <;> split_ifs at e3 <;> omega
    have hdisjG : ∀ a k k', k ≠ k' → Disjoint (G a k) (G a k') := by
      intro a k k' hkk'
      rw [Finset.disjoint_left]
      intro u hu hu'
      have m1 := memG a k u hu
      have m2 := memG a k' u hu'
      rcases k with i | i <;> rcases k' with j | j <;>
        simp only [idx, lt, Sum.elim_inl, Sum.elim_inr, id_eq] at m1 m2
      · have hij : i ≠ j := fun h => hkk' (by rw [h])
        exact Finset.disjoint_left.mp (hdisj i j hij) m1 m2
      · exact mixed a i j u m1 m2 (memI a j u hu')
      · exact mixed a j i u m2 m1 (memI a i u hu)
      · have hij : i ≠ j := fun h => hkk' (by rw [h])
        exact Finset.disjoint_left.mp (hdisj i j hij) m1 m2
    have h3G : ∀ a k k', k ≠ k' → ∀ x ∈ G a k, ∀ x' ∈ G a k, ∀ y ∈ G a k', ∀ y' ∈ G a k',
        c x y % 2 = c x' y' % 2 := by
      intro a k k' hkk' x hx x' hx' y hy y' hy'
      have hxx' := h1G a k x hx x' hx'
      have hyy' := h1G a k' y hy y' hy'
      have lx := lenG a k x hx
      have lx' := lenG a k x' hx'
      have ly := lenG a k' y hy
      have ly' := lenG a k' y' hy'
      by_cases hidx : idx k = idx k'
      · have hl : lt a k ≠ lt a k' := by
          rcases k with i | i <;> rcases k' with j | j <;> simp [idx, lt] at hidx ⊢
          · exact hkk' (by rw [hidx])
          · exact hkk' (by rw [hidx])
        have e1 := h2 (idx k) _ (memG a k x hx) _ (hidx ▸ memG a k' y hy)
        have e2 := h2 (idx k) _ (memG a k x' hx') _ (hidx ▸ memG a k' y' hy')
        rw [c_snoc _ _ _ _ (by rw [lx, ly])] at e1
        rw [c_snoc _ _ _ _ (by rw [lx', ly'])] at e2
        simp [hl] at e1 e2
        omega
      · have e := h3 (idx k) (idx k') hidx _ (memG a k x hx) _ (memG a k x' hx')
          _ (memG a k' y hy) _ (memG a k' y' hy')
        rw [c_snoc _ _ _ _ (by rw [lx, ly]), c_snoc _ _ _ _ (by rw [lx', ly']), ← hxx', ← hyy'] at e
        split_ifs at e <;> omega
    have bound : ∀ a, ∑ k, (G a k).card ^ 2 ≤ 2 ^ m := fun a =>
      ih (G a) (lenG a) (hdisjG a) (h1G a) (h2G a) (h3G a)
    have hne : ∀ i, ∀ x ∈ A i, x ≠ [] := by
      intro i x hx h
      have := hlen i x hx
      rw [h] at this
      simp at this
    calc ∑ i, (A i).card ^ 2
        ≤ ∑ i, ((G false (Sum.inl i)).card ^ 2 + (G false (Sum.inr i)).card ^ 2 +
            ((G true (Sum.inl i)).card ^ 2 + (G true (Sum.inr i)).card ^ 2)) := by
          apply sum_le_sum
          intro i _
          simp only [G, Sum.elim_inl, Sum.elim_inr, Bool.not_false, Bool.not_true]
          rw [card_split (A i) (hne i)]
          split_ifs with hI
          · have := two_mul_le_add_sq (Bpart false (A i)).card (Bpart true (A i)).card
            nlinarith
          · simp only [I, not_and_or, Finset.not_nonempty_iff_eq_empty] at hI
            rcases hI with h | h <;> simp [h]
      _ = ∑ k, (G false k).card ^ 2 + ∑ k, (G true k).card ^ 2 := by
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
          simp only [Finset.sum_add_distrib]
      _ ≤ 2 ^ m + 2 ^ m := add_le_add (bound false) (bound true)
      _ = 2 ^ (m + 1) := by ring

end OC
