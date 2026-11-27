import OC.Lemma2
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Shankar's bound `|F| ≤ 2^n`, and the structure of extremal families at every split
-/

namespace OC
open Finset

section BoundProofs
variable {F : Finset (List Bool)} {n : ℕ}

/-- Lemma 1 applied to the prefix classes. -/
lemma EvenFam.sumP (hE : EvenFam F n) {t : ℕ} (ht : t ≤ 2 * n) :
    ∑ k ∈ Ks F t, (P F t k).card ^ 2 ≤ 2 ^ t := by
  have L := lemma1 t (ι := Ks F t) (fun k => P F t k) ?_ ?_ ?_ ?_ ?_
  · rwa [Finset.sum_coe_sort (Ks F t) (fun k => (P F t k).card ^ 2)] at L
  · intro k x hx
    obtain ⟨w, hw, -, rfl⟩ := mem_P.mp hx
    exact hE.len_take hw ht
  · intro k k' hkk'
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨w, hw, hwk, rfl⟩ := mem_P.mp hx
    obtain ⟨w', hw', hwk', hww'⟩ := mem_P.mp hx'
    apply hkk'
    apply Subtype.ext
    rw [← hwk, ← hwk']
    exact key_of_take hww'.symm
  · intro k x hx y hy
    obtain ⟨w, hw, hwk, rfl⟩ := mem_P.mp hx
    obtain ⟨w', hw', hwk', rfl⟩ := mem_P.mp hy
    exact key_ht (hwk.trans hwk'.symm)
  · intro k x hx y hy
    obtain ⟨w, hw, hwk, rfl⟩ := mem_P.mp hx
    obtain ⟨w', hw', hwk', rfl⟩ := mem_P.mp hy
    rw [key_parity (hwk.trans hwk'.symm) hw', c_self, hE.len_take hw' ht]
  · intro k k' _ x hx x' hx' y hy y' hy'
    obtain ⟨w1, hw1, hk1, rfl⟩ := mem_P.mp hx
    obtain ⟨w2, hw2, hk2, rfl⟩ := mem_P.mp hx'
    obtain ⟨v1, hv1, hk3, rfl⟩ := mem_P.mp hy
    obtain ⟨v2, hv2, hk4, rfl⟩ := mem_P.mp hy'
    rw [key_parity (hk1.trans hk2.symm) hv1, c_comm, key_parity (hk3.trans hk4.symm) hw2, c_comm]

/-- prefix parities transfer to suffix parities -/
lemma EvenFam.cs_parity (hE : EvenFam F n) {t : ℕ} (ht : t ≤ 2 * n) {w v : List Bool}
    (hw : w ∈ F) (hv : v ∈ F) :
    c (w.drop t).reverse (v.drop t).reverse % 2 = c (w.take t) (v.take t) % 2 := by
  rw [c_reverse _ _ (by rw [hE.len_drop hw, hE.len_drop hv])]
  have := hE.split_parity hw hv ht
  omega

/-- Lemma 1 applied to the reversed suffix classes. -/
lemma EvenFam.sumQ (hE : EvenFam F n) {t : ℕ} (ht : t ≤ 2 * n) :
    ∑ k ∈ Ks F t, (Q F t k).card ^ 2 ≤ 2 ^ (2 * n - t) := by
  have L := lemma1 (2 * n - t) (ι := Ks F t) (fun k => (Q F t k).image List.reverse) ?_ ?_ ?_ ?_ ?_
  · rw [Finset.sum_coe_sort (Ks F t) (fun k => ((Q F t k).image List.reverse).card ^ 2)] at L
    simpa only [Finset.card_image_of_injective _ List.reverse_injective] using L
  · intro k z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w, hw, -, rfl⟩ := mem_Q.mp hy
    simp [hE.len_drop hw]
  · intro k k' hkk'
    rw [Finset.disjoint_left]
    intro z hz hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y', hy', hyy'⟩ := Finset.mem_image.mp hz'
    have hyy : y' = y := List.reverse_injective hyy'
    subst hyy
    obtain ⟨w, hw, hwk, rfl⟩ := mem_Q.mp hy
    obtain ⟨w', hw', hwk', hww'⟩ := mem_Q.mp hy'
    apply hkk'
    apply Subtype.ext
    rw [← hwk, ← hwk']
    exact hE.key_of_drop ht hw hw' hww'.symm
  · intro k z hz z' hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨w, hw, hwk, rfl⟩ := mem_Q.mp hy
    obtain ⟨w', hw', hwk', rfl⟩ := mem_Q.mp hy'
    have h1 := hE.ht_take_add hw t
    have h2 := hE.ht_take_add hw' t
    have h3 := key_ht (hwk.trans hwk'.symm)
    simp only [ht_reverse]
    omega
  · intro k z hz z' hz'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
    obtain ⟨w, hw, hwk, rfl⟩ := mem_Q.mp hy
    obtain ⟨w', hw', hwk', rfl⟩ := mem_Q.mp hy'
    rw [hE.cs_parity ht hw hw', key_parity (hwk.trans hwk'.symm) hw', c_self,
      hE.len_take hw' ht]
    omega
  · intro k k' _ z1 hz1 z2 hz2 z3 hz3 z4 hz4
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.mp hz2
    obtain ⟨y3, hy3, rfl⟩ := Finset.mem_image.mp hz3
    obtain ⟨y4, hy4, rfl⟩ := Finset.mem_image.mp hz4
    obtain ⟨w1, hw1, hk1, rfl⟩ := mem_Q.mp hy1
    obtain ⟨w2, hw2, hk2, rfl⟩ := mem_Q.mp hy2
    obtain ⟨v1, hv1, hk3, rfl⟩ := mem_Q.mp hy3
    obtain ⟨v2, hv2, hk4, rfl⟩ := mem_Q.mp hy4
    rw [hE.cs_parity ht hw1 hv1, hE.cs_parity ht hw2 hv2, key_parity (hk1.trans hk2.symm) hv1,
      c_comm, key_parity (hk3.trans hk4.symm) hw2, c_comm]

/-- Each class injects into `P × Q`. -/
lemma card_fib_le {t : ℕ} (k : ℕ × Finset (List Bool)) :
    (fib F t k).card ≤ (P F t k).card * (Q F t k).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun w => (w.take t, w.drop t))
  · intro w hw
    rw [Finset.mem_coe, mem_fib] at hw
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨mem_P.mpr ⟨w, hw.1, hw.2, rfl⟩, mem_Q.mpr ⟨w, hw.1, hw.2, rfl⟩⟩
  · intro w1 _ w2 _ h
    simp only [Prod.mk.injEq] at h
    rw [← List.take_append_drop t w1, ← List.take_append_drop t w2, h.1, h.2]

lemma card_eq_sum_fib (t : ℕ) : F.card = ∑ k ∈ Ks F t, (fib F t k).card := by
  rw [Finset.card_eq_sum_card_image (key F t) F]; rfl

lemma card_le_sumPQ (t : ℕ) : F.card ≤ ∑ k ∈ Ks F t, (P F t k).card * (Q F t k).card := by
  rw [card_eq_sum_fib t]
  exact Finset.sum_le_sum fun k _ => card_fib_le k

/-- **Shankar's Theorem 1.4**: an even family of paths `(0,0) → (n,n)` has at most `2^n` members. -/
theorem EvenFam.card_le (hE : EvenFam F n) : F.card ≤ 2 ^ n := by
  have hA := hE.sumP (t := n) (by omega)
  have hB := hE.sumQ (t := n) (by omega)
  have hC := card_le_sumPQ (F := F) n
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Ks F n) (fun k => (P F n k).card)
    (fun k => (Q F n k).card)
  have key : F.card ^ 2 ≤ (2 ^ n) ^ 2 :=
    calc F.card ^ 2 ≤ (∑ k ∈ Ks F n, (P F n k).card * (Q F n k).card) ^ 2 :=
          Nat.pow_le_pow_left hC 2
      _ ≤ (∑ k ∈ Ks F n, (P F n k).card ^ 2) * ∑ k ∈ Ks F n, (Q F n k).card ^ 2 := hCS
      _ ≤ 2 ^ n * 2 ^ (2 * n - n) := Nat.mul_le_mul hA hB
      _ = (2 ^ n) ^ 2 := by rw [show 2 * n - n = n by omega]; ring
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp key

/-- **Lemma 2, equality case**: the structure of an extremal family at a split `t`. -/
theorem EvenFam.structure (hE : EvenFam F n) (hF : F.card = 2 ^ n) {t : ℕ} (ht : t ≤ 2 * n) :
    (∀ k ∈ Ks F t, ∀ x ∈ P F t k, ∀ y ∈ Q F t k, x ++ y ∈ F ∧ key F t (x ++ y) = k) ∧
    (∀ k ∈ Ks F t, 2 ^ n * (P F t k).card = 2 ^ t * (Q F t k).card) ∧
    (∑ k ∈ Ks F t, (P F t k).card ^ 2 = 2 ^ t) := by
  set K := Ks F t
  set p : ℕ × Finset (List Bool) → ℕ := fun k => (P F t k).card
  set q : ℕ × Finset (List Bool) → ℕ := fun k => (Q F t k).card
  have hA : ∑ k ∈ K, p k ^ 2 ≤ 2 ^ t := hE.sumP ht
  have hB : ∑ k ∈ K, q k ^ 2 ≤ 2 ^ (2 * n - t) := hE.sumQ ht
  have hC : 2 ^ n ≤ ∑ k ∈ K, p k * q k := hF ▸ card_le_sumPQ t
  have hCS : (∑ k ∈ K, p k * q k) ^ 2 ≤ (∑ k ∈ K, p k ^ 2) * ∑ k ∈ K, q k ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq K p q
  have h2n : 2 ^ t * 2 ^ (2 * n - t) = 2 ^ n * 2 ^ n := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  set A := ∑ k ∈ K, p k ^ 2
  set B := ∑ k ∈ K, q k ^ 2
  set S := ∑ k ∈ K, p k * q k
  have hAB : A * B = 2 ^ n * 2 ^ n := by
    apply le_antisymm
    · calc A * B ≤ 2 ^ t * 2 ^ (2 * n - t) := Nat.mul_le_mul hA hB
        _ = _ := h2n
    · calc 2 ^ n * 2 ^ n ≤ S * S := Nat.mul_le_mul hC hC
        _ = S ^ 2 := (sq S).symm
        _ ≤ A * B := hCS
  have hS : S = 2 ^ n := by
    apply le_antisymm _ hC
    have : S ^ 2 ≤ (2 ^ n) ^ 2 := by rw [sq (2 ^ n), ← hAB]; exact hCS
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  have hpos : 0 < 2 ^ (2 * n - t) := by positivity
  have hA' : A = 2 ^ t := by
    apply le_antisymm hA
    have hB0 : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h | h
      · rw [h, mul_zero] at hAB; have : 0 < 2 ^ n * 2 ^ n := by positivity
        omega
      · exact h
    apply Nat.le_of_mul_le_mul_right (c := 2 ^ (2 * n - t)) _ hpos
    calc 2 ^ t * 2 ^ (2 * n - t) = A * B := by rw [hAB, h2n]
      _ ≤ A * 2 ^ (2 * n - t) := Nat.mul_le_mul_left A hB
  have hB' : B = 2 ^ (2 * n - t) := by
    have hpt : 0 < 2 ^ t := by positivity
    apply Nat.eq_of_mul_eq_mul_left hpt
    rw [← hA', hAB, ← h2n, hA']
  refine ⟨?_, ?_, hA'⟩
  · -- (E1): every class is all of `P k × Q k`
    have hfib : ∀ k ∈ K, (fib F t k).card = p k * q k := by
      have hsum : ∑ k ∈ K, (fib F t k).card = ∑ k ∈ K, p k * q k := by
        rw [← card_eq_sum_fib t, hF, ← hS]
      exact (Finset.sum_eq_sum_iff_of_le (fun k _ => card_fib_le k)).mp hsum
    intro k hk x hx y hy
    have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := fib F t k) (t := P F t k ×ˢ Q F t k)
      (fun w _ => (w.take t, w.drop t))
      (fun w hw => by
        rw [mem_fib] at hw
        exact Finset.mem_product.mpr ⟨mem_P.mpr ⟨w, hw.1, hw.2, rfl⟩, mem_Q.mpr ⟨w, hw.1, hw.2, rfl⟩⟩)
      (fun w1 w2 _ _ h => by
        simp only [Prod.mk.injEq] at h
        rw [← List.take_append_drop t w1, ← List.take_append_drop t w2, h.1, h.2])
      (by rw [Finset.card_product, hfib k hk])
    obtain ⟨w, hw, hxy⟩ := hsurj (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)
    simp only [Prod.mk.injEq] at hxy
    rw [hxy.1, hxy.2, List.take_append_drop]
    exact mem_fib.mp hw
  · -- (E2): `∑ (2^n p - 2^t q)^2 = 0`
    have hzero : ∑ k ∈ K, ((2 ^ n : ℤ) * p k - 2 ^ t * q k) ^ 2 = 0 := by
      have e : ∀ k ∈ K, ((2 ^ n : ℤ) * p k - 2 ^ t * q k) ^ 2 =
          (2 ^ n * 2 ^ n) * ((p k : ℤ) ^ 2) - 2 * 2 ^ n * 2 ^ t * ((p k : ℤ) * q k) +
            (2 ^ t * 2 ^ t) * ((q k : ℤ) ^ 2) := fun k _ => by ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      have cA : (∑ k ∈ K, (p k : ℤ) ^ 2) = (2 ^ t : ℤ) := by exact_mod_cast hA'
      have cB : (∑ k ∈ K, (q k : ℤ) ^ 2) = (2 ^ (2 * n - t) : ℤ) := by exact_mod_cast hB'
      have cS : (∑ k ∈ K, (p k : ℤ) * q k) = (2 ^ n : ℤ) := by exact_mod_cast hS
      have c2 : (2 ^ t * 2 ^ (2 * n - t) : ℤ) = 2 ^ n * 2 ^ n := by exact_mod_cast h2n
      rw [cA, cB, cS]
      linear_combination (2 ^ t : ℤ) * c2
    intro k hk
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
      ((2 ^ n : ℤ) * p k - 2 ^ t * q k))).mp hzero k hk
    have : (2 ^ n : ℤ) * p k = 2 ^ t * q k := by nlinarith [sq_nonneg ((2 ^ n : ℤ) * p k - 2 ^ t * q k)]
    exact_mod_cast this

end BoundProofs

end OC
