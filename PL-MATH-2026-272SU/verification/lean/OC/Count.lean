import OC.Main
import OC.Edges
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Counting: Shankar's Conjecture 4.1

A `Cat` family of order `n + 1` splits uniquely around the partner of its first
position: it is `Dec F₁ F₂ = {a u ā v : a ∈ {N,E}, u ∈ F₁, v ∈ F₂}` for `Cat`
families `F₁`, `F₂` of orders `k`, `n - k`.  This is the Catalan recursion, so there
are `catalan n` such families; by `extremal_iff_cat` they are exactly the even
families of `2^n` paths.
-/

namespace OC
open Finset

/-- the word `a u ā v` -/
def dw (a : Bool) (u v : List Bool) : List Bool := a :: (u ++ ((!a) :: v))

/-- the families `F₁`, `F₂` joined by an outer pair -/
def Dec (F₁ F₂ : Finset (List Bool)) : Finset (List Bool) :=
  (F₁ ×ˢ F₂).biUnion (fun p => {dw true p.1 p.2, dw false p.1 p.2})

lemma mem_Dec {F₁ F₂ : Finset (List Bool)} {w : List Bool} :
    w ∈ Dec F₁ F₂ ↔ ∃ a u v, u ∈ F₁ ∧ v ∈ F₂ ∧ w = dw a u v := by
  simp only [Dec, Finset.mem_biUnion, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, h | h⟩
    · exact ⟨true, u, v, hu, hv, h⟩
    · exact ⟨false, u, v, hu, hv, h⟩
  · rintro ⟨a, u, v, hu, hv, rfl⟩
    refine ⟨(u, v), ⟨hu, hv⟩, ?_⟩
    cases a <;> simp

lemma mem_InsFam {i : ℕ} {G : Finset (List Bool)} {w : List Bool} :
    w ∈ InsFam i G ↔ ∃ b g, g ∈ G ∧ w = insPair i b g := by
  simp only [InsFam, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨g, hg, h | h⟩
    · exact ⟨true, g, hg, h⟩
    · exact ⟨false, g, hg, h⟩
  · rintro ⟨b, g, hg, rfl⟩
    exact ⟨g, hg, by cases b <;> simp⟩

lemma dw_nil (a : Bool) (v : List Bool) : dw a [] v = insPair 0 a v := by
  simp [dw, insPair]

lemma dw_ins_left {i : ℕ} (a b : Bool) {u : List Bool} (v : List Bool) (hi : i ≤ u.length) :
    dw a (insPair i b u) v = insPair (i + 1) b (dw a u v) := by
  simp only [dw, insPair, List.take_succ_cons, List.drop_succ_cons]
  rw [List.take_append_of_le_length hi, List.drop_append_of_le_length hi]
  simp

lemma dw_ins_right {i : ℕ} (a b : Bool) (u : List Bool) {v : List Bool} :
    dw a u (insPair i b v) = insPair (u.length + 2 + i) b (dw a u v) := by
  have e1 : (a :: (u ++ ((!a) :: v))).take (u.length + 2 + i) = a :: (u ++ ((!a) :: v.take i)) := by
    rw [show u.length + 2 + i = (u.length + 1 + i) + 1 by omega, List.take_succ_cons,
      List.take_append, List.take_of_length_le (by omega),
      show u.length + 1 + i - u.length = i + 1 by omega, List.take_succ_cons]
  have e2 : (a :: (u ++ ((!a) :: v))).drop (u.length + 2 + i) = v.drop i := by
    rw [show u.length + 2 + i = (u.length + 1 + i) + 1 by omega, List.drop_succ_cons,
      List.drop_append, List.drop_of_length_le (by omega),
      show u.length + 1 + i - u.length = i + 1 by omega, List.drop_succ_cons, List.nil_append]
  simp only [insPair, dw] at e1 e2 ⊢
  rw [e1, e2]
  simp

lemma Dec_nil_left (F₂ : Finset (List Bool)) : Dec {[]} F₂ = InsFam 0 F₂ := by
  ext w; rw [mem_Dec, mem_InsFam]
  constructor
  · rintro ⟨a, u, v, hu, hv, rfl⟩
    rw [Finset.mem_singleton] at hu; subst hu
    exact ⟨a, v, hv, dw_nil a v⟩
  · rintro ⟨b, g, hg, rfl⟩
    exact ⟨b, [], g, Finset.mem_singleton_self _, hg, (dw_nil b g).symm⟩

lemma Dec_ins_left {i : ℕ} {G₁ : Finset (List Bool)} (F₂ : Finset (List Bool))
    (hG : ∀ u ∈ G₁, i ≤ u.length) : Dec (InsFam i G₁) F₂ = InsFam (i + 1) (Dec G₁ F₂) := by
  ext w; rw [mem_Dec, mem_InsFam]
  constructor
  · rintro ⟨a, u', v, hu', hv, rfl⟩
    obtain ⟨b, u, hu, rfl⟩ := mem_InsFam.mp hu'
    exact ⟨b, dw a u v, mem_Dec.mpr ⟨a, u, v, hu, hv, rfl⟩, dw_ins_left a b v (hG u hu)⟩
  · rintro ⟨b, x, hx, rfl⟩
    obtain ⟨a, u, v, hu, hv, rfl⟩ := mem_Dec.mp hx
    exact ⟨a, insPair i b u, v, mem_InsFam.mpr ⟨b, u, hu, rfl⟩, hv,
      (dw_ins_left a b v (hG u hu)).symm⟩

lemma Dec_ins_right {i L : ℕ} (G₁ : Finset (List Bool)) {G₂ : Finset (List Bool)}
    (hG₁ : ∀ u ∈ G₁, u.length = L) : Dec G₁ (InsFam i G₂) = InsFam (L + 2 + i) (Dec G₁ G₂) := by
  ext w; rw [mem_Dec, mem_InsFam]
  constructor
  · rintro ⟨a, u, v', hu, hv', rfl⟩
    obtain ⟨b, v, hv, rfl⟩ := mem_InsFam.mp hv'
    refine ⟨b, dw a u v, mem_Dec.mpr ⟨a, u, v, hu, hv, rfl⟩, ?_⟩
    rw [dw_ins_right, hG₁ u hu]
  · rintro ⟨b, x, hx, rfl⟩
    obtain ⟨a, u, v, hu, hv, rfl⟩ := mem_Dec.mp hx
    refine ⟨a, u, insPair i b v, hu, mem_InsFam.mpr ⟨b, v, hv, rfl⟩, ?_⟩
    rw [dw_ins_right, hG₁ u hu]

/-- joining two `Cat` families gives a `Cat` family -/
theorem cat_Dec : ∀ {k : ℕ} {F₁ : Finset (List Bool)}, Cat k F₁ →
    ∀ {j : ℕ} {F₂ : Finset (List Bool)}, Cat j F₂ → Cat (k + j + 1) (Dec F₁ F₂) := by
  intro k F₁ h₁
  induction h₁ with
  | zero =>
    intro j F₂ h₂
    rw [Dec_nil_left, show 0 + j + 1 = j + 1 by ring]
    exact Cat.step 0 (Nat.zero_le _) h₂
  | @step k G₁ i hi hG₁ ih =>
    intro j F₂ h₂
    have hlen : ∀ u ∈ G₁, i ≤ u.length := fun u hu => by
      rw [(cat_extremal hG₁).1.len u hu]; exact hi
    rw [Dec_ins_left F₂ hlen, show k + 1 + j + 1 = (k + j + 1) + 1 by ring]
    exact Cat.step (i + 1) (by omega) (ih h₂)

/-- every `Cat` family of positive order splits around the partner of position `0` -/
theorem Dec_of_cat : ∀ (n : ℕ) {F : Finset (List Bool)}, Cat (n + 1) F →
    ∃ k j F₁ F₂, k + j = n ∧ Cat k F₁ ∧ Cat j F₂ ∧ F = Dec F₁ F₂ := by
  intro n
  induction n with
  | zero =>
    intro F h
    cases h with
    | step i hi hG =>
      cases hG
      have : i = 0 := by omega
      subst this
      exact ⟨0, 0, {[]}, {[]}, rfl, Cat.zero, Cat.zero, (Dec_nil_left _).symm⟩
  | succ n ih =>
    intro F h
    cases h with
    | step i hi hG =>
      obtain ⟨k, j, G₁, G₂, hkj, h₁, h₂, rfl⟩ := ih hG
      have l₁ : ∀ u ∈ G₁, u.length = 2 * k := (cat_extremal h₁).1.len
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        refine ⟨0, n + 1, {[]}, Dec G₁ G₂, by ring, Cat.zero, ?_, (Dec_nil_left _).symm⟩
        have := cat_Dec h₁ h₂
        rwa [show k + j + 1 = n + 1 by omega] at this
      · by_cases hik : i ≤ 2 * k + 1
        · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          refine ⟨k + 1, j, InsFam i' G₁, G₂, by omega, Cat.step i' (by omega) h₁, h₂, ?_⟩
          rw [Dec_ins_left G₂ (fun u hu => by rw [l₁ u hu]; omega)]
        · obtain ⟨i', rfl⟩ : ∃ i', i = 2 * k + 2 + i' := ⟨i - (2 * k + 2), by omega⟩
          refine ⟨k, j + 1, G₁, InsFam i' G₂, by omega, h₁, Cat.step i' (by omega) h₂, ?_⟩
          rw [Dec_ins_right G₁ l₁]

lemma Dec_partner {k : ℕ} {F₁ F₂ : Finset (List Bool)} (h₁ : ∀ u ∈ F₁, u.length = 2 * k)
    {w : List Bool} (hw : w ∈ Dec F₁ F₂) : w[0]? ≠ w[2 * k + 1]? := by
  obtain ⟨a, u, v, hu, hv, rfl⟩ := mem_Dec.mp hw
  simp only [dw, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [h₁ u hu])]
  simp [h₁ u hu]

lemma Dec_not_partner {k : ℕ} {F₁ F₂ : Finset (List Bool)} (h₁ : ∀ u ∈ F₁, u.length = 2 * k)
    (hne₁ : F₁.Nonempty) (hne₂ : F₂.Nonempty) {p : ℕ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * k) :
    ∃ w ∈ Dec F₁ F₂, w[0]? = w[p]? := by
  obtain ⟨u, hu⟩ := hne₁
  obtain ⟨v, hv⟩ := hne₂
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  have hlt : p' < u.length := by rw [h₁ u hu]; omega
  refine ⟨dw (u[p']) u v, mem_Dec.mpr ⟨_, u, v, hu, hv, rfl⟩, ?_⟩
  simp only [dw, List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [List.getElem?_append_left hlt]
  simp [hlt]

lemma Cat.nonempty {n : ℕ} {G : Finset (List Bool)} (h : Cat n G) : G.Nonempty := by
  rw [← Finset.card_pos, (cat_extremal h).2]; positivity

/-- the splitting is unique -/
theorem Dec_inj {k k' j j' : ℕ} {F₁ F₂ F₁' F₂' : Finset (List Bool)} (h₁ : Cat k F₁)
    (h₂ : Cat j F₂) (h₁' : Cat k' F₁') (h₂' : Cat j' F₂') (h : Dec F₁ F₂ = Dec F₁' F₂') :
    k = k' ∧ F₁ = F₁' ∧ F₂ = F₂' := by
  have l₁ := (cat_extremal h₁).1.len
  have l₁' := (cat_extremal h₁').1.len
  have hk : k = k' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨w, hw, he⟩ := Dec_not_partner l₁' h₁'.nonempty h₂'.nonempty
        (p := 2 * k + 1) (by omega) (by omega)
      rw [← h] at hw
      exact Dec_partner l₁ hw he
    · obtain ⟨w, hw, he⟩ := Dec_not_partner l₁ h₁.nonempty h₂.nonempty
        (p := 2 * k' + 1) (by omega) (by omega)
      rw [h] at hw
      exact Dec_partner l₁' hw he
  subst hk
  have dec_eq : ∀ {a a' : Bool} {u u' v v' : List Bool}, u.length = u'.length →
      dw a u v = dw a' u' v' → a = a' ∧ u = u' ∧ v = v' := by
    intro a a' u u' v v' hl he
    simp only [dw, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain ⟨rfl, he2⟩ := List.append_inj he hl
    simp only [List.cons.injEq] at he2
    exact ⟨rfl, rfl, he2.2⟩
  refine ⟨rfl, ?_, ?_⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨v, hv⟩ := h₂.nonempty
      have hw : dw true u v ∈ Dec F₁' F₂' := h ▸ mem_Dec.mpr ⟨true, u, v, hu, hv, rfl⟩
      obtain ⟨a', u', v', hu', hv', he⟩ := mem_Dec.mp hw
      obtain ⟨-, rfl, -⟩ := dec_eq (by rw [l₁ u hu, l₁' u' hu']) he
      exact hu'
    · intro hu
      obtain ⟨v, hv⟩ := h₂'.nonempty
      have hw : dw true u v ∈ Dec F₁ F₂ := h ▸ mem_Dec.mpr ⟨true, u, v, hu, hv, rfl⟩
      obtain ⟨a', u', v', hu', hv', he⟩ := mem_Dec.mp hw
      obtain ⟨-, rfl, -⟩ := dec_eq (by rw [l₁' u hu, l₁ u' hu']) he
      exact hu'
  · ext v
    constructor
    · intro hv
      obtain ⟨u, hu⟩ := h₁.nonempty
      have hw : dw true u v ∈ Dec F₁' F₂' := h ▸ mem_Dec.mpr ⟨true, u, v, hu, hv, rfl⟩
      obtain ⟨a', u', v', hu', hv', he⟩ := mem_Dec.mp hw
      obtain ⟨-, -, rfl⟩ := dec_eq (by rw [l₁ u hu, l₁' u' hu']) he
      exact hv'
    · intro hv
      obtain ⟨u, hu⟩ := h₁'.nonempty
      have hw : dw true u v ∈ Dec F₁ F₂ := h ▸ mem_Dec.mpr ⟨true, u, v, hu, hv, rfl⟩
      obtain ⟨a', u', v', hu', hv', he⟩ := mem_Dec.mp hw
      obtain ⟨-, -, rfl⟩ := dec_eq (by rw [l₁' u hu, l₁ u' hu']) he
      exact hv'

/-- the `Cat` families of order `n` -/
noncomputable def CatSet (n : ℕ) : Finset (Finset (List Bool)) := by
  classical exact (allWords (2 * n)).powerset.filter (fun F => Cat n F)

lemma mem_CatSet {n : ℕ} {F : Finset (List Bool)} : F ∈ CatSet n ↔ Cat n F := by
  classical
  unfold CatSet
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨fun w hw => mem_allWords.mpr ((cat_extremal h).1.len w hw), h⟩⟩

lemma CatSet_zero : CatSet 0 = {{[]}} := by
  ext F
  rw [mem_CatSet, Finset.mem_singleton]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact Cat.zero

lemma card_CatSet_succ (n : ℕ) :
    (CatSet (n + 1)).card = ∑ k ∈ range (n + 1), (CatSet k).card * (CatSet (n - k)).card := by
  have heq : CatSet (n + 1) = (range (n + 1)).biUnion
      (fun k => (CatSet k ×ˢ CatSet (n - k)).image (fun p => Dec p.1 p.2)) := by
    ext F
    rw [mem_CatSet, Finset.mem_biUnion]
    constructor
    · intro h
      obtain ⟨k, j, F₁, F₂, hkj, h₁, h₂, rfl⟩ := Dec_of_cat n h
      refine ⟨k, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr ⟨(F₁, F₂), ?_, rfl⟩⟩
      rw [Finset.mem_product, mem_CatSet, mem_CatSet, show n - k = j by omega]
      exact ⟨h₁, h₂⟩
    · rintro ⟨k, hk, hF⟩
      obtain ⟨⟨F₁, F₂⟩, hp, rfl⟩ := Finset.mem_image.mp hF
      rw [Finset.mem_product, mem_CatSet, mem_CatSet] at hp
      have := cat_Dec hp.1 hp.2
      rwa [show k + (n - k) + 1 = n + 1 by have := Finset.mem_range.mp hk; omega] at this
  rw [heq, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_image_of_injOn, Finset.card_product]
    rintro ⟨F₁, F₂⟩ hp ⟨F₁', F₂'⟩ hp' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_CatSet] at hp hp'
    obtain ⟨-, rfl, rfl⟩ := Dec_inj hp.1 hp.2 hp'.1 hp'.2 he
    rfl
  · intro k _ k' _ hkk'
    rw [Function.onFun, Finset.disjoint_left]
    intro F hF hF'
    obtain ⟨⟨F₁, F₂⟩, hp, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨⟨F₁', F₂'⟩, hp', he⟩ := Finset.mem_image.mp hF'
    rw [Finset.mem_product, mem_CatSet, mem_CatSet] at hp hp'
    exact hkk' (Dec_inj hp'.1 hp'.2 hp.1 hp.2 he).1.symm

/-- there are `catalan n` families of order `n` -/
theorem card_CatSet (n : ℕ) : (CatSet n).card = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [CatSet_zero, catalan_zero]; rfl
    · rw [card_CatSet_succ, catalan_succ,
        Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i)) (n + 1)]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [ih k (by omega), ih (n - k) (by omega)]

/-- the paths from `(0,0)` to `(n,n)` -/
def Omega (n : ℕ) : Finset (List Bool) := (allWords (2 * n)).filter (fun w => ht w = n)

/-- **Conjecture 4.1 (Shankar, arXiv:2607.23117).**  There are exactly `C_n` families of
`2^n` North-East lattice paths from `(0,0)` to `(n,n)` in which every two distinct paths
share an even number of unit edges. -/
theorem conjecture_4_1 (n : ℕ) :
    ((Omega n).powerset.filter (fun F =>
      (∀ w ∈ F, ∀ v ∈ F, w ≠ v → Even (edges w ∩ edges v).card) ∧ F.card = 2 ^ n)).card =
      catalan n := by
  rw [← card_CatSet n]
  congr 1
  ext F
  rw [Finset.mem_filter, Finset.mem_powerset, mem_CatSet, ← extremal_iff_cat]
  have hO : ∀ w, w ∈ Omega n ↔ w.length = 2 * n ∧ ht w = n := fun w => by
    rw [Omega, Finset.mem_filter, mem_allWords]
  constructor
  · rintro ⟨hsub, hev, hcard⟩
    refine ⟨⟨fun w hw => ((hO w).mp (hsub hw)).1, fun w hw => ((hO w).mp (hsub hw)).2, ?_⟩, hcard⟩
    intro w hw v hv
    by_cases hwv : w = v
    · subst hwv
      rw [c_self, ((hO w).mp (hsub hw)).1]
      omega
    · rw [c_eq_card_inter w v (by rw [((hO w).mp (hsub hw)).1, ((hO v).mp (hsub hv)).1])]
      exact Nat.even_iff.mp (hev w hw v hv hwv)
  · rintro ⟨hE, hcard⟩
    refine ⟨fun w hw => (hO w).mpr ⟨hE.len w hw, hE.hn w hw⟩, fun w hw v hv _ => ?_, hcard⟩
    rw [← c_eq_card_inter w v (by rw [hE.len w hw, hE.len v hv])]
    exact Nat.even_iff.mpr (hE.even w hw v hv)

end OC
