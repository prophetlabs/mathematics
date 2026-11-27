import OC.Bound
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-!
# Prefixes, extensions, and the classes of an extremal family seen through prefixes
-/

namespace OC
open Finset

/-- the length-`t` prefixes of words of `F` -/
def pre (F : Finset (List Bool)) (t : ℕ) : Finset (List Bool) := F.image (List.take t)

/-- the suffixes `y` with `z ++ y ∈ F` -/
def ext (F : Finset (List Bool)) (z : List Bool) : Finset (List Bool) :=
  (F.filter (fun w => w.take z.length = z)).image (List.drop z.length)

/-- all words of length `m` -/
def allWords (m : ℕ) : Finset (List Bool) := (Finset.univ : Finset (Fin m → Bool)).image List.ofFn

lemma mem_allWords {m : ℕ} {x : List Bool} : x ∈ allWords m ↔ x.length = m := by
  constructor
  · intro h
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp h
    simp
  · intro h
    subst h
    exact Finset.mem_image.mpr ⟨fun i => x[i.val], Finset.mem_univ _, List.ofFn_getElem⟩

lemma card_allWords (m : ℕ) : (allWords m).card = 2 ^ m := by
  unfold allWords
  rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

section Prefixes
variable {F : Finset (List Bool)} {n : ℕ}

lemma mem_pre {t : ℕ} {z : List Bool} : z ∈ pre F t ↔ ∃ w ∈ F, w.take t = z := by
  simp [pre]

lemma mem_ext {z y : List Bool} : y ∈ ext F z ↔ z ++ y ∈ F := by
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
    rw [Finset.mem_filter] at hw
    have e : z ++ w.drop z.length = w := by
      conv_rhs => rw [← List.take_append_drop z.length w]
      rw [hw.2]
    rw [e]; exact hw.1
  · intro h
    exact Finset.mem_image.mpr ⟨z ++ y, Finset.mem_filter.mpr ⟨h, List.take_left' rfl⟩,
      List.drop_left' rfl⟩

lemma mem_pre_iff_ext {t : ℕ} {z : List Bool} (hz : z.length = t) :
    z ∈ pre F t ↔ (ext F z).Nonempty := by
  constructor
  · intro h
    obtain ⟨w, hw, rfl⟩ := mem_pre.mp h
    refine ⟨w.drop t, mem_ext.mpr ?_⟩
    rw [List.take_append_drop]; exact hw
  · rintro ⟨y, hy⟩
    exact mem_pre.mpr ⟨z ++ y, mem_ext.mp hy, by rw [← hz]; exact List.take_left' rfl⟩

lemma key_self_take {t : ℕ} (w : List Bool) : key F t (w.take t) = key F t w :=
  key_of_take (by rw [List.take_take, min_self])

lemma key_append {t : ℕ} {z : List Bool} (hz : z.length = t) (y : List Bool) :
    key F t (z ++ y) = key F t z :=
  key_of_take (by rw [List.take_left' hz, ← hz, List.take_length])

/-- (E1) in transfer form: two prefixes with the same signature have the same extensions. -/
lemma EvenFam.transfer (hE : EvenFam F n) (hF : F.card = 2 ^ n) {t : ℕ} (ht : t ≤ 2 * n)
    {z₁ z₂ y : List Bool} (h₁ : z₁.length = t) (h₂ : z₂ ∈ pre F t)
    (hk : key F t z₁ = key F t z₂) (hy : z₁ ++ y ∈ F) : z₂ ++ y ∈ F := by
  have E1 := (hE.structure hF ht).1
  have hk1 : key F t (z₁ ++ y) = key F t z₁ := key_append h₁ y
  have hKs : key F t z₁ ∈ Ks F t := Finset.mem_image.mpr ⟨z₁ ++ y, hy, hk1⟩
  obtain ⟨w₂, hw₂, rfl⟩ := mem_pre.mp h₂
  have hz₂ : w₂.take t ∈ P F t (key F t z₁) :=
    mem_P.mpr ⟨w₂, hw₂, by rw [hk, key_self_take], rfl⟩
  have hy' : y ∈ Q F t (key F t z₁) :=
    mem_Q.mpr ⟨z₁ ++ y, hy, hk1, List.drop_left' h₁⟩
  exact (E1 _ hKs _ hz₂ _ hy').1

lemma P_key_mem {t : ℕ} {z z' : List Bool} :
    z' ∈ P F t (key F t z) ↔ z' ∈ pre F t ∧ key F t z' = key F t z := by
  constructor
  · intro h
    obtain ⟨w, hw, hk, rfl⟩ := mem_P.mp h
    exact ⟨mem_pre.mpr ⟨w, hw, rfl⟩, by rw [key_self_take, hk]⟩
  · rintro ⟨h, hk⟩
    obtain ⟨w, hw, rfl⟩ := mem_pre.mp h
    exact mem_P.mpr ⟨w, hw, by rw [← key_self_take, hk], rfl⟩

lemma EvenFam.Q_key (hE : EvenFam F n) (hF : F.card = 2 ^ n) {t : ℕ} (ht : t ≤ 2 * n)
    {z : List Bool} (hz : z ∈ pre F t) (hzl : z.length = t) :
    Q F t (key F t z) = ext F z := by
  ext y
  rw [mem_Q, mem_ext]
  constructor
  · rintro ⟨w, hw, hk, rfl⟩
    apply hE.transfer hF ht (z₁ := w.take t) (hE.len_take hw ht) hz
    · rw [key_self_take, hk]
    · rw [List.take_append_drop]; exact hw
  · intro h
    exact ⟨z ++ y, h, key_append hzl y, List.drop_left' hzl⟩

/-- (E2) for the class of a prefix. -/
lemma EvenFam.E2_pre (hE : EvenFam F n) (hF : F.card = 2 ^ n) {t : ℕ} (ht : t ≤ 2 * n)
    {z : List Bool} (hz : z ∈ pre F t) (hzl : z.length = t) :
    2 ^ n * (P F t (key F t z)).card = 2 ^ t * (ext F z).card := by
  rw [← hE.Q_key hF ht hz hzl]
  apply (hE.structure hF ht).2.1
  obtain ⟨w, hw, rfl⟩ := mem_pre.mp hz
  exact Finset.mem_image.mpr ⟨w, hw, (key_self_take w).symm⟩

/-- the classes partition the prefixes -/
lemma pre_eq_biUnion (t : ℕ) : pre F t = (Ks F t).biUnion (P F t) := by
  ext z
  rw [mem_pre, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨key F t w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, mem_P.mpr ⟨w, hw, rfl, rfl⟩⟩
  · rintro ⟨k, -, hz⟩
    obtain ⟨w, hw, -, rfl⟩ := mem_P.mp hz
    exact ⟨w, hw, rfl⟩

lemma card_pre_eq_sum (t : ℕ) : (pre F t).card = ∑ k ∈ Ks F t, (P F t k).card := by
  rw [pre_eq_biUnion t, Finset.card_biUnion]
  intro k _ k' _ hkk'
  rw [Function.onFun, Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨w, hw, hwk, rfl⟩ := mem_P.mp hz
  obtain ⟨w', hw', hwk', hww'⟩ := mem_P.mp hz'
  exact hkk' (by rw [← hwk, ← hwk']; exact key_of_take hww'.symm)

/-- If every word of length `m` is a prefix, the classes at `m` have one prefix each. -/
lemma EvenFam.single (hE : EvenFam F n) (hF : F.card = 2 ^ n) {m : ℕ} (hm : m ≤ 2 * n)
    (hall : ∀ x : List Bool, x.length = m → x ∈ pre F m) {w₁ w₂ : List Bool}
    (h₁ : w₁ ∈ F) (h₂ : w₂ ∈ F) (hk : key F m w₁ = key F m w₂) : w₁.take m = w₂.take m := by
  have E3 := (hE.structure hF hm).2.2
  have hge : 2 ^ m ≤ ∑ k ∈ Ks F m, (P F m k).card := by
    rw [← card_pre_eq_sum, ← card_allWords m]
    exact Finset.card_le_card fun x hx => hall x (mem_allWords.mp hx)
  have hle : ∀ k ∈ Ks F m, (P F m k).card ≤ (P F m k).card ^ 2 := fun k _ => by
    rcases Nat.eq_zero_or_pos (P F m k).card with h | h
    · rw [h]; simp
    · nlinarith
  have heq := (Finset.sum_eq_sum_iff_of_le hle).mp (le_antisymm (Finset.sum_le_sum hle)
    (E3 ▸ hge))
  have hk₁ : key F m w₁ ∈ Ks F m := Finset.mem_image.mpr ⟨w₁, h₁, rfl⟩
  have h1 := heq _ hk₁
  have hcard : (P F m (key F m w₁)).card ≤ 1 := by
    rcases Nat.eq_zero_or_pos (P F m (key F m w₁)).card with h | h
    · omega
    · nlinarith
  exact Finset.card_le_one.mp hcard _ (mem_P.mpr ⟨w₁, h₁, rfl, rfl⟩) _
    (mem_P.mpr ⟨w₂, h₂, hk.symm, rfl⟩)

/-- extensions of `x` split by the next letter -/
lemma card_ext_split (hE : EvenFam F n) {x : List Bool} (hx : x.length < 2 * n) :
    (ext F x).card = (ext F (x ++ [false])).card + (ext F (x ++ [true])).card := by
  have hsplit : ext F x = (ext F (x ++ [false])).image (List.cons false) ∪
      (ext F (x ++ [true])).image (List.cons true) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_image, mem_ext]
    constructor
    · intro h
      have hl : y ≠ [] := by
        rintro rfl
        have := hE.len _ h
        simp at this
        omega
      obtain ⟨b, y', rfl⟩ := List.exists_cons_of_ne_nil hl
      cases b
      · exact Or.inl ⟨y', by simpa using h, rfl⟩
      · exact Or.inr ⟨y', by simpa using h, rfl⟩
    · rintro (⟨y', h, rfl⟩ | ⟨y', h, rfl⟩) <;> simpa using h
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ List.cons_injective,
    Finset.card_image_of_injective _ List.cons_injective]
  rw [Finset.disjoint_left]
  intro y h1 h2
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨_, -, h⟩ := Finset.mem_image.mp h2
  simp at h

end Prefixes

end OC
