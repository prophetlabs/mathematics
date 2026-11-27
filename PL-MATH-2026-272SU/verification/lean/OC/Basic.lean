import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lattice paths as words, and their common edges

A North-East lattice path is a word in `Bool`: `true` = N (a unit step up),
`false` = E (a unit step right).  `ht x` is the number of N's.

Two paths of the same length, started at the same point, share their `i`-th
unit edge exactly when their `i`-th letters agree and their prefixes before
position `i` have the same number of N's.  `ce x y d` counts these shared
edges when the N-count of `x` exceeds that of `y` by `d` at the start, and
`c x y = ce x y 0` is the number of common edges of the paths `x`, `y` from
the origin.
-/

namespace OC

/-- number of N's -/
def ht (x : List Bool) : ℕ := x.count true

/-- height increment of one letter -/
def bz (a : Bool) : ℤ := if a then 1 else 0

/-- common edges, with a starting height difference `d` -/
def ce : List Bool → List Bool → ℤ → ℕ
  | a :: x, b :: y, d => (if a = b ∧ d = 0 then 1 else 0) + ce x y (d + bz a - bz b)
  | _, _, _ => 0

/-- number of common edges of two paths from the origin -/
def c (x y : List Bool) : ℕ := ce x y 0

@[simp] lemma ht_nil : ht [] = 0 := rfl

@[simp] lemma ht_cons (a : Bool) (x : List Bool) :
    ht (a :: x) = ht x + (if a then 1 else 0) := by
  cases a <;> simp [ht]

@[simp] lemma ht_append (x y : List Bool) : ht (x ++ y) = ht x + ht y := by
  simp [ht, List.count_append]

lemma ht_le_length (x : List Bool) : ht x ≤ x.length := List.count_le_length

@[simp] lemma ce_nil_left (y : List Bool) (d : ℤ) : ce [] y d = 0 := by
  cases y <;> rfl

@[simp] lemma ce_nil_right (x : List Bool) (d : ℤ) : ce x [] d = 0 := by
  cases x <;> rfl

lemma ce_cons (a b : Bool) (x y : List Bool) (d : ℤ) :
    ce (a :: x) (b :: y) d = (if a = b ∧ d = 0 then 1 else 0) + ce x y (d + bz a - bz b) := rfl

/-- Splitting at any point (Fact 1 of the write-up, in offset form). -/
lemma ce_append (x x' y y' : List Bool) (d : ℤ) (h : x.length = x'.length) :
    ce (x ++ y) (x' ++ y') d = ce x x' d + ce y y' (d + ht x - ht x') := by
  induction x generalizing x' d with
  | nil =>
    cases x' with
    | nil => simp
    | cons b x' => simp at h
  | cons a x ih =>
    cases x' with
    | nil => simp at h
    | cons b x' =>
      simp only [List.cons_append, ce_cons]
      rw [ih x' _ (by simpa using h), add_assoc]
      have e : d + bz a - bz b + (ht x : ℤ) - (ht x' : ℤ) = d + (ht (a :: x) : ℤ) - (ht (b :: x') : ℤ) := by
        cases a <;> cases b <;> simp [bz] <;> push_cast <;> ring
      rw [e]

/-- Appending one letter to each path. -/
lemma c_snoc (x x' : List Bool) (a b : Bool) (h : x.length = x'.length) :
    c (x ++ [a]) (x' ++ [b]) = c x x' + (if a = b ∧ ht x = ht x' then 1 else 0) := by
  unfold c
  rw [ce_append x x' [a] [b] 0 h]
  congr 1
  simp only [ce_cons, ce_nil_left, add_zero]
  have : ((0 : ℤ) + ht x - ht x' = 0) ↔ ht x = ht x' := by omega
  simp only [this]

/-- Appending two letters to each path. -/
lemma c_snoc2 (x x' : List Bool) (a b a' b' : Bool) (h : x.length = x'.length) :
    c (x ++ [a, b]) (x' ++ [a', b']) =
      c x x' + (if a = a' ∧ ht x = ht x' then 1 else 0) +
        (if b = b' ∧ ht x + (if a then 1 else 0) = ht x' + (if a' then 1 else 0) then 1 else 0) := by
  have e1 : x ++ [a, b] = (x ++ [a]) ++ [b] := by simp
  have e2 : x' ++ [a', b'] = (x' ++ [a']) ++ [b'] := by simp
  rw [e1, e2, c_snoc _ _ _ _ (by simp [h]), c_snoc _ _ _ _ h]
  cases a <;> cases a' <;> simp

lemma ce_self (x : List Bool) : ce x x 0 = x.length := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [ce_cons, ih]; omega

@[simp] lemma c_self (x : List Bool) : c x x = x.length := ce_self x

lemma ce_symm (x y : List Bool) (d : ℤ) : ce x y d = ce y x (-d) := by
  induction x generalizing y d with
  | nil => simp
  | cons a x ih =>
    cases y with
    | nil => simp
    | cons b y =>
      simp only [ce_cons]
      rw [ih]
      congr 1
      · by_cases hab : a = b
        · subst hab; simp
        · have : ¬ b = a := fun h => hab h.symm
          simp [hab, this]
      · congr 1; ring

lemma c_comm (x y : List Bool) : c x y = c y x := by
  unfold c; rw [ce_symm]; simp

/-- Every nonempty word is a shorter word followed by a letter. -/
lemma exists_snoc {x : List Bool} {m : ℕ} (h : x.length = m + 1) :
    ∃ y a, x = y ++ [a] ∧ y.length = m := by
  have hx : x ≠ [] := by rintro rfl; simp at h
  exact ⟨x.dropLast, x.getLast hx, (List.dropLast_append_getLast hx).symm, by simp [h]⟩

/-- A word with `k` N's followed by `e` E's. -/
def mkp (k e : ℕ) : List Bool := List.replicate k true ++ List.replicate e false

@[simp] lemma mkp_length (k e : ℕ) : (mkp k e).length = k + e := by simp [mkp]

@[simp] lemma ht_mkp (k e : ℕ) : ht (mkp k e) = k := by
  simp [mkp, ht, List.count_replicate]

/-- The zigzag words `N (NE)^r` and `E (EN)^r`. -/
def zig : ℕ → List Bool
  | 0 => [true]
  | r + 1 => zig r ++ [true, false]

def zag : ℕ → List Bool
  | 0 => [false]
  | r + 1 => zag r ++ [false, true]

@[simp] lemma zig_length (r : ℕ) : (zig r).length = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [zig, ih]; ring

@[simp] lemma zag_length (r : ℕ) : (zag r).length = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [zag, ih]; ring

@[simp] lemma ht_zig (r : ℕ) : ht (zig r) = r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [zig, ih]

@[simp] lemma ht_zag (r : ℕ) : ht (zag r) = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [zag, ih]

lemma c_zig_zag (r : ℕ) : c (zig r) (zag r) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [zig, zag]
    rw [c_snoc2 _ _ _ _ _ _ (by simp), ih]
    simp

lemma c_zag_zig (r : ℕ) : c (zag r) (zig r) = 0 := by
  rw [c_comm]; exact c_zig_zag r

end OC
