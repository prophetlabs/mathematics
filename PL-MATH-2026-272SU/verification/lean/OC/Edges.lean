import OC.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# `c` counts common unit edges

A unit edge of the grid is a pair `(p, a)`: its start point `p ∈ ℕ × ℕ` and its
direction `a` (`true` = N, `false` = E).  `edgesFrom p x` is the set of unit edges of
the path that starts at `p` and follows the word `x`.  We prove that for two paths
from the origin of equal length, `c x y` is the number of unit edges they share.
-/

namespace OC
open Finset

/-- one step from `p` in direction `a` -/
def step (p : ℕ × ℕ) (a : Bool) : ℕ × ℕ := if a then (p.1, p.2 + 1) else (p.1 + 1, p.2)

/-- the unit edges of the path from `p` following `x` -/
def edgesFrom : ℕ × ℕ → List Bool → Finset ((ℕ × ℕ) × Bool)
  | _, [] => ∅
  | p, a :: x => insert (p, a) (edgesFrom (step p a) x)

/-- the unit edges of the path from the origin following `x` -/
def edges (x : List Bool) : Finset ((ℕ × ℕ) × Bool) := edgesFrom (0, 0) x

lemma level_step (p : ℕ × ℕ) (a : Bool) : (step p a).1 + (step p a).2 = p.1 + p.2 + 1 := by
  cases a <;> simp [step] <;> ring

/-- every edge of a path from `p` starts at level `≥ p.1 + p.2` -/
lemma level_ge {p : ℕ × ℕ} {x : List Bool} {e : (ℕ × ℕ) × Bool} (he : e ∈ edgesFrom p x) :
    p.1 + p.2 ≤ e.1.1 + e.1.2 := by
  induction x generalizing p with
  | nil => simp [edgesFrom] at he
  | cons a x ih =>
    simp only [edgesFrom, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact le_refl _
    · have := ih he; rw [level_step] at this; omega

lemma step_snd (p : ℕ × ℕ) (a : Bool) : ((step p a).2 : ℤ) = p.2 + bz a := by
  cases a <;> simp [step, bz]

lemma card_inter_edgesFrom (x y : List Bool) (h : x.length = y.length) (p q : ℕ × ℕ)
    (hl : p.1 + p.2 = q.1 + q.2) :
    (edgesFrom p x ∩ edgesFrom q y).card = ce x y ((p.2 : ℤ) - q.2) := by
  induction x generalizing y p q with
  | nil => simp [edgesFrom]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have hl' : (step p a).1 + (step p a).2 = (step q b).1 + (step q b).2 := by
        rw [level_step, level_step, hl]
      have hrest := ih y (by simpa using h) (step p a) (step q b) hl'
      simp only [edgesFrom, ce_cons]
      -- the first edges lie on the lowest level, the others above it
      have key : insert (p, a) (edgesFrom (step p a) x) ∩ insert (q, b) (edgesFrom (step q b) y) =
          (if (p, a) = (q, b) then {(p, a)} else ∅) ∪
            (edgesFrom (step p a) x ∩ edgesFrom (step q b) y) := by
        ext e
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨h1 | h1, h2 | h2⟩
          · left; subst h1; rw [h2]; simp
          · exfalso; subst h1
            have := level_ge h2; rw [level_step] at this; dsimp only at this; omega
          · exfalso; subst h2
            have := level_ge h1; rw [level_step] at this; dsimp only at this; omega
          · right; exact ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · split_ifs at h1 with hpq
            · simp only [Finset.mem_singleton] at h1
              subst h1
              exact ⟨Or.inl rfl, Or.inl hpq⟩
            · simp at h1
          · exact ⟨Or.inr h1, Or.inr h2⟩
      rw [key, Finset.card_union_of_disjoint]
      · congr 1
        · have e : ((p, a) = (q, b)) ↔ (a = b ∧ (p.2 : ℤ) - q.2 = 0) := by
            constructor
            · intro h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
            · rintro ⟨rfl, h2⟩
              have h2' : p.2 = q.2 := by omega
              have h1' : p.1 = q.1 := by omega
              rw [Prod.ext h1' h2']
          by_cases hc : (p, a) = (q, b)
          · rw [if_pos hc, if_pos (e.mp hc)]; simp
          · rw [if_neg hc, if_neg (fun h => hc (e.mpr h))]; simp
        · rw [hrest]
          congr 1
          rw [step_snd, step_snd]
          ring
      · rw [Finset.disjoint_left]
        intro e h1 h2
        split_ifs at h1 with hpq
        · simp only [Finset.mem_singleton] at h1
          subst h1
          have := level_ge (Finset.mem_inter.mp h2).1
          rw [level_step] at this
          dsimp only at this
          omega
        · simp at h1

/-- `c x y` is the number of common unit edges of the two paths. -/
theorem c_eq_card_inter (x y : List Bool) (h : x.length = y.length) :
    c x y = (edges x ∩ edges y).card := by
  rw [edges, edges, card_inter_edgesFrom x y h (0, 0) (0, 0) rfl]
  rfl

end OC
