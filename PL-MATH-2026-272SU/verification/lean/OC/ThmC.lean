import OC.Basic

/-!
# Theorem C and Lemma D

Theorem C: if two distinct words `x, x'` of length `m` satisfy the parity
condition (∗∗) — `c p x ≡ c p x' (mod 2)` for every word `p` of length `m`
whose endpoint differs from both endpoints of `x` and `x'` — then they are
siblings, or they are the zigzag pair `N(NE)^r`, `E(EN)^r`.

Lemma D: if `ht y = ht y' + 2` and `c p y ≡ c p y'` for every `p` whose
endpoint is not the midpoint, then `(y, y') = (N(NE)^s N, E(EN)^s E)`.

Words of equal length have equal endpoints iff they have equal N-counts, so
endpoints are compared through `ht`.
-/

namespace OC

/-- the parity condition (∗∗) -/
def PC (m : ℕ) (x x' : List Bool) : Prop :=
  ∀ p : List Bool, p.length = m → ht p ≠ ht x → ht p ≠ ht x' → c p x % 2 = c p x' % 2

lemma PC.symm {m : ℕ} {x x' : List Bool} (h : PC m x x') : PC m x' x :=
  fun p hp h1 h2 => (h p hp h2 h1).symm

/-- conclusion of Theorem C -/
def SibOrZig (m : ℕ) (x x' : List Bool) : Prop :=
  (∃ u : List Bool, ∃ a : Bool, x = u ++ [a] ∧ x' = u ++ [!a]) ∨
  (∃ r, m = 2 * r + 1 ∧ ((x = zig r ∧ x' = zag r) ∨ (x = zag r ∧ x' = zig r)))

def ThmC (m : ℕ) : Prop :=
  ∀ x x' : List Bool, x.length = m → x'.length = m → x ≠ x' → PC m x x' → SibOrZig m x x'

def LemD (k : ℕ) : Prop :=
  ∀ y y' : List Bool, y.length = k → y'.length = k → ht y = ht y' + 2 →
    (∀ p : List Bool, p.length = k → ht p + 1 ≠ ht y → c p y % 2 = c p y' % 2) →
    ∃ s, k = 2 * s + 2 ∧ y = zig s ++ [true] ∧ y' = zag s ++ [false]

@[simp] lemma ht_single (a : Bool) : ht [a] = if a then 1 else 0 := by cases a <;> rfl

/-- Lemma D for `k = m + 1`, from Theorem C for `m`. -/
lemma lemD_succ (m : ℕ) (hC : ThmC m) : LemD (m + 1) := by
  intro y y' hy hy' hh hP
  obtain ⟨yh, a, rfl, hyh⟩ := exists_snoc hy
  obtain ⟨yh', b, rfl, hyh'⟩ := exists_snoc hy'
  have hPC : PC m yh yh' := by
    intro q hq h1 h2
    by_cases hq1 : ht q + 1 = ht (yh ++ [a])
    · have := hP (q ++ [true]) (by simp [hq]) (by simp at hq1 ⊢; omega)
      rw [c_snoc _ _ _ _ (by rw [hq, hyh]), c_snoc _ _ _ _ (by rw [hq, hyh'])] at this
      simpa [h1, h2] using this
    · have := hP (q ++ [false]) (by simp [hq]) (by simpa using hq1)
      rw [c_snoc _ _ _ _ (by rw [hq, hyh]), c_snoc _ _ _ _ (by rw [hq, hyh'])] at this
      simpa [h1, h2] using this
  have hne : yh ≠ yh' := by
    rintro rfl
    cases a <;> cases b <;> simp at hh <;> omega
  rcases hC yh yh' hyh hyh' hne hPC with ⟨u, α, rfl, rfl⟩ | ⟨r, hr, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · -- siblings: the N-counts force α = a = N, b = E
    have hα : α = true ∧ a = true ∧ b = false := by
      cases α <;> cases a <;> cases b <;> simp at hh ⊢ <;> omega
    obtain ⟨rfl, rfl, rfl⟩ := hα
    simp only [Bool.not_true, List.append_assoc, List.singleton_append] at hP ⊢
    have hu : u.length + 1 = m := by simpa using hyh
    rcases Nat.eq_zero_or_pos u.length with h0 | hpos
    · -- k = 2: (NN, EE)
      have : u = [] := List.length_eq_zero_iff.mp h0
      subst this
      exact ⟨0, by omega, rfl, rfl⟩
    · exfalso
      by_cases he : ht u < u.length
      · -- u has an E: test path q E N with q ending one step up-left of u
        set q := mkp (ht u + 1) (u.length - ht u - 1) with hqdef
        have hql : q.length = u.length := by simp [hqdef]; omega
        have := hP (q ++ [false, true]) (by simp [hql]; omega) (by simp [hqdef])
        rw [c_snoc2 _ _ _ _ _ _ hql, c_snoc2 _ _ _ _ _ _ hql] at this
        simp [hqdef] at this
        omega
      · -- u = N^j with j ≥ 1: test path q N E
        have hhu : ht u = u.length := le_antisymm (ht_le_length u) (not_lt.mp he)
        set q := mkp (ht u - 1) 1 with hqdef
        have hql : q.length = u.length := by simp [hqdef]; omega
        have e1 : ht u - 1 + 1 = ht u := by omega
        have e2 : ht u - 1 ≠ ht u := by omega
        have := hP (q ++ [true, false]) (by simp [hql]; omega) (by simp [hqdef]; omega)
        rw [c_snoc2 _ _ _ _ _ _ hql, c_snoc2 _ _ _ _ _ _ hql] at this
        simp [hqdef, e1, e2] at this
        omega
  · -- (zig r, zag r): N-counts force a = N, b = E
    have hab : a = true ∧ b = false := by
      cases a <;> cases b <;> simp at hh ⊢
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨r, by omega, rfl, rfl⟩
  · -- (zag r, zig r): impossible
    exfalso
    cases a <;> cases b <;> simp at hh <;> omega

/-- The special case of Theorem C: endpoints are diagonal neighbours, the heavier
word ends in E and the lighter in N.  Reduces to Lemma D. -/
lemma special {m : ℕ} (hD : LemD m) (xh xh' : List Bool) (hxh : xh.length = m)
    (hxh' : xh'.length = m) (hh : ht xh = ht xh' + 2)
    (hP : PC (m + 1) (xh ++ [false]) (xh' ++ [true])) :
    ∃ s, m = 2 * s + 2 ∧ xh = zig s ++ [true] ∧ xh' = zag s ++ [false] := by
  apply hD xh xh' hxh hxh' hh
  intro q hq h1
  by_cases hq2 : ht q = ht xh
  · have hq3 : ht q ≠ ht xh' := by omega
    have := hP (q ++ [true]) (by simp [hq]) (by simp <;> omega) (by simp <;> omega)
    rw [c_snoc _ _ _ _ (by rw [hq, hxh]), c_snoc _ _ _ _ (by rw [hq, hxh'])] at this
    simpa [hq3] using this
  · have := hP (q ++ [false]) (by simp [hq]) (by simp <;> omega) (by simp <;> omega)
    rw [c_snoc _ _ _ _ (by rw [hq, hxh]), c_snoc _ _ _ _ (by rw [hq, hxh'])] at this
    simpa [hq2] using this

/-- A test path witnessing that (∗∗) fails. -/
lemma not_PC_of {m : ℕ} {x x' : List Bool} (p : List Bool) (hp : p.length = m)
    (h1 : ht p ≠ ht x) (h2 : ht p ≠ ht x') (h3 : c p x % 2 ≠ c p x' % 2) : ¬ PC m x x' :=
  fun h => h3 (h p hp h1 h2)

/-- closes the side goals of a sibling test path -/
macro "sib_tac" : tactic => `(tactic| first
  | (simp <;> omega)
  | (rw [c_snoc2 _ _ _ _ _ _ rfl, c_snoc2 _ _ _ _ _ _ rfl]; simp <;> omega))

/-- closes the side goals of a zigzag test path -/
macro "zig_tac" : tactic => `(tactic| first
  | (simp <;> omega)
  | (rw [c_snoc _ _ _ _ (by simp), c_snoc _ _ _ _ (by simp)]; simp [c_zig_zag, c_zag_zig] <;> omega))

/-- Theorem C for `m + 1`, from Theorem C and Lemma D for `m`. -/
lemma thmC_succ (m : ℕ) (hC : ThmC m) (hD : LemD m) : ThmC (m + 1) := by
  intro x x' hx hx' hne hP
  obtain ⟨xh, a, rfl, hxh⟩ := exists_snoc hx
  obtain ⟨xh', b, rfl, hxh'⟩ := exists_snoc hx'
  -- Case 1: siblings
  by_cases h1 : xh = xh'
  · subst h1
    left
    refine ⟨xh, a, rfl, ?_⟩
    cases a <;> cases b <;> simp_all
  -- Case 2: the special configuration (either orientation)
  by_cases h2 : a = false ∧ b = true ∧ ht xh = ht xh' + 2
  · obtain ⟨rfl, rfl, hh⟩ := h2
    obtain ⟨s, hs, rfl, rfl⟩ := special hD xh xh' hxh hxh' hh hP
    right
    exact ⟨s + 1, by omega, Or.inl ⟨by simp [zig], by simp [zag]⟩⟩
  by_cases h3 : b = false ∧ a = true ∧ ht xh' = ht xh + 2
  · obtain ⟨rfl, rfl, hh⟩ := h3
    obtain ⟨s, hs, rfl, rfl⟩ := special hD xh' xh hxh' hxh hh hP.symm
    right
    exact ⟨s + 1, by omega, Or.inr ⟨by simp [zag], by simp [zig]⟩⟩
  -- Case 3: the truncations satisfy (∗∗), so they are siblings or zigzags,
  -- and every extension of those fails (∗∗).
  exfalso
  have hPC : PC m xh xh' := by
    intro q hq hq1 hq2
    have key : ∀ γ : Bool, ht (q ++ [γ]) ≠ ht (xh ++ [a]) → ht (q ++ [γ]) ≠ ht (xh' ++ [b]) →
        c q xh % 2 = c q xh' % 2 := by
      intro γ g1 g2
      have := hP (q ++ [γ]) (by simp [hq]) g1 g2
      rw [c_snoc _ _ _ _ (by rw [hq, hxh]), c_snoc _ _ _ _ (by rw [hq, hxh'])] at this
      simpa [hq1, hq2] using this
    by_cases e1 : ht q ≠ ht (xh ++ [a]) ∧ ht q ≠ ht (xh' ++ [b])
    · exact key false (by simpa using e1.1) (by simpa using e1.2)
    · apply key true
      · cases a <;> cases b <;> simp at e1 h2 h3 ⊢ <;> omega
      · cases a <;> cases b <;> simp at e1 h2 h3 ⊢ <;> omega
  rcases hC xh xh' hxh hxh' h1 hPC with ⟨u, α, rfl, rfl⟩ | ⟨r, hr, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simp only [List.append_assoc, List.singleton_append] at hP
    have hu : u.length + 1 = m := by simpa using hxh
    cases α <;> cases a <;> cases b <;>
    first
    | (refine not_PC_of (u ++ [false, false]) ?_ ?_ ?_ ?_ hP <;> sib_tac)
    | (refine not_PC_of (u ++ [true, true]) ?_ ?_ ?_ ?_ hP <;> sib_tac)
    | (refine not_PC_of (u ++ [true, false]) ?_ ?_ ?_ ?_ hP <;> sib_tac)
    | (refine not_PC_of (u ++ [false, true]) ?_ ?_ ?_ ?_ hP <;> sib_tac)
  all_goals
    cases a <;> cases b <;>
    first
    | (refine not_PC_of (zig r ++ [true]) ?_ ?_ ?_ ?_ hP <;> zig_tac)
    | (refine not_PC_of (zig r ++ [false]) ?_ ?_ ?_ ?_ hP <;> zig_tac)
    | (refine not_PC_of (zag r ++ [true]) ?_ ?_ ?_ ?_ hP <;> zig_tac)
    | (refine not_PC_of (zag r ++ [false]) ?_ ?_ ?_ ?_ hP <;> zig_tac)

/-- Theorem C and Lemma D, for every length. -/
theorem thmC_lemD : ∀ m, ThmC m ∧ LemD m
  | 0 => by
    refine ⟨fun x x' hx hx' hne _ => absurd ?_ hne, fun y y' hy _ hh _ => ?_⟩
    · rw [List.length_eq_zero_iff.mp hx, List.length_eq_zero_iff.mp hx']
    · have := ht_le_length y; omega
  | m + 1 =>
    have h := thmC_lemD m
    ⟨thmC_succ m h.1 h.2, lemD_succ m h.1⟩

theorem thmC (m : ℕ) : ThmC m := (thmC_lemD m).1

theorem lemD (k : ℕ) : LemD k := (thmC_lemD k).2

end OC
