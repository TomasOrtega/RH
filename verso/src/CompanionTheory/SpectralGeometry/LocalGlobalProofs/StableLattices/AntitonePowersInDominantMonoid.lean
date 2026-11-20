import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

/- English proof (translation)
Establish `hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0` using `⟨n, Or.inl rfl⟩`. Establish `hle : Nat.find hex ≤ n` using `Nat.find_min' hex (Or.inl rfl)`. Use `⟨⟨Nat.find hex, by omega⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Establish `hne : Nat.find hex ≠ n + 1` using `by omega`.

Simplify using `only [tExp, hne, if_false]`. Distinguish the cases in `hj : (j : ℕ) < Nat.find hex`. Establish `hnot` using `Nat.find_min hex hj`. Establish `hpos : 0 < b j`. Assume the negation of the conclusion as `hcon`.

Conclude with `hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)`. Rewrite using `[if_pos hj, if_pos hpos]`. Establish `hspec` using `Nat.find_spec hex`. Establish `hnpos : ¬ 0 < b j`. Break down `hspec with h | ⟨h, h'⟩` into its components or cases.

Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hmono : b j ≤ b ⟨Nat.find hex, h⟩` using `hb (by`. Rewrite using `[Fin.le_def]`. Conclude with `not_lt.mp hj)`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hj, if_neg hnpos]`.
-/
theorem exists_tExp_eq_indicator (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `b _ h0 hN`. Establish `hb : b = 0`. Use function extensionality and compare the values at `j`.

Establish `h1` using `h0 j`. Establish `h2` using `hN j`. Simplify using `only [Nat.cast_zero] at h2`. Simplify using `only [Pi.zero_apply]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hb, dPow_zero]`. Conclude with `Submonoid.one_mem _`. Consider the case `succ N ih`. Introduce `b hb h0 hN`. Take `⟨i, hi⟩` from `exists_tExp_eq_indicator b hb`.

Establish `hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i`. Rewrite using `[hi]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[hdecomp, dPow_add]`.

Use `Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)` and prove the remaining obligations. Introduce `x y hxy`. Establish `hm` using `hb hxy`. Establish `hx` using `h0 x`. Establish `hy` using `h0 y`.

Use `show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)`. Apply the tactic sequence `split_ifs <;> omega`. Introduce `j`. Establish `h1` using `h0 j`. Use `show 0 ≤ (b j - if 0 < b j then 1 else 0)`.

Apply the tactic sequence `split_ifs <;> omega`. Introduce `j`. Establish `h1` using `h0 j`. Establish `h2` using `hN j`. Move the coercions through the operations in `at h2`.

Use `show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem dPow_mem_closure_of_nonneg (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega

/- English proof (translation)
Proceed by induction on `C with`. Consider the case `zero`. Introduce `a ha h0`. Establish `hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ)`. Introduce `j`.

Establish `h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs` using `Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Use linear arithmetic over natural numbers and integers. Use `dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd` and prove the remaining obligations. Use `h0 j` as an intermediate fact. Simplify using `using this`.

Consider the case `succ C ih`. Introduce `a ha h0`. Establish `hlast : tExp n (Fin.last (n + 1)) = fun _ => -1`. Use function extensionality and compare the values at `j`. Simplify using `[tExp]`.

Establish `hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1))`. Rewrite using `[hlast]`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules. Rewrite using `[hdecomp, dPow_add]`.

Use `Submonoid.mul_mem _ (ih _ ?_ ?_) (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)` and prove the remaining obligations. Introduce `x y hxy`. Use `ha hxy` as an intermediate fact. Use `show a y + 1 ≤ a x + 1`. Use linear arithmetic over natural numbers and integers.

Introduce `j`. Use `h0 j` as an intermediate fact. Move the coercions through the operations in `at this`. Use `show -(C : ℤ) ≤ a j + 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega

/- English proof (translation)
Use `dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)` and prove the remaining obligations. Establish `h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs` using `Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)`. Use linear arithmetic over natural numbers and integers.
-/
theorem dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  refine dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)
  have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
    Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.CartGL
