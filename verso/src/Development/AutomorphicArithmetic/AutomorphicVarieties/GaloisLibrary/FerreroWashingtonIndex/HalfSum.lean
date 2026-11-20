import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Introduce `α k _ σ H H' g hσ hg hH hH' hHH' hH'H`. Use `Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Distinguish the cases in `h : x ∈ H'`. Simplify using `[h]`.

Simplify using `only [h, if_false]`. Conclude with `(hHH' x hx).resolve_left h`. Introduce `y hy`. Distinguish the cases in `h : y ∈ H`. Simplify using `[h]`.

Simplify using `only [h, if_false]`. Conclude with `(hH'H y hy).resolve_left h`. Introduce `x hx`. Distinguish the cases in `h : x ∈ H'`. Simplify using `[h, hx]`.

Simplify using `[h, hH x hx, hσ]`. Introduce `y hy`. Distinguish the cases in `h : y ∈ H`. Simplify using `[h, hy]`. Simplify using `[h, hH' y hy, hσ]`.

Introduce `x hx`. Distinguish the cases in `h : x ∈ H'`. Simplify using `[h]`. Simplify using `[h, hg]`.
-/
theorem UpperTheory.V.FW.halfSum :
    ∀ (α k : Type) [AddCommMonoid k] (σ : α → α) (H H' : Finset α) (g : α → k), (∀ x, σ (σ x) = x) → (∀ x, g (σ x) = g x) → (∀ x ∈ H, σ x ∉ H) → (∀ x ∈ H', σ x ∉ H') → (∀ x ∈ H, x ∈ H' ∨ σ x ∈ H') → (∀ x ∈ H', x ∈ H ∨ σ x ∈ H) → ∑ x ∈ H, g x = ∑ x ∈ H', g x := by
  classical
  intro α k _ σ H H' g hσ hg hH hH' hHH' hH'H
  refine Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp only [h, if_false]
      exact (hHH' x hx).resolve_left h
  · intro y hy
    by_cases h : y ∈ H
    · simp [h]
    · simp only [h, if_false]
      exact (hH'H y hy).resolve_left h
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h, hx]
    · simp [h, hH x hx, hσ]
  · intro y hy
    by_cases h : y ∈ H
    · simp [h, hy]
    · simp [h, hH' y hy, hσ]
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp [h, hg]
