import Mathlib

/- English proof (translation)
Introduce `H F G _ _ _ _ _ _ ι f U φ hι hU hφ`. Set `S : Subgroup H` to `{ carrier := {h : H | (fun x => φ (x * f (ι h))) = φ} one_mem' := by`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Use the proof step `mul_mem' := by`.

Introduce `a b ha hb`. Use function extensionality and compare the values at `x`. Establish `h1 : φ (x * f (ι a) * f (ι b)) = φ (x * f (ι a))` using `congrFun hb (x * f (ι a))`. Establish `h2 : φ (x * f (ι a)) = φ x` using `congrFun ha x`. Rewrite using `[map_mul, map_mul, ← mul_assoc, h1, h2]`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Use function extensionality and compare the values at `x`. Establish `h1 : φ (x * f (ι a⁻¹) * f (ι a)) = φ (x * f (ι a⁻¹))` using `congrFun ha (x * f (ι a⁻¹))`. Rewrite using `[← h1]`.

Simplify using `}`. Establish `hle : U.comap ι ≤ S`. Introduce `h hh`. Use function extensionality and compare the values at `x`. Conclude with `hφ (ι h) hh x`.

Establish `hopen : IsOpen ((U.comap ι : Subgroup H) : Set H)` using `hU.preimage hι`. Conclude with `Subgroup.isOpen_mono hle hopen`.
-/
theorem UpperTheory.isOpen_right_invariance :
    ∀ {H F G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group F] [TopologicalSpace F] [Group G]
        (ι : H →* F) (f : F →* G) (U : Subgroup F) (φ : G → ℂ), Continuous ι → IsOpen (U : Set F) →
        (∀ u ∈ U, ∀ g, φ (g * f u) = φ g) → IsOpen {h : H | (fun x => φ (x * f (ι h))) = φ} := by
  intro H F G _ _ _ _ _ _ ι f U φ hι hU hφ
  let S : Subgroup H :=
    { carrier := {h : H | (fun x => φ (x * f (ι h))) = φ}
      one_mem' := by
        funext x
        simp
      mul_mem' := by
        intro a b ha hb
        funext x
        have h1 : φ (x * f (ι a) * f (ι b)) = φ (x * f (ι a)) := congrFun hb (x * f (ι a))
        have h2 : φ (x * f (ι a)) = φ x := congrFun ha x
        rw [map_mul, map_mul, ← mul_assoc, h1, h2]
      inv_mem' := by
        intro a ha
        funext x
        have h1 : φ (x * f (ι a⁻¹) * f (ι a)) = φ (x * f (ι a⁻¹)) := congrFun ha (x * f (ι a⁻¹))
        rw [← h1]
        simp }
  have hle : U.comap ι ≤ S := by
    intro h hh
    funext x
    exact hφ (ι h) hh x
  have hopen : IsOpen ((U.comap ι : Subgroup H) : Set H) := hU.preimage hι
  exact Subgroup.isOpen_mono hle hopen
