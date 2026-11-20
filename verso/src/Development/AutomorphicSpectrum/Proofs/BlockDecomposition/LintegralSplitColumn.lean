import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

/- English proof (translation)
Take `rfl : inst = Unique.fintype` from `Subsingleton.elim _ _`. Conclude with `(measurePreserving_funUnique (volume : Measure ℂ) U).symm`.
-/
theorem measurePreserving_funUnique_symm {U : Type} [inst : Fintype U] [Unique U] :
    MeasurePreserving (MeasurableEquiv.funUnique U ℂ).symm (volume : Measure ℂ)
      (Measure.pi fun _ : U => (volume : Measure ℂ)) := by
  obtain rfl : inst = Unique.fintype := Subsingleton.elim _ _
  exact (measurePreserving_funUnique (volume : Measure ℂ) U).symm

/- English proof (translation)
Use `haveI : Unique {j : α // ¬ j ≠ j₀} := { default := ⟨j₀, by simp⟩ uniq := fun x => Subtype.ext (by simpa using x.2) }`. Establish `h1` using `(measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ)) (fun j => j ≠ j₀)).symm`. Establish `h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ))` using `measurePreserving_funUnique_symm`. Establish `h3` using `(MeasurePreserving.id (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2`. Establish `h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _) ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))) ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ))` using `Measure.measurePreserving_swap`.

Establish `h5` using `h1.comp (h3.comp h4)`. Use `h5 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p j`. Distinguish the cases in `h : j = j₀`. Substitute `h` using the available equality.

Simplify using `[MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]`. Simplify using `[MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]`.
-/
theorem measurePreserving_joinEntry {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]

/- English proof (translation)
Establish `h1` using `(volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm`. Apply the tactic sequence `have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ)))) (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)`. Conclude with `h2.comp h1`.
-/
theorem measurePreserving_joinCol (d : ℕ) {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : (Fin d → ℂ) × (Fin d → {j : α // j ≠ j₀} → ℂ) => joinCol j₀ p.1 p.2)
      volume volume := by
  have h1 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ ({j : α // j ≠ j₀} → ℂ) (Fin d)).symm
  have h2 := measurePreserving_pi (fun _ : Fin d => (volume : Measure (ℂ × ({j : α // j ≠ j₀} → ℂ))))
    (fun _ : Fin d => (volume : Measure (α → ℂ))) (fun _ => measurePreserving_joinEntry j₀)
  exact h2.comp h1

/- English proof (translation)
Introduce `d α _ _ j₀ Φ hΦ`. Establish `hT` using `measurePreserving_joinCol d j₀`. Rewrite using `[← hT.lintegral_comp hΦ]`. Conclude with `lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable`.
-/
theorem lintegral_joinCol : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (Φ : (Fin d → α → ℂ) → ℝ≥0∞), Measurable Φ → ∫⁻ C : Fin d → α → ℂ, Φ C = ∫⁻ C' : Fin d → {j : α // j ≠ j₀} → ℂ, ∫⁻ c : Fin d → ℂ, Φ (joinCol j₀ c C') := by
  intro d α _ _ j₀ Φ hΦ
  have hT := measurePreserving_joinCol d j₀
  rw [← hT.lintegral_comp hΦ]
  exact lintegral_prod_symm _ (hΦ.comp hT.measurable).aemeasurable

end GlobalTheory.CompanionTheory.FSCrofton
