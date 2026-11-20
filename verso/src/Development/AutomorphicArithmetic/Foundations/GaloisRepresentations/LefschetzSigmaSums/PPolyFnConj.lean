import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi

set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)

namespace UpperTheory.Gal.LocalSmoothExtension

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private theorem conv_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (K : Subgroup H) (f₁ f₂ : H → ℂ) :
    Formalism.UG.conv K (fun g => σ (f₁ g)) (fun g => σ (f₂ g)) = fun g => σ (Formalism.UG.conv K f₁ f₂ g) := by
  funext g
  unfold Formalism.UG.conv
  have h := σ.toAddEquiv.map_finsum
    (fun x : H ⧸ K => f₁ (Quotient.out x) * f₂ ((Quotient.out x)⁻¹ * g))
  simpa [map_mul] using h.symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem wordFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (w : List J) :
    wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g)) = fun g => σ (wordFn K ψ w f g) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Formalism.UG.conv K (fun g => σ (ψ j g)) (wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g))) = _
    rw [ih, conv_conj]
    rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem polyFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (s : List J →₀ ℂ) :
    polyFn K (fun j g => σ (ψ j g)) (wmap σ.toRingHom s) (fun g => σ (f g)) = fun g => σ (polyFn K ψ s f g) := by
  funext g
  unfold polyFn wmap
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  simp [Finsupp.sum, Finset.sum_apply, map_sum, wordFn_conj]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private theorem wmap_wmul {J : Type} (f : ℂ →+* ℂ) (a s : List J →₀ ℂ) :
    wmap f (wmul a s) = wmul (wmap f a) (wmap f s) := by
  unfold wmul wmap
  have hm : ∀ t : List J →₀ ℂ, Finsupp.mapRange f f.map_zero t =
      Finsupp.mapRange.addMonoidHom f.toAddMonoidHom t := fun t => rfl
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  rw [hm, map_finsuppSum]
  refine Finsupp.sum_congr (fun w _ => ?_)
  rw [map_finsuppSum, Finsupp.sum_mapRange_index (by intro w'; simp)]
  refine Finsupp.sum_congr (fun w' _ => ?_)
  rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  congr 1
  exact map_mul f (a w) (s w')

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem polyFnConj_of : PolyFnConj := fun σ _ _ _ K ψ f =>
  ⟨wordFn_conj σ K ψ f, polyFn_conj σ K ψ f, wmap_wmul σ.toRingHom⟩

end UpperTheory.Gal.LocalSmoothExtension

end
