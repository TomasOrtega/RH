import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.FieldVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem injective_of_isField {K L : Type} [CommRing K] [Ring L] [Nontrivial L] (hK : IsField K)
    (f : K →+* L) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun y hy => ?_
  by_contra hne
  obtain ⟨z, hz⟩ := hK.mul_inv_cancel hne
  have : f (y * z) = 1 := by rw [hz, map_one]
  rw [map_mul, hy, zero_mul] at this
  exact zero_ne_one this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities.
-/
theorem absBar_finEmb_eq (hK : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  have h1 := minpoly.algHom_eq (finEmb F v τ) (injective_of_isField hK (finEmb F v τ).toRingHom) y
  have h2 := minpoly.algHom_eq (finEmb F v τ') (injective_of_isField hK (finEmb F v τ').toRingHom) y
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  unfold spectralNorm
  rw [h1, h2]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations.
-/
theorem absFin_eq (hK : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absFin F v y = absBar F v (finEmb F v τ y) := by
  refine le_antisymm ((absFin_le_iff F v).2 fun τ' => (absBar_finEmb_eq v hK τ' τ y).le) (le_absFin F v τ y)

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_valuation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) →
    ∃ W : Valuation (Fv F v ⊗[F] E) ℝ≥0, (∀ a, W a = absFin F v a) ∧ ∀ a, W (sigR (Fv F v) σ a) = W a := by
  intro F E _ _ _ _ _ σ _ v hK
  let τ₀ : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  refine ⟨(valBar F v).comap (finEmb F v τ₀).toRingHom, fun a => ?_, fun a => ?_⟩
  · exact (absFin_eq v hK τ₀ a).symm
  · change absBar F v (finEmb F v τ₀ (sigR (Fv F v) σ a)) = absBar F v (finEmb F v τ₀ a)
    rw [finEmb_sigR]
    exact absBar_finEmb_eq v hK _ _ a

end GlobalTheory.CompanionTheory.KFin.FieldVal

end
