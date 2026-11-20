import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsNoetherian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompletionNormalDescent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAffineCompletionNormal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermCompletionEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

A detailed English derivation is pending.
-/
theorem holGerms_isUnit_of_value_ne_zero {σ : Type} [Fintype σ] {w : σ → ℂ} (φ : holGerms w)
    (hφ : holGermValue w φ ≠ 0) : IsUnit φ := by
  rcases φ with ⟨_, f, hf, rfl⟩
  have hfw : f w ≠ 0 := hφ
  let ψ : holGerms w := ⟨((fun z => (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ), _, hf.inv hfw, rfl⟩
  refine IsUnit.of_mul_eq_one ψ (Subtype.ext ?_)
  change ((fun z => f z * (f z)⁻¹ : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = ((fun _ => (1 : ℂ) : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ)
  exact Germ.coe_eq.2 ((hf.continuousAt.eventually_ne hfw).mono fun z hz => mul_inv_cancel₀ hz)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules.
-/
theorem holGermPointIdeal_le_jacobson {σ : Type} [Fintype σ] (w : σ → ℂ) :
    holGermPointIdeal w ≤ (⊥ : Ideal (holGerms w)).jacobson := by
  intro x hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  apply holGerms_isUnit_of_value_ne_zero
  have hx0 : holGermValue w x = 0 := RingHom.mem_ker.1 hx
  simp [map_add, map_mul, hx0]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem germQuotPointIdeal_le_jacobson {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    germQuotPointIdeal I w ≤ (⊥ : Ideal (holGerms w ⧸ I.map (polyGerm w))).jacobson := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [Ideal.mem_jacobson_bot]
  intro y
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have hu := Ideal.mem_jacobson_bot.1 (holGermPointIdeal_le_jacobson w hx') y'
  simpa [map_add, map_mul] using hu.map (Ideal.Quotient.mk (I.map (polyGerm w)))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem ZariskiAnalyticNormality.proof (hN : HolGermsNoetherian.Statement)
    (hD : CompletionNormalDescent.Statement) (hA : AffineCompletionNormal.Statement)
    (hE : GermCompletionEquiv.Statement) : ZariskiAnalyticNormality.Statement := by
  intro σ _ I w hI hIC hw
  have := hN σ w
  obtain ⟨e, -⟩ := hE σ I w
  obtain ⟨hdom, hic⟩ := hA σ I (polyPointIdeal I w) hI hIC (polyPointIdeal_isMaximal I w hw)
  have hdom' : IsDomain (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    e.toMulEquiv.isDomain
  have hic' : IsIntegrallyClosed
      (AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))) :=
    IsIntegrallyClosed.of_equiv e.symm
  obtain ⟨hB, hBic⟩ := hD _ (germQuotPointIdeal I w) inferInstance
    (germQuotPointIdeal_le_jacobson I w) hdom' hic'
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).1 hB, hBic⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
