import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SumIdemMul

noncomputable section

open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.KAway

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraMap_AE_injective : Function.Injective (algebraMap (AF F) (AE F E)) := by
  exact FaithfulSMul.algebraMap_injective (AF F) (AE F E)

instance isIntegral_AE : Algebra.IsIntegral (AF F) (AE F E) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  infer_instance

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Equip the data with the indicated structure. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem span_top' (hcm : IsCMExt F E σ) {n : ℕ} (ε : ℤ) (hε : ε * ε = 1)
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) (hX : IsUnit X.det) :
    Ideal.span {a : AF F | ∃ g, IsEH σ ε g ∧ algebraMap (AF F) (AE F E) a =
      (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det * cA σ (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det} = ⊤ := by
  by_contra hI
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  haveI := hm
  have hker : RingHom.ker (algebraMap (AF F) (AE F E)) ≤ m := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := algebraMap_AE_injective (by rw [hx, map_zero])
    rw [hx0]
    exact m.zero_mem
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  haveI := hQ
  letI : Field (AE F E ⧸ Q) := Ideal.Quotient.field Q
  obtain ⟨g, hg, h1, h2⟩ := exists_point hcm ε hε X hX (Ideal.Quotient.mk Q)
  obtain ⟨a, ha⟩ := nrm_exists hcm (X.toBlocks₁₁ - incM F g * X.toBlocks₂₁).det
  have haI : a ∈ m := hIm (Ideal.subset_span ⟨g, hg, ha⟩)
  rw [← hQm] at haI
  have h0 : Ideal.Quotient.mk Q (algebraMap (AF F) (AE F E) a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 haI
  rw [ha, map_mul] at h0
  exact mul_ne_zero h1 h2 h0

end PositivityTheory.SiegelWeilFormula.KAway

end
