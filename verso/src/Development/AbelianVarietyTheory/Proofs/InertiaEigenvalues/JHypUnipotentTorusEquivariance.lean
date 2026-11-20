import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnifConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JHypEquiv

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem secondCountable_K [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem t2Space_K (A : Et F E) : T2Space A.K := by
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).symm.t2Space

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem row_one (A : Et F E) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K) (j : Fin 2) :
    (nS z * mS s * g) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g 1 j := by
  show ((nS z).1 * (mS s).1 * g.1) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g.1 1 j
  simp [nS, mS, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem absK_unit (A : Et F E) (s : A.Kˣ) : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
  unfold Et.absK
  rw [dif_pos s.isUnit]
  congr 2
  exact Units.ext (IsUnit.unit_spec _)

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem integral_inv_mul [Unram F E] (A : Et F E) (μK : Measure A.K) [μK.IsAddHaarMeasure] (s : A.Kˣ)
    (H : A.K → ℂ) :
    ∫ t, H (((s⁻¹ : A.Kˣ) : A.K) * t) ∂μK = (distribHaarChar A.K s : ℝ) * ∫ u, H u ∂μK := by
  haveI := secondCountable_K A
  haveI := t2Space_K A
  have hmap : μK.map (fun x => (s⁻¹ : A.Kˣ) • x) = (distribHaarChar A.K s : ENNReal) • μK := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul _) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul, inv_inv]
  have e := integral_map_equiv (MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K) (μ := μK) H
  rw [show (⇑(MeasurableEquiv.smul (s⁻¹ : A.Kˣ) : A.K ≃ᵐ A.K)) = fun x => (s⁻¹ : A.Kˣ) • x from rfl, hmap,
    integral_smul_measure] at e
  rw [show (fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t)) = fun t => H ((s⁻¹ : A.Kˣ) • t) from rfl, ← e]
  simp [Complex.real_smul]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem etaK_mul [Unram F E] (A : Et F E) (s : A.Kˣ) (u : A.K) (hu : IsUnit u) :
    A.etaK ((s : A.K) * u) = A.etaK s * A.etaK u := by
  unfold Et.etaK
  rw [map_mul]
  exact (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ (s.isUnit.map (Algebra.norm F)).ne_zero (hu.map (Algebra.norm F)).ne_zero

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem jHyp_nm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ)
    (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K),
    A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  intro F E _ _ _ _ _ A μK hμ ψ φ' z s g
  haveI := hμ
  unfold Et.jHyp
  simp only [row_one]
  set H : A.K → ℂ := fun u => A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK ((s : A.K) * u) with hH
  have h1 : (fun t => A.tilde μK ψ φ' (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 0)) (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 1)) *
      A.etaK t) = fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t) := by
    funext t
    simp only [hH]
    rw [Units.mul_inv_cancel_left]
    congr 2 <;> ring
  rw [h1, integral_inv_mul A μK s H]
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ u ∂μK, IsUnit u := ae_iff.mpr hnull
  have h2 : ∫ u, H u ∂μK = ∫ u, A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK u * A.etaK s ∂μK := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hH]
    rw [etaK_mul A s u hu]
    ring
  rw [h2, integral_mul_const, absK_unit]
  ring

end GlobalTheory.JHypEquiv
