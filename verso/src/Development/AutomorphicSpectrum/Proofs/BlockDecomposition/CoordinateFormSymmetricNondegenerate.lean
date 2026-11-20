import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem traceGram_isSymm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).IsSymm := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  ext k l
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have h := Algebra.trace_eq_of_algEquiv s (b l * σ (b k))
  have hs : s (b l * σ (b k)) = b k * σ (b l) := by
    show σ (b l * σ (b k)) = b k * σ (b l)
    rw [map_mul, hσ, mul_comm]
  rw [hs] at h
  exact h.symm ▸ rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem traceGram_det_ne_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    (Matrix.of fun k l : Fin d => Algebra.trace F E (b k * σ (b l))).det ≠ 0 := by
  have hσ : ∀ e, σ (σ e) = e := sig_invol hCM
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  set y : E := ∑ l, v l • b l with hy
  have hk : ∀ k, Algebra.trace F E (b k * σ y) = 0 := by
    intro k
    have := congrFun hmul k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, map_sum, Finset.mul_sum, map_sum, ← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hsm : σ (v l • b l) = v l • σ (b l) := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]
    rw [hsm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]
  have hz : ∀ x, Algebra.traceForm F E (σ y) x = 0 := by
    intro x
    rw [← b.sum_repr x]
    simp only [map_sum, map_smul, Algebra.traceForm_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm (σ y), hk, smul_zero]
  have hσy : σ y = 0 := (traceForm_nondegenerate F E).1 _ hz
  have hy0 : y = 0 := by rw [← hσ y, hσy, map_zero]
  have := (Fintype.linearIndependent_iff.1 b.linearIndependent) v hy0
  exact funext this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coordForm_isSymm_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  intro F E _ _ _ _ _ σ hCM d b n
  constructor
  · refine Matrix.IsSymm.fromBlocks (Matrix.isSymm_one) (by simp) ?_
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext _
    exact traceGram_isSymm hCM b
  · unfold coordForm
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => traceGram_det_ne_zero hCM b

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
