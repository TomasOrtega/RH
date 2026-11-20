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
Establish `hσ : ∀ e, σ (σ e) = e` using `sig_invol hCM`. Set `s : E ≃ₐ[F] E` to `AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)`. Use extensionality with `k l`. Simplify using `only [Matrix.transpose_apply, Matrix.of_apply]`. Establish `h` using `Algebra.trace_eq_of_algEquiv s (b l * σ (b k))`.

Establish `hs : s (b l * σ (b k)) = b k * σ (b l)` using `by show σ (b l * σ (b k)) = b k * σ (b l)`. Rewrite using `[map_mul, hσ, mul_comm]`. Rewrite `h` using `[hs]`. Conclude with `h.symm ▸ rfl`.
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
Establish `hσ : ∀ e, σ (σ e) = e` using `sig_invol hCM`. Use `haveI : FiniteDimensional F E := Module.Finite.of_basis b`. Introduce `h0`. Take `⟨v, hv, hmul⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h0`. Apply `hv` to reduce the goal to its premises.

Use `set y : E := ∑ l, v l • b l with hy`. Establish `hk : ∀ k, Algebra.trace F E (b k * σ y) = 0`. Introduce `k`. Use `congrFun hmul k` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this`.

Rewrite using `[hy, map_sum, Finset.mul_sum, map_sum, ← this]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `hsm : σ (v l • b l) = v l • σ (b l)`. Rewrite using `[Algebra.smul_def, map_mul, AlgHom.commutes, ← Algebra.smul_def]`. Rewrite using `[hsm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm]`.

Establish `hz : ∀ x, Algebra.traceForm F E (σ y) x = 0`. Introduce `x`. Rewrite using `[← b.sum_repr x]`. Simplify using `only [map_sum, map_smul, Algebra.traceForm_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm (σ y), hk, smul_zero]`. Establish `hσy : σ y = 0` using `(traceForm_nondegenerate F E).1 _ hz`. Establish `hy0 : y = 0` using `by rw [← hσ y, hσy, map_zero]`. Use `(Fintype.linearIndependent_iff.1 b.linearIndependent) v hy0` as an intermediate fact. Conclude with `funext this`.
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
Introduce `F E _ _ _ _ _ σ hCM d b n`. Prove the components needed by the constructor for the conclusion. Use `Matrix.IsSymm.fromBlocks (Matrix.isSymm_one) (by simp) ?_` and prove the remaining obligations. Unfold `Matrix.IsSymm`. Rewrite using `[Matrix.blockDiagonal_transpose]`.

Use `congr 1`. Use function extensionality and compare the values at `_`. Conclude with `traceGram_isSymm hCM b`. Unfold `coordForm`. Rewrite using `[Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_blockDiagonal]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun _ _ => traceGram_det_ne_zero hCM b`.
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
