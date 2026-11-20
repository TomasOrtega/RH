import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}
end
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI`. Take `⟨i1, i2, i3, i4, i5, -⟩` from `GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT`. Use `GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)` as an intermediate fact. Establish `: BorelSpace (WOF F E nS nT)` using `⟨rfl⟩`. Establish `hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1` using `fun M M' h => by`.

Rewrite using `[← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`. Set `A : GL (Fin nT) (AF F ⊗[F] E)` to `⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩`. Set `e : WOF F E nS nT ≃+ WOF F E nS nT` to `{ toFun := fun w => A.1 * w invFun := fun w => (A⁻¹).1 * w left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] map_add' := fun v w => Matrix.mul_add _ v w }`. Establish `c1 : Continuous e` using `continuous_const.matrix_mul continuous_id`. Establish `c2 : Continuous e.symm` using `continuous_const.matrix_mul continuous_id`.

Use `⟨hN.comp c1, ?_, fun y => ?_⟩` and prove the remaining obligations. Establish `: (ν.map e).IsAddHaarMeasure` using `e.isAddHaarMeasure_map ν c1 c2`. Take `⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩`. Establish `h1 : Integrable N (ν.map e)`. Rewrite using `[hc]`.

Conclude with `hI.smul_measure_nnreal`. Conclude with `(integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1`. Establish `h` using `integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)`. Establish `hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) = Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s)`. Use `Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)` and prove the remaining obligations.

Establish `hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hd : A.1.det = cAF σ s.1.det` using `by show ((s.1.map (cAF σ))ᵀ).det = _`. Rewrite using `[Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Use `show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)`. Rewrite using `[GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]`.

Rewrite `h` using `[hn]`. Use `set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm`. Establish `hm0 : 0 < m` using `NNReal.coe_pos.2 distribHaarChar_pos`. Establish `hf : mfac F E nS s ^ 2 = m ^ nS` using `by show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) = fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w)` using `funext fun w => by`. Rewrite using `[← phase_move JS JT hT.2 ξ₀ B.ψ s y w]`.

Rewrite `h` using `[h2]`. Rewrite using `[h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne', Complex.ofReal_one, one_mul]`.
-/
theorem change_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
