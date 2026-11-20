import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaOfSmF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI := isModuleTopology_AE F E`. Set `b` to `Module.finBasis F E`. Set `bb` to `Algebra.TensorProduct.basis (AF F) b`. Establish `hz : ∀ z : AEF F E, θ (infPartF F E z) = ∑ i, θ (fstA F (bb.repr z i) ⊗ₜ[F] (1 : E)) * τ (b i)`.

Introduce `z`. Use `conv_lhs => rw [← bb.sum_repr z]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Use `show θ (fstA F (bb.repr z i) ⊗ₜ[F] b i) = _`. Rewrite using `[← hθ.1 (b i), ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `hc : ∀ i, Continuous fun z : AEF F E => bb.repr z i` using `fun i => IsModuleTopology.continuous_of_linearMap (bb.coord i)`. Use `(continuous_finset_sum _ fun i _ => ?_).congr fun z => (hz z).symm` and prove the remaining obligations. Conclude with `(hθ.2.comp (continuous_fst.comp (hc i))).mul continuous_const`.
-/
theorem continuous_theta_infPartF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) :
    Continuous fun z : AEF F E => θ (infPartF F E z) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AEF F E, θ (infPartF F E z) = ∑ i, θ (fstA F (bb.repr z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← bb.sum_repr z]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    show θ (fstA F (bb.repr z i) ⊗ₜ[F] b i) = _
    rw [← hθ.1 (b i), ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc : ∀ i, Continuous fun z : AEF F E => bb.repr z i := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  refine (continuous_finset_sum _ fun i _ => ?_).congr fun z => (hz z).symm
  exact (hθ.2.comp (continuous_fst.comp (hc i))).mul continuous_const

end GlobalTheory.ThetaOfSmF

open GlobalTheory.ThetaOfSmF in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl`. Use `⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩` and prove the remaining obligations. Take `⟨lam, hlc, hlam⟩` from `GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)`. Set `P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ)` to `{ toFun := fun t => piWF θ (L t) map_zero' := by`. Use function extensionality and compare the values at `p`.

Simplify using `only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]`. Use the proof step `map_add' := fun s t => by`. Use function extensionality and compare the values at `p`. Simplify using `only [piWF, map_add, Matrix.add_apply, Pi.add_apply] }`. Establish `hP : Continuous P` using `continuous_pi fun p => (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))`.

Establish `hLP : ∀ t, L t = iotaVF ι (P t)`. Introduce `t`. Use extensionality with `i j`. Use `sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)` and prove the remaining obligations. Establish `h0 : finPartF F E (L t i j) = 0` using `congrFun (congrFun (hL0 t) i) j`.

Rewrite using `[map_sub, h0]`. Simplify using `only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]`. Rewrite using `[map_sub, map_sub]`. Simplify using `only [iotaVF, Matrix.of_apply, hι.comp]`. Use `show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0`.

Conclude with `sub_self _`. Set `φ : (Fin k → ℝ) →+ ℂ` to `{ toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t)) map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero] map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add, neg_add] }`. Establish `hφ : Continuous φ` using `(hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg`. Establish `e : (fun t => f.1 (w + L t)) = fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f)`. Use function extensionality and compare the values at `t`.

Establish `h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w` using `by show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _`. Rewrite using `[coe_rhoBF, ← hLP t]`. Establish `h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t)`. Rewrite using `[hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]`. Both sides reduce to the same expression.

Use `show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)`. Rewrite using `[ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`. Rewrite using `[e]`. Conclude with `(φ.toRealLinearMap hφ).contDiff.cexp.mul (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))`.
-/
theorem GlobalTheory.ThetaOfSmF.theta_of_smF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)

  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add, Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _

  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add, neg_add] }
  have hφ : Continuous φ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) := by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))

end
