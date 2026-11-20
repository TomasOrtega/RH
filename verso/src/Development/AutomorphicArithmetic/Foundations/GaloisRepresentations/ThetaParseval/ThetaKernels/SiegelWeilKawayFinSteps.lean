import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinSteps
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayFinBase

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SDf
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
/- English proof (translation)
Establish `hβ' : β = finOne F • β` using `by conv_lhs => rw [← smul_split β, hβ, zero_add]`. Establish `hβM : ∀ M : Mx F E d.n d.n, finOne F • M = 0 → β * M = 0` using `fun M hM => by`. Rewrite using `[hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]`. Use `⟨fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩` and prove the remaining obligations. Introduce `X Z hZ show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) = d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X`.

Rewrite using `[hG X Z hZ]`. Establish `e : β * d.gram (X + Z) (X + Z) = β * d.gram X X`. Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, hβM (d.gram X Z) (by r …`. Simplify using the standard rewrite rules. Rewrite using `[e]`.

Use function extensionality and compare the values at `X`. Rewrite using `[((hT.2.1 F E σ d) Φ hΦ).1 x β hx X, hTΦ]`. Simplify using `only [id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepN_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (β : Mx F E d.n d.n) (hx : inFrame d.b x = Matrix.fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) :
    _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβ' : β = finOne F • β := by
    conv_lhs => rw [← smul_split β, hβ, zero_add]
  have hβM : ∀ M : Mx F E d.n d.n, finOne F • M = 0 → β * M = 0 := fun M hM => by
    rw [hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]
  refine ⟨fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) =
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X
    rw [hG X Z hZ]
    have e : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_left_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_add_right_k, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        hβM (d.gram X Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_right_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z X) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]),
        hβM (d.gram Z Z) (by rw [← _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.gram_smul_left_k, hZ]; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram])]
      simp
    rw [e]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).1 x β hx X, hTΦ]
    simp only [id]
    ring
/- English proof (translation)
Use `set M : Mx F E d.n d.n := (a'⁻¹).1 with hM`. Establish `hMe : eInf F • M = eInf F • (1 : Mx F E d.n d.n)`. Establish `h1 : a'.1 * M = 1` using `by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨fun G X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) * (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ), fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩` and prove the remaining obligations.

Introduce `X Z hZ show _ * G ((X + Z) * Mᵀ) = _ * G (X * Mᵀ)`. Rewrite using `[Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]`. Use function extensionality and compare the values at `X`. Rewrite using `[((hT.2.1 F E σ d) Φ hΦ).2.1 x a a' hx X, hTΦ]`. Establish `hf' : f (X * Mᵀ) = f X`.

Establish `e : X * Mᵀ = X + X * (M - 1)ᵀ`. Rewrite using `[Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `hf X _ ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 ?_)` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul, hMe, sub_self, Matrix.mul_zero]`. Use `beta_reduce`. Rewrite using `[hf']`. Simplify using `only [id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stepM_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (x : d.G) (a a' : GL (Fin d.n) (AE F E))
    (hx : inFrame d.b x = Matrix.fromBlocks a.1 0 0 a'.1) (ha : eInf F • a'.1 = eInf F • (1 : Mx F E d.n d.n)) :
    ∃ B, _root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.StepF_k d x id B := by
  set M : Mx F E d.n d.n := (a'⁻¹).1 with hM
  have hMe : eInf F • M = eInf F • (1 : Mx F E d.n d.n) := by
    have h1 : a'.1 * M = 1 := by rw [hM, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc eInf F • M = (eInf F • (1 : Mx F E d.n d.n)) * M := by rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (eInf F • a'.1) * M := by rw [ha]
      _ = eInf F • (1 : Mx F E d.n d.n) := by rw [Matrix.smul_mul, h1]
  refine ⟨fun G X => (d.χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det a) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ),
    fun f hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · intro X Z hZ
    show _ * G ((X + Z) * Mᵀ) = _ * G (X * Mᵀ)
    rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · funext X
    rw [((hT.2.1 F E σ d) Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hf' : f (X * Mᵀ) = f X := by
      have e : X * Mᵀ = X + X * (M - 1)ᵀ := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one]
        abel
      rw [e]
      refine hf X _ ((_root_.PositivityTheory.SiegelWeilFormula.KAway.SDf.cw_zero_iff_k d _).2 ?_)
      rw [← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul, hMe,
        sub_self, Matrix.mul_zero]
    beta_reduce
    rw [hf']
    simp only [id]
    ring
end SDf
end PositivityTheory.SiegelWeilFormula.KAway
end
end
