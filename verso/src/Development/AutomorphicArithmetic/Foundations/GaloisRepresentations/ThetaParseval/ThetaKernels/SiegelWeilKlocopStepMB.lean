import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepMA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRDIota
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNB

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
/- English proof (translation)
Introduce `y a ha hy`. Establish `haH : IsUnit aᴴ.det` using `by rw [Matrix.det_conjTranspose]; exact ha.star`. Establish `hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ`. Establish `h1 : mR y * mR y⁻¹ = 1` using `by show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1`. Rewrite using `[mul_inv_cancel]`.

Both sides reduce to the same expression. Establish `h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1`. Rewrite using `[hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `[Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨hM, hA1, -, hO1, hF1, -⟩` from `R.frame_diag w y a (aᴴ)⁻¹ hy`. Take `⟨hM', -, hD', hO', -, hF'⟩` from `R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi`. Use `set M := inFrame d.b (R.ι w y) with hMdef`. Use `set M' := inFrame d.b (R.ι w y⁻¹) with hM'def`. Establish `hMM : M * M' = 1`.

Rewrite using `[hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]`. Establish `hMM' : M' * M = 1`. Rewrite using `[hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]`. Establish `bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)}, P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ → P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1`. Introduce `P Q hP hQ hPQ`.

Rewrite `hPQ` using `[hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ`. Take `⟨h1, -, -, h4⟩` from `Matrix.fromBlocks_inj.mp hPQ`. Conclude with `⟨h1, h4⟩`. Take `⟨t1, u1⟩` from `bl hM hM' hMM`.

Take `⟨t2, u2⟩` from `bl hM' hM hMM'`. Set `t : GL (Fin d.n) (AE F E)` to `⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩`. Set `u : GL (Fin d.n) (AE F E)` to `⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩`. Establish `hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1` using `hM`. Use `set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) * (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc`.

Use `⟨t, hA1, fun w' h => (hO1 w' h).1, hF1, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩` and prove the remaining obligations. Take `⟨φ, rfl⟩` from `hf`. Take `⟨ψ, hψ⟩` from `GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ`. Conclude with `⟨ψ, hψ⟩`. Use function extensionality and compare the values at `X`.

Rewrite using `[(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]`. Establish `hui : (u⁻¹).1 = M'.toBlocks₂₂` using `rfl`. Rewrite using `[hui]`. Use `set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ`. Establish `hZo : ∀ w', w' ≠ w → d.cw w' Z = 0`.

Introduce `w' h`. Rewrite using `[hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by`. Rewrite using `[← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]`. Conclude with `Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,`. Use the proof step `Matrix.mul_one, sub_self]`.

Establish `hZf : finOne F • Z = 0`. Rewrite using `[hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, sub_self]`. Establish `hX : X * (M'.toBlocks₂₂)ᵀ = X + Z` using `by rw [hZ]; abel`. Establish `hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]`.

Rewrite using `[_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]`.

Rewrite using `[hloc, hX, hΨ X Z hZo hZf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.stepM_gen (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    ∃ t : GL (Fin d.n) (AE F E), d.cw w t.1 = a ∧ (∀ w', w' ≠ w → d.cw w' t.1 = 1) ∧ finOne F • t.1 = finOne F • 1 ∧
      R.StepOK w (R.ι w y) (fun f u => ((d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ)) * f (Matrix.of u * a)) id := by
  intro y a ha hy
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = Matrix.fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1
      rw [mul_inv_cancel]; rfl
    have h2 : Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [Matrix.nonsing_inv_mul _ ha, Matrix.mul_nonsing_inv _ haH]
    calc mR y⁻¹ = (Matrix.fromBlocks a⁻¹ 0 0 aᴴ * mR y) * mR y⁻¹ := by rw [h2, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨hM, hA1, -, hO1, hF1, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y) with hMdef
  set M' := inFrame d.b (R.ι w y⁻¹) with hM'def
  have hMM : M * M' = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by
    rw [hMdef, hM'def, ← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl : ∀ {P Q : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)},
      P = Matrix.fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂ → Q = Matrix.fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ →
      P * Q = 1 → P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    intro P Q hP hQ hPQ
    rw [hP, hQ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    obtain ⟨h1, -, -, h4⟩ := Matrix.fromBlocks_inj.mp hPQ
    exact ⟨h1, h4⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM
  obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩
  let u : GL (Fin d.n) (AE F E) := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  have hMtu : inFrame d.b (R.ι w y) = Matrix.fromBlocks t.1 0 0 u.1 := hM
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  refine ⟨t, hA1, fun w' h => (hO1 w' h).1, hF1, fun f hf => ?_, fun Ψ hΨ => ⟨hΨ, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · obtain ⟨φ, rfl⟩ := hf
    obtain ⟨ψ, hψ⟩ := GlobalTheory.T.schwartz_linear_change d.m d.n c a ha φ
    exact ⟨ψ, hψ⟩
  · funext X
    rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hMtu X, hTΦ]
    have hui : (u⁻¹).1 = M'.toBlocks₂₂ := rfl
    rw [hui]
    set Z := X * (M'.toBlocks₂₂)ᵀ - X with hZ
    have hZo : ∀ w', w' ≠ w → d.cw w' Z = 0 := by
      intro w' h
      rw [hZ, show d.cw w' (X * (M'.toBlocks₂₂)ᵀ - X) = d.cw w' X * (d.cw w' M'.toBlocks₂₂)ᵀ - d.cw w' X from by
        rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]; exact Matrix.map_sub _ (map_sub _) _ _, (hO' w' h).2, Matrix.transpose_one,
        Matrix.mul_one, sub_self]
    have hZf : finOne F • Z = 0 := by
      rw [hZ, smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one, sub_self]
    have hX : X * (M'.toBlocks₂₂)ᵀ = X + Z := by rw [hZ]; abel
    have hloc : R.loc w (X * (M'.toBlocks₂₂)ᵀ) = Matrix.of (R.loc w X) * a := by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc]
      rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, hD', ← Matrix.mul_assoc, mapStar_mulR]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, id]
    rw [hloc, hX, hΨ X Z hZo hZf]
    ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
