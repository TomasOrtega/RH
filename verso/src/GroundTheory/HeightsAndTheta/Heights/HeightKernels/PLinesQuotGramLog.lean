import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace KLinesQuotGramLog

/- English proof (translation)
Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inl i => exact hBl i`. Consider the case `inr j => exact hBr j`.
-/
theorem basis_eq_elim {K : Type*} [Field K] {n m k : ℕ}
    (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K)) (b : Fin m → Fin n → K) (τ : Fin k → Fin n)
    (hBl : ∀ i, B (Sum.inl i) = b i) (hBr : ∀ j, B (Sum.inr j) = Pi.single (τ j) 1) :
    (⇑B : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K) := by
  funext x
  cases x with
  | inl i => exact hBl i
  | inr j => exact hBr j

/- English proof (translation)
The claim follows from `PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)`.
-/
theorem diag_posDef {n : ℕ} (d : Fin n → ℝ) (hd : ∀ x, 0 < d x) :
    (Matrix.diagonal fun x => (d x : ℂ)).PosDef :=
  PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)

end KLinesQuotGramLog

open KLinesQuotGramLog in

/- English proof (translation)
Introduce `K _ n m k d σ B b c τ hd hBl hBr hτ hli`. Use `set H : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hH`. Establish `hHpd : H.PosDef` using `diag_posDef d hd`. Establish `hBe` using `basis_eq_elim B b τ hBl hBr`. Establish `hchg` using `h1 K n H σ (Fin m ⊕ Fin k) B (Sum.elim b c)`.

Take `⟨hdetP, hV⟩` from `h2 K n m k B b c hBl hli`. Use `set z : ℂ := σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hz`. Rewrite `hchg` using `[hdetP]`. Establish `hzc : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.conj_mul']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hchg` using `[hzc]`. Establish `hGu : (gramAt H σ (Sum.elim b c)).det.re = ‖z‖ ^ 2 * (gramAt H σ (⇑B)).det.re`. Rewrite using `[hchg, Complex.re_ofReal_mul]`.

Establish `hliB : LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K))`. Rewrite using `[← hBe]`. Conclude with `B.linearIndependent`. Establish `hFis` using `h3 K n m k d σ b τ hd hτ hliB`. Rewrite `hFis` using `[← hBe]`.

Establish `hlib : LinearIndependent K b` using `hli.comp Sum.inl Sum.inl_injective`. Establish `hGb : 0 < (gramAt H σ b).det.re` using `MCDet.re_det_pos (h4 K n H σ (Fin m) b hHpd hlib)`. Establish `hGB : 0 < (gramAt H σ (⇑B)).det.re` using `MCDet.re_det_pos (h4 K n H σ (Fin m ⊕ Fin k) (⇑B) hHpd B.linearIndependent)`. Establish `hz0 : 0 < ‖z‖` using `norm_pos_iff.mpr ((map_ne_zero σ).mpr hV)`. Establish `hprod : 0 < ∏ j, d (τ j)` using `Finset.prod_pos fun j _ => hd (τ j)`.

Rewrite using `[hGu, Real.log_mul (pow_pos hz0 2).ne' hGB.ne', Real.log_pow]`. Establish `hlog` using `Real.log_le_log hGB hFis`. Rewrite `hlog` using `[Real.log_mul hGb.ne' hprod.ne', Real.log_prod fun j _ => (hd (τ j)).ne']`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem LinesQuotGramLog.proof (h1 : LinesGramDetChange.Statement) (h2 : LinesCoordDet.Statement)
    (h3 : LinesGramFischerBound.Statement) (h4 : LinesGramPosDef.Statement) :
    LinesQuotGramLog.Statement := by
  intro K _ n m k d σ B b c τ hd hBl hBr hτ hli
  classical
  set H : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hH
  have hHpd : H.PosDef := diag_posDef d hd
  have hBe := basis_eq_elim B b τ hBl hBr

  have hchg := h1 K n H σ (Fin m ⊕ Fin k) B (Sum.elim b c)
  obtain ⟨hdetP, hV⟩ := h2 K n m k B b c hBl hli
  set z : ℂ := σ (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det with hz
  rw [hdetP] at hchg
  have hzc : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  rw [hzc] at hchg
  have hGu : (gramAt H σ (Sum.elim b c)).det.re = ‖z‖ ^ 2 * (gramAt H σ (⇑B)).det.re := by
    rw [hchg, Complex.re_ofReal_mul]

  have hliB : LinearIndependent K (Sum.elim b fun j => (Pi.single (τ j) 1 : Fin n → K)) := by
    rw [← hBe]; exact B.linearIndependent
  have hFis := h3 K n m k d σ b τ hd hτ hliB
  rw [← hBe] at hFis

  have hlib : LinearIndependent K b := hli.comp Sum.inl Sum.inl_injective
  have hGb : 0 < (gramAt H σ b).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m) b hHpd hlib)
  have hGB : 0 < (gramAt H σ (⇑B)).det.re :=
    MCDet.re_det_pos (h4 K n H σ (Fin m ⊕ Fin k) (⇑B) hHpd B.linearIndependent)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hV)
  have hprod : 0 < ∏ j, d (τ j) := Finset.prod_pos fun j _ => hd (τ j)

  rw [hGu, Real.log_mul (pow_pos hz0 2).ne' hGB.ne', Real.log_pow]
  have hlog := Real.log_le_log hGB hFis
  rw [Real.log_mul hGb.ne' hprod.ne', Real.log_prod fun j _ => (hd (τ j)).ne'] at hlog
  push_cast
  linarith

end GroundTheory.Heights₂.Heights
