import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemLpTwoAndTendstoOfCauchyOfAeTendsto
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBoundStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroFormEqBigCellIntegralTopDensityCompactStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorAddSmulCompactCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TendstoTopVectorCompactApproximantsBigCellStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

/- English proof (translation)
Introduce `hP Cb`. Take `⟨C₁, h₁⟩` from `GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound`. Take `⟨C₂, h₂⟩` from `GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell Cb`. Use `⟨max C₁ C₂, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f χ A N w hCb hχ hf hA hthr hw hlen ε hε`.

Establish `hpos : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)`. Check the signs of the components of the expression. Establish `hmono : ∀ C : ℝ, C ≤ max C₁ C₂ → C * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A`. Introduce `C hC`. Use `le_trans ?_ hthr` and prove the remaining obligations.

Rewrite using `[mul_assoc, mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hC hpos`. Take `⟨-, K, hK⟩` from `h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hA (hmono _ (le_max_left _ _)) hlen ε ε hε hε`. Establish `hpt` using `h₂ Wp Wq P p f χ A N w hCb hχ hf hA (hmono _ (le_max_right _ _)) hw hlen ε hε`. Establish `hcpt` using `Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P p.T.base hχ hf hε`.

Establish `hL : ∀ n : ℕ, MemLp (tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) 2 volume` using `fun n => (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb (hcpt n) hw).1`. Use `⟨hL, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto _ volume _ (fun n => tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) _ K hL (Eventually.of_forall hpt) ?_` and prove the remaining obligations. Introduce `n m hnm`. Establish `hsub : KB.CptCoef p.T.base (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m)` using `Formalism.FourierDecayAlt.P.PBN.cpt_sub p.T.base (hcpt n) (hcpt m)`.

Establish `hlin : ∀ c, tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w c - tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c = tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.c …`. Introduce `c`. Establish `h` using `GlobalTheory.T.topVector_add_smul_compactCoefficients Wp Wq P p Cb (-1) _ _ w c hCb hw (hcpt n) (hcpt m)`. Rewrite `h` using `[neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg]`. Conclude with `h.symm`.

Establish `hβ` using `(GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb hsub hw).2`. Establish `hb : ‖B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G) (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w) (Formalism.FourierDecayAlt.P.CutBP.apx (D.cut …` using `hK n m hnm`. Rewrite `hb` using `[hβ, Complex.norm_real]`. Simplify using `only [hlin]`. Conclude with `(le_abs_self _).trans hb`.
-/
theorem tv_approx_tendsto_L2 : P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (A : ℝ) (N : ℕ) (w : List C.Letter), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → C6.IsCut0 χ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A → KB.CutWord P p.l0 w → w.length ≤ N → ∀ ε : ℝ, 0 < ε → (∀ n : ℕ, MemLp (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w) 2 volume) ∧ MemLp (tv p (D.cutF p.T.base χ f ε) w) 2 volume ∧ Tendsto (fun n : ℕ => eLpNorm (tv p ((fun g : B.Mat P.k P.r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF p.T.base χ f ε g)) w - tv p (D.cutF p.T.base χ f ε) w) 2 volume) atTop (𝓝 0) := by
  intro hP Cb
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.levelZeroPairing_compactApproximants_cauchy_bound
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.tendsto_topVector_compactApproximants_bigCell Cb
  refine ⟨max C₁ C₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ A N w hCb hχ hf hA hthr hw hlen ε hε
  have hpos : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₁ C₂ →
      C * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    intro C hC
    refine le_trans ?_ hthr
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC hpos
  obtain ⟨-, K, hK⟩ := h₁ P.k P.r Wp Wq p.T.base (M.sgn P p.l0) w χ f A N hχ hf hA (hmono _ (le_max_left _ _)) hlen
    ε ε hε hε
  have hpt := h₂ Wp Wq P p f χ A N w hCb hχ hf hA (hmono _ (le_max_right _ _)) hw hlen ε hε
  have hcpt := Formalism.FourierDecayAlt.P.CutBP.cptCoef_apx P p.T.base hχ hf hε
  have hL : ∀ n : ℕ, MemLp (tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) 2 volume := fun n =>
    (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb (hcpt n) hw).1
  refine ⟨hL, ?_⟩
  refine GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto _ volume _
    (fun n => tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w) _ K hL (Eventually.of_forall hpt) ?_
  intro n m hnm
  have hsub : KB.CptCoef p.T.base
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) :=
    Formalism.FourierDecayAlt.P.PBN.cpt_sub p.T.base (hcpt n) (hcpt m)
  have hlin : ∀ c, tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n) w c -
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c =
      tv p (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w c := by
    intro c
    have h := GlobalTheory.T.topVector_add_smul_compactCoefficients Wp Wq P p Cb (-1) _ _ w c hCb hw (hcpt n) (hcpt m)
    rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg] at h
    exact h.symm
  have hβ := (GlobalTheory.T.levelZeroForm_eq_bigCell_integral_topDensity_compact hP Wp Wq P p Cb _ w hCb hsub hw).2
  have hb : ‖B.beta p.T.base (List.foldr (fun (a : Bool × ℝ) G => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) G)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m) w)
      (Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) n - Formalism.FourierDecayAlt.P.CutBP.apx (D.cutF p.T.base χ f ε) m)‖ ≤
      K / ((n : ℝ) + 1) := hK n m hnm
  rw [hβ, Complex.norm_real] at hb
  simp only [hlin]
  exact (le_abs_self _).trans hb

end GlobalTheory.TopVec
