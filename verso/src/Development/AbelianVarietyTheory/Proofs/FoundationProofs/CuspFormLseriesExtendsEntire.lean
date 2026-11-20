import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFormGamma1OfIsCuspFormCoeffSeqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinMeanSquareCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefQExpansionFunctionUpperHalfPlaneStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Establish `key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `: 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem div_le_half_sq_add {t x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    t / x ≤ (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 := by
  have key : (t ^ 2 / y + y * x⁻¹ * x⁻¹) / 2 - t / x = (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * x ^ 2 * y) := by positivity
  linarith

/- English proof (translation)
Use `set σ := s.re with hσ`. Use `set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ`. Establish `hδ0 : 0 < δ` using `by rw [hδ]; linarith`. Establish `h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ)` using `hsq δ hδ0`. Establish `h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ))` using `Real.summable_nat_rpow.mpr (by linarith)`.

Use `Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_` and prove the remaining obligations. Rewrite using `[LSeries.norm_term_eq]`. Use `split_ifs with hn`. Establish `: 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ)` using `by positivity`. Establish `: 0 ≤ (n : ℝ) ^ (-(1 + δ))` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn' : (0 : ℝ) < n` using `Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)`. Establish `e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹`. Rewrite using `[show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn', Real.rpow_neg hn'.le]`. Rewrite using `[e]`.

Conclude with `div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)`.
-/
theorem lseriesSummable_of_sq (a : ℕ → ℂ) (k : ℕ)
    (hsq : ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + s))
    (s : ℂ) (hs : ((k : ℝ) + 1) / 2 < s.re) : LSeriesSummable a s := by
  set σ := s.re with hσ
  set δ : ℝ := σ - ((k : ℝ) + 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 : Summable fun n : ℕ => ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := hsq δ hδ0
  have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + δ)) := Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · have : 0 ≤ ‖a n‖ ^ 2 / (n : ℝ) ^ ((k : ℝ) + δ) := by positivity
    have : 0 ≤ (n : ℝ) ^ (-(1 + δ)) := by positivity
    linarith
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have e : (n : ℝ) ^ (-(1 + δ)) = (n : ℝ) ^ ((k : ℝ) + δ) * ((n : ℝ) ^ σ)⁻¹ * ((n : ℝ) ^ σ)⁻¹ := by
      rw [show -(1 + δ) = ((k : ℝ) + δ) + -σ + -σ by rw [hδ]; ring, Real.rpow_add hn', Real.rpow_add hn',
        Real.rpow_neg hn'.le]
    rw [e]
    exact div_le_half_sq_add (Real.rpow_pos_of_pos hn' σ) (Real.rpow_pos_of_pos hn' _)

/- English proof (translation)
Introduce `k L N ε g hk hL hNL hcf`. Use `haveI : NeZero L := ⟨hL.ne'⟩`. Take `⟨f, hf⟩` from `GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε g hk hL hNL hcf`. Establish `hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n` using `fun n => by`. Establish `h` using `GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane g hcf.1.1 n`.

Rewrite `h` using `[coef, ← hf]`. Conclude with `h`. Establish `hk0 : (0 : ℤ) < (k : ℤ)` using `by exact_mod_cast hk`. Establish `hsq` using `(GlobalTheory.T.rankin_mean_square_cuspForm k L (ch ε) g hk hcf).2.2.1`. Establish `hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s` using `lseriesSummable_of_sq g k hsq`.

Establish `habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal)` using `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)`. Establish `hdiff : Differentiable ℂ (ModularForm.L hk0 f)` using `CuspForm.differentiable_L hk0 f`. Establish `hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s`. Introduce `s hs`. Establish `h` using `CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)`.

Simplify using `only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h`. Establish `hs0 : s ≠ 0`. Introduce `h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[LSeries, ← h.tsum_eq]`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Rewrite using `[LSeries.term_of_ne_zero' hs0, hcoef]`. Use `⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩` and prove the remaining obligations. Use `set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU`.

Establish `hLU : AnalyticOnNhd ℂ (LSeries g) U` using `(LSeries_analyticOnNhd g).mono fun c hc => by`. Simplify using `only [Set.mem_setOf_eq, hU] at hc ⊢`. Conclude with `lt_of_le_of_lt habs (by exact_mod_cast hc)`. Establish `hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U` using `fun z _ => hdiff.analyticAt z`. Establish `hconn : IsPreconnected U` using `(convex_halfSpace_re_gt _).isPreconnected`.

Use `set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀`. Establish `hz₀re : z₀.re = (k : ℝ) + 2` using `by rw [hz₀, Complex.ofReal_re]`. Establish `hk' : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hz₀U : z₀ ∈ U` using `by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith`. Establish `hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f`.

Establish `hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Use `filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc`. Conclude with `hagree c hc`. Conclude with `hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs`.
-/
theorem lseries_cusp_entire : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) g → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s ∧ LSeries g s = Λ s := by
  intro k L N ε g hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_cuspForm_gamma1_of_isCuspFormCoeffSeq k L N ε g hk hL hNL hcf
  have hcoef : ∀ n, (qExpansion 1 ⇑f).coeff n = g n := fun n => by
    have h := GlobalTheory.T.coef_qExpansionFunctionUpperHalfPlane g hcf.1.1 n
    rw [coef, ← hf] at h
    exact h
  have hk0 : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hsq := (GlobalTheory.T.rankin_mean_square_cuspForm k L (ch ε) g hk hcf).2.2.1
  have hsum : ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re → LSeriesSummable g s := lseriesSummable_of_sq g k hsq
  have habs : LSeries.abscissaOfAbsConv g ≤ (((((k : ℝ) + 1) / 2 : ℝ)) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => hsum y (by simpa using hy)
  have hdiff : Differentiable ℂ (ModularForm.L hk0 f) := CuspForm.differentiable_L hk0 f

  have hagree : ∀ s : ℂ, (k : ℝ) / 2 + 1 < s.re → LSeries g s = ModularForm.L hk0 f s := by
    intro s hs
    have h := CuspForm.hasSum_L hk0 f (s := s) (by rw [Int.cast_natCast]; exact hs)
    simp only [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hs0 : s ≠ 0 := by
      intro h0; rw [h0, Complex.zero_re] at hs; have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    rw [LSeries, ← h.tsum_eq]
    congr 1
    funext n
    rw [LSeries.term_of_ne_zero' hs0, hcoef]
  refine ⟨ModularForm.L hk0 f, hdiff, fun s hs => ⟨hsum s hs, ?_⟩⟩
  set U : Set ℂ := {c : ℂ | ((k : ℝ) + 1) / 2 < c.re} with hU
  have hLU : AnalyticOnNhd ℂ (LSeries g) U := (LSeries_analyticOnNhd g).mono fun c hc => by
    simp only [Set.mem_setOf_eq, hU] at hc ⊢
    exact lt_of_le_of_lt habs (by exact_mod_cast hc)
  have hΛU : AnalyticOnNhd ℂ (ModularForm.L hk0 f) U := fun z _ => hdiff.analyticAt z
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := (((k : ℝ) + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = (k : ℝ) + 2 := by rw [hz₀, Complex.ofReal_re]
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hz₀U : z₀ ∈ U := by simp only [hU, Set.mem_setOf_eq, hz₀re]; linarith
  have hev : LSeries g =ᶠ[𝓝 z₀] ModularForm.L hk0 f := by
    have hopen : IsOpen {c : ℂ | (k : ℝ) / 2 + 1 < c.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [Set.mem_setOf_eq, hz₀re]; linarith)] with c hc
    exact hagree c hc
  exact hLU.eqOn_of_preconnected_of_eventuallyEq hΛU hconn hz₀U hev hs

end GlobalTheory.EisM
