import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormLevLimit

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, fun g hg hne => he.trans (h.2.2 g hg hne)⟩`.
-/
theorem cccoef_mono {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {Bs : B.RealPlaceData k r Wp Wq} {A : ℝ} {mm : ℕ} {ε ε' : ℝ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (h : JC.CCCoefM Bs A mm ε' F) (he : ε ≤ ε') : JC.CCCoefM Bs A mm ε F :=
  ⟨h.1, h.2.1, fun g hg hne => he.trans (h.2.2 g hg hne)⟩

/- English proof (translation)
Rewrite using `[hcut]`. Simplify using `[JCx2.pdPsi, JCx2.pdPhi, JCx2.pdChi, JCx2.pdSq]`.
-/
theorem cut_eq {k r : ℕ} (cut : ℕ → B.Mat k r → ℂ)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) (g : B.Mat k r) :
    cut n g = 1 - JCx2.pdPsi ((n : ℝ) + 1) g := by
  rw [hcut]
  simp [JCx2.pdPsi, JCx2.pdPhi, JCx2.pdChi, JCx2.pdSq]

/- English proof (translation)
Take `⟨Cs, hCs0, hSQ⟩` from `sliceQ`. Use `⟨Cs + 1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b`. Establish `hk2 : 2 ≤ P.k` using `p.hl.2.2`. Use `set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX`.

Establish `hX1 : 1 ≤ X`. Establish `h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1`. Establish `: (0 : ℝ) ≤ P.r` using `Nat.cast_nonneg _`. Establish `: (0 : ℝ) ≤ P.k` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3` using `one_le_pow₀ h1`. Establish `: 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4` using `one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)`. Establish `hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1`.

Establish `h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A` using `le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA`. Establish `h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use `set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM`. Take `⟨bf, hbf⟩` from `hfA M`.

Establish `hbf0 : 0 ≤ bf` using `JCx2.pd_ccle_nonneg hbf`. Establish `hbf' : B.CCle (A - 1) M f bf` using `BetaSesquilinearity.CCle_mono_A (by linarith) hbf`. Take `⟨Kp, hKp0, hKp⟩` from `JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M`. Establish `hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1))` using `fun n => hKp _ (by positivity) A f bf hbf`. Establish `hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g)` using `fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf`.

Use `set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn`. Establish `hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g)`. Introduce `n`. Use function extensionality and compare the values at `g`. Simplify using `only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]`.

Simplify using `[sub_eq_add_neg]`. Establish `hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf)`. Introduce `n`. Rewrite using `[hneq n]`. Use `JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_` and prove the remaining obligations.

Establish `h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf` using `div_le_self (by positivity) (by`. Establish `: (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use the proof step `linarith)`. Simplify using `only [norm_neg, norm_one, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n)`. Introduce `n`. Rewrite using `[hneq n]`. Conclude with `BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))`. Establish `hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g`.

Introduce `n`. Use function extensionality and compare the values at `g`. Rewrite using `[hneq n]`. Simplify using the standard rewrite rules. Establish `hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε`.

Introduce `n`. Use function extensionality and compare the values at `g`. Simplify using `only [D.cutF, hhn]`. Rewrite using `[smul_comm]`. Simplify using `only [KB.Pl.RR, hFn]`.

Unfold `D.RRplace`. Distinguish the cases in `hab : D.IsLocPt a i ∧ D.IsLocPt b i`. Use `swap`. Simplify using `only [dif_neg hab]`. Conclude with `tendsto_const_nhds`.

Simplify using `only [dif_pos hab, dif_pos hi]`. Establish `hca : P.r - i = P.r - D.ptSize a` using `by simp [hab.1.2]`. Establish `hcb : P.r - i = P.r - D.ptSize b` using `by simp [hab.2.2]`. Establish `hQa` using `fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e`. Establish `hQb` using `fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e`.

Use `choose εa Ka hεa hKa hQ1a hQ2a using hQa`. Use `choose εb Kb hεb hKb hQ1b hQ2b using hQb`. Use `set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS`. Establish `hSa : ∀ e, (εa e)⁻¹ ≤ S`. Introduce `e`.

Establish `h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹` using `Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)`. Establish `h2 : 0 ≤ ∑ e, (εb e)⁻¹` using `Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSb : ∀ e, (εb e)⁻¹ ≤ S`. Introduce `e`.

Establish `h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹` using `Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)`. Establish `h2 : 0 ≤ ∑ e, (εa e)⁻¹` using `Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS0 : 0 < S` using `lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)`. Establish `hε₀a : ∀ e, S⁻¹ ≤ εa e` using `fun e => by`.

Use `inv_anti₀ (inv_pos.2 (hεa e)) (hSa e)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Establish `hε₀b : ∀ e, S⁻¹ ≤ εb e` using `fun e => by`. Use `inv_anti₀ (inv_pos.2 (hεb e)) (hSb e)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.

Use `set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK`. Establish `hKa' : ∀ e, Ka e ≤ KK`. Introduce `e`. Establish `h1 : Ka e ≤ ∑ e, Ka e` using `Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)`. Establish `h2 : 0 ≤ ∑ e, Kb e` using `Finset.sum_nonneg fun e _ => hKb e`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKb' : ∀ e, Kb e ≤ KK`. Introduce `e`. Establish `h1 : Kb e ≤ ∑ e, Kb e` using `Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)`. Establish `h2 : 0 ≤ ∑ e, Ka e` using `Finset.sum_nonneg fun e _ => hKa e`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hKK0 : 0 ≤ KK` using `le_trans (hKa Wd.e1) (hKa' Wd.e1)`. Establish `hB1 : bf ≤ bf + Kp * bf` using `by nlinarith`. Establish `main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ), (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) → (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c → JC.CCCoefM (p.T.bs i) (P5.Ause …`. Introduce `q hcq εq Kq hεq hKq hKq' hQ1 hQ2`.

Use `⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hQ1 e f bf hf hbf'`. Conclude with `⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩`. Take `⟨h1, h2⟩` from `hQ1 e (hn n) _ (hns n) (hnC n)`. Conclude with `⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩`.

Take `⟨h1, h2⟩` from `hQ1 e _ _ (hψs n) (hψ n)`. Establish `hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ = (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ`. Introduce `γ hγ`. Use `hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ` as an intermediate fact. Rewrite `this` using `[hsub n]`.

Simplify using `only [Pi.sub_apply, ← this]`. Simplify using the standard rewrite rules. Establish `hC2` using `Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)`. Simplify using `only [norm_neg, norm_one, one_mul] at hC2`. Establish `hC3` using `JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))`.

Use `⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩` and prove the remaining obligations. Rewrite `hne` using `[← hd γ hγ]`. Establish `hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Simplify using `[h0]`. Conclude with `(hεq e).trans (h1.2.2 γ hγ hne')`. Take `⟨ma1, ma2, ma3⟩` from `main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a`. Take `⟨mb1, mb2, mb3⟩` from `main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b`. Establish `hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0)`.

Establish `h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat.congr (fun n => by simp)`. Use `(h1.const_mul (Kp * bf)).const_mul KK` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv, mul_assoc]`. Conclude with `formLev_limit P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0) (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f) (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n)) (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 m …`.
-/
theorem belowTop : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ Cc : ℝ, Cl ≤ Cc →
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε A : ℝ) (N : ℕ) (cut : ℕ → B.Mat P.k P.r → ℂ),
    C6.IsCut0 χ → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A m f) →
    Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
    (∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) →
    ∀ i, i ≤ P.r → ∀ w : List C.Letter, w.length ≤ N → ∀ a b,
      Tendsto (fun n => p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) i w a b) atTop
        (𝓝 (p.RR (D.cutF p.T.base χ f ε) i w a b)) := by
  obtain ⟨Cs, hCs0, hSQ⟩ := sliceQ
  refine ⟨Cs + 1, by positivity, ?_⟩
  intro Cc hCc Wp Wq _ _ _ _ _ _ P p f χ ε A N cut hχ hε hf hfA hA hcut i hi w hw a b
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set X : ℝ := (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    linarith
  have hR4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * X ≤ A - 1 := by
    have h1 : (Cs + 1) * ((P.r : ℝ) + 1) ^ 4 * X ≤ A :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc (by positivity)) (by positivity)) hA
    have h2 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 * X := by nlinarith
    nlinarith
  set M := 3 * (11 * (N * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hM
  obtain ⟨bf, hbf⟩ := hfA M
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) M f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) M
  have hψ : ∀ n : ℕ, B.CCle (A - 1) M (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => JCx2.pd_smooth_smul (JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) M (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact BetaSesquilinearity.CkOn_add hf (BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hsub : ∀ n, (fun g => f g - hn n g) = fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g := by
    intro n; funext g
    rw [hneq n]; simp
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  simp only [KB.Pl.RR, hFn]
  unfold D.RRplace
  by_cases hab : D.IsLocPt a i ∧ D.IsLocPt b i
  swap
  · simp only [dif_neg hab]; exact tendsto_const_nhds
  simp only [dif_pos hab, dif_pos hi]
  have hca : P.r - i = P.r - D.ptSize a := by simp [hab.1.2]
  have hcb : P.r - i = P.r - D.ptSize b := by simp [hab.2.2]
  have hQa := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw a hca hab.1 e
  have hQb := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N P rfl rfl hk2 hχ hA' ε hε i hi w hw b hcb hab.2 e
  choose εa Ka hεa hKa hQ1a hQ2a using hQa
  choose εb Kb hεb hKb hQ1b hQ2b using hQb
  set S : ℝ := ∑ e, (εa e)⁻¹ + ∑ e, (εb e)⁻¹ with hS
  have hSa : ∀ e, (εa e)⁻¹ ≤ S := by
    intro e
    have h1 : (εa e)⁻¹ ≤ ∑ e, (εa e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εa e)⁻¹) (fun e _ => (inv_pos.2 (hεa e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εb e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεb e)).le
    linarith
  have hSb : ∀ e, (εb e)⁻¹ ≤ S := by
    intro e
    have h1 : (εb e)⁻¹ ≤ ∑ e, (εb e)⁻¹ :=
      Finset.single_le_sum (f := fun e => (εb e)⁻¹) (fun e _ => (inv_pos.2 (hεb e)).le) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, (εa e)⁻¹ := Finset.sum_nonneg fun e _ => (inv_pos.2 (hεa e)).le
    linarith
  have hS0 : 0 < S := lt_of_lt_of_le (inv_pos.2 (hεa Wd.e1)) (hSa Wd.e1)
  have hε₀a : ∀ e, S⁻¹ ≤ εa e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεa e)) (hSa e); rwa [inv_inv] at this
  have hε₀b : ∀ e, S⁻¹ ≤ εb e := fun e => by
    have := inv_anti₀ (inv_pos.2 (hεb e)) (hSb e); rwa [inv_inv] at this
  set KK : ℝ := ∑ e, Ka e + ∑ e, Kb e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := by
    intro e
    have h1 : Ka e ≤ ∑ e, Ka e := Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Kb e := Finset.sum_nonneg fun e _ => hKb e
    linarith
  have hKb' : ∀ e, Kb e ≤ KK := by
    intro e
    have h1 : Kb e ≤ ∑ e, Kb e := Finset.single_le_sum (f := Kb) (fun e _ => hKb e) (Finset.mem_univ e)
    have h2 : 0 ≤ ∑ e, Ka e := Finset.sum_nonneg fun e _ => hKa e
    linarith
  have hKK0 : 0 ≤ KK := le_trans (hKa Wd.e1) (hKa' Wd.e1)
  have hB1 : bf ≤ bf + Kp * bf := by nlinarith

  have main : ∀ (q : C.LPt) (hcq : P.r - i = P.r - D.ptSize q) (εq Kq : Wd.Ix (Fin w.length) → ℝ),
      (∀ e, S⁻¹ ≤ εq e) → (∀ e, 0 ≤ Kq e) → (∀ e, Kq e ≤ KK) →
      (∀ e (h : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h → B.CCle (A - 1) M h c →
        JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) (εq e) (xs p.T χ ε i hi w q hcq h e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq h e) (Kq e * c)) →
      (∀ e (h₁ h₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (c₁ c₂ : ℝ), B.CkOn ⊤ (B.GV P.k P.r) h₁ →
        B.CkOn ⊤ (B.GV P.k P.r) h₂ → B.CCle (A - 1) M h₁ c₁ → B.CCle (A - 1) M h₂ c₂ →
        ∀ γ ∈ B.GV P.k (P.r - i), xs p.T χ ε i hi w q hcq h₁ e γ - xs p.T χ ε i hi w q hcq h₂ e γ =
          xs p.T χ ε i hi w q hcq (fun g => h₁ g - h₂ g) e γ) →
      (∀ e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq f e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹ (xs p.T χ ε i hi w q hcq (hn n) e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N) (xs p.T χ ε i hi w q hcq (hn n) e) (KK * (bf + Kp * bf))) ∧
      (∀ n e, JC.CCCoefM (p.T.bs i) (P5.Auser P N + 1) (P5.mmUser P N) S⁻¹
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) ∧
        B.CCle (P5.Auser P N + 1) (P5.mmUser P N)
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) (KK * (Kp * bf / ((n : ℝ) + 1)))) := by
    intro q hcq εq Kq hεq hKq hKq' hQ1 hQ2
    refine ⟨fun e => ?_, fun n e => ?_, fun n e => ?_⟩
    · obtain ⟨h1, h2⟩ := hQ1 e f bf hf hbf'
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul (hKq' e) hB1 hbf0 hKK0)⟩
    · obtain ⟨h1, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
      exact ⟨cccoef_mono h1 (hεq e), JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))⟩
    · obtain ⟨h1, h2⟩ := hQ1 e _ _ (hψs n) (hψ n)
      have hd : ∀ γ ∈ B.GV P.k (P.r - i), (fun γ => (-1 : ℂ) • xs p.T χ ε i hi w q hcq
          (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ) γ =
          (xs p.T χ ε i hi w q hcq (hn n) e - xs p.T χ ε i hi w q hcq f e) γ := by
        intro γ hγ
        have := hQ2 e f (hn n) bf _ hf (hns n) hbf' (hnC n) γ hγ
        rw [hsub n] at this
        simp only [Pi.sub_apply, ← this]
        simp
      have hC2 := Formalism.FourierDecayAlt.P.Ux1.cc_congr hd (BetaSesquilinearity.CCle_smul (-1) h2)
      simp only [norm_neg, norm_one, one_mul] at hC2
      have hC3 := JCx2.pd_ccle_mono_c hC2 (mul_le_mul_of_nonneg_right (hKq' e) (by positivity))
      refine ⟨⟨hC3.1, ⟨_, hC3⟩, fun γ hγ hne => ?_⟩, hC3⟩
      rw [← hd γ hγ] at hne
      have hne' : xs p.T χ ε i hi w q hcq (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) e γ ≠ 0 := by
        intro h0; apply hne; simp [h0]
      exact (hεq e).trans (h1.2.2 γ hγ hne')
  obtain ⟨ma1, ma2, ma3⟩ := main a hca εa Ka hε₀a hKa hKa' hQ1a hQ2a
  obtain ⟨mb1, mb2, mb3⟩ := main b hcb εb Kb hε₀b hKb hKb' hQ1b hQ2b
  have hdn : Tendsto (fun n : ℕ => KK * (Kp * bf / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat.congr
      (fun n => by simp)
    have := (h1.const_mul (Kp * bf)).const_mul KK
    simpa [div_eq_mul_inv, mul_assoc] using this
  exact formLev_limit P p.T _ ⟨i, by omega⟩ w N hw S⁻¹ (inv_pos.2 hS0)
    (xs p.T χ ε i hi w a hca f) (xs p.T χ ε i hi w b hcb f)
    (fun n => xs p.T χ ε i hi w a hca (hn n)) (fun n => xs p.T χ ε i hi w b hcb (hn n))
    (KK * (bf + Kp * bf)) (fun n => KK * (Kp * bf / ((n : ℝ) + 1))) hdn ma1 mb1 ma2 mb2 ma3 mb3

/- English proof (translation)
Establish `hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n)`. Establish `e : cut n = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g` using `funext fun g => cut_eq cut hcut n g`. Rewrite using `[e]`. Conclude with `contDiff_const.sub (JCx2.pd_psi_cd _)`. Use `⟨JCx2.pd_smooth_smul hcs (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε), ⟨2 * ((n : ℝ) + 1), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `g _ hne`. Establish `hc : cut n g ≠ 0` using `by intro h0; apply hne; simp [h0]`. Rewrite `hc` using `[hcut]`. Establish `hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Apply `hc` to reduce the goal to its premises. Rewrite using `[Real.smoothTransition.zero_of_nonpos hle]`. Simplify using the standard rewrite rules. Establish `hn1 : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`.

Establish `hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) = ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2`. Rewrite `hpos` using `[hsum]`. Establish `h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4` using `by linarith`.

Establish `h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) = ∑ i, ∑ j, Complex.normSq (g i j)`. Clear the denominators using the available nonvanishing facts. Establish `h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4` using `mul_lt_mul_of_pos_left h1 (by positivity)`. Rewrite `h3` using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `B.gN`. Rewrite using `[show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]`. Conclude with `Real.sqrt_le_sqrt (by nlinarith)`. Take `⟨δ, hδ, hδ0⟩` from `hχ.2.1`. Use `⟨δ * ε, by positivity, fun g _ hne => ?_⟩` and prove the remaining obligations.

Establish `hc : χ (Gf P.k P.r Bs.z Bs.z' g / ε) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Simplify using `[D.cutF, h0]`. Establish `h1 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hc (hδ0 _ hlt)`. Rewrite `h1` using `[le_div_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cutCpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ) (cut : ℕ → B.Mat P.k P.r → ℂ)
    (hχ : C6.IsCut0 χ) (hε : 0 < ε) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcut : ∀ n g, cut n g = ((Real.smoothTransition
      ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) (n : ℕ) :
    KB.CptCoef Bs fun g => cut n g • D.cutF Bs χ f ε g := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cut n) := by
    have e : cut n = fun g => 1 - JCx2.pdPsi ((n : ℝ) + 1) g := funext fun g => cut_eq cut hcut n g
    rw [e]
    exact contDiff_const.sub (JCx2.pd_psi_cd _)
  refine ⟨JCx2.pd_smooth_smul hcs (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε), ⟨2 * ((n : ℝ) + 1), ?_⟩, ?_⟩
  · intro g _ hne
    have hc : cut n g ≠ 0 := by intro h0; apply hne; simp [h0]
    rw [hcut] at hc
    have hpos : 0 < (4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3 := by
      by_contra hle
      push_neg at hle
      apply hc
      rw [Real.smoothTransition.zero_of_nonpos hle]
      simp
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hsum : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j) =
        ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
      ring
    have hlt : ∑ i, ∑ j, Complex.normSq (g i j) < 4 * ((n : ℝ) + 1) ^ 2 := by
      rw [hsum] at hpos
      have h1 : ((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j) < 4 := by linarith
      have h2 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) =
          ∑ i, ∑ j, Complex.normSq (g i j) := by
        field_simp
      have h3 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1)⁻¹ ^ 2 * ∑ i, ∑ j, Complex.normSq (g i j)) < ((n : ℝ) + 1) ^ 2 * 4 :=
        mul_lt_mul_of_pos_left h1 (by positivity)
      rw [h2] at h3
      linarith
    unfold B.gN
    rw [show (2 * ((n : ℝ) + 1)) = Real.sqrt ((2 * ((n : ℝ) + 1)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · obtain ⟨δ, hδ, hδ0⟩ := hχ.2.1
    refine ⟨δ * ε, by positivity, fun g _ hne => ?_⟩
    have hc : χ (Gf P.k P.r Bs.z Bs.z' g / ε) ≠ 0 := by
      intro h0; apply hne; simp [D.cutF, h0]
    have h1 : δ ≤ Gf P.k P.r Bs.z Bs.z' g / ε := by
      by_contra hlt; push_neg at hlt; exact hc (hδ0 _ hlt)
    rw [le_div_iff₀ hε] at h1
    linarith

end Formalism.FourierDecayAlt.P.PBE
