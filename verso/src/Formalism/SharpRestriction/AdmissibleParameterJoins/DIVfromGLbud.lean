import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLo

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

/- English proof (translation)
Unfold `WeightDegreeSizes.LevelPrimeBudget`. Conclude with `h`.
-/
theorem levelPrime_budget_of_fifth {C : ℝ} (h : ∀ u, product_first_zeroth_parts.WeightBudgetBound D u L C) : WeightDegreeSizes.LevelPrimeBudget D L C := by
  unfold WeightDegreeSizes.LevelPrimeBudget
  exact h

/- English proof (translation)
Establish `key : ∀ X e : ℝ, 256 ≤ X → 0 < e → e < 1 / 52 → (4 : ℝ) ≤ X ^ (-(e / 100)) * Real.sqrt (X * X ^ (-(e / 8)))`. Introduce `X e hX he he'`. Establish `hX0 : 0 < X` using `by linarith`. Establish `h1 : X * X ^ (-(e / 8)) = X ^ (1 + -(e / 8))`. Rewrite using `[Real.rpow_add hX0, Real.rpow_one]`.

Rewrite using `[h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]`. Establish `h256 : (4 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 4)`. Rewrite using `[show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]`. Evaluate the numerical expressions. Rewrite using `[h256]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨Cn₀, hCn⟩` from `numsL_wtsL_fam Fm hT hDl`. Take `⟨x2, hx2⟩` from `hCn Cn₀ le_rfl 3 le_rfl`. Take `⟨x3, hx3⟩` from `hT`. Use `⟨max (max x2 x3) (max (Fm.x1 + 1) 256), fun x hx i u => ?_⟩` and prove the remaining obligations.

Establish `hxa : x2 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb : x3 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hx1 : Fm.x1 < x`. Establish `: Fm.x1 + 1 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h256 : (256 : ℝ) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Take `⟨hN, hW⟩` from `hx2 x hxa i`. Establish `hTu` using `(hx3 x hxb i).1`. Establish `hm : 4 ≤ (Fm.D x i).R.m`. Establish `S` using `Fm.sizes x hx1 i`.

Establish `hM : SizeM (Fm.L x i)` using `S.2.1`. Unfold `SizeM szTh Scale.delta1 at hM`. Establish `hX : (256 : ℝ) ≤ (Fm.L x i).sc.x`. Rewrite using `[Fm.L_x x i hx1]`. Conclude with `h256`.

Establish `h4` using `key _ _ hX (Fm.L x i).sc.eps_pos (Fm.L x i).sc.eps_lt`. Conclude with `h4.trans hM.1` after adjusting the coercions. Conclude with `levelPrime_setting_of_sizes le_rfl hN hW hTu hm u`.
-/
theorem setting_fam {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u := by
  have key : ∀ X e : ℝ, 256 ≤ X → 0 < e → e < 1 / 52 →
      (4 : ℝ) ≤ X ^ (-(e / 100)) * Real.sqrt (X * X ^ (-(e / 8))) := by
    intro X e hX he he'
    have hX0 : 0 < X := by linarith
    have h1 : X * X ^ (-(e / 8)) = X ^ (1 + -(e / 8)) := by
      rw [Real.rpow_add hX0, Real.rpow_one]
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    have h256 : (4 : ℝ) = (256 : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [show (256 : ℝ) = 4 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h256]
    calc (256 : ℝ) ^ ((1 : ℝ) / 4) ≤ X ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ (-(e / 100) + (1 + -(e / 8)) * (1 / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  obtain ⟨x3, hx3⟩ := hT
  refine ⟨max (max x2 x3) (max (Fm.x1 + 1) 256), fun x hx i u => ?_⟩
  have hxa : x2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    linarith
  have h256 : (256 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hN, hW⟩ := hx2 x hxa i
  have hTu := (hx3 x hxb i).1
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have S := Fm.sizes x hx1 i
    have hM : SizeM (Fm.L x i) := S.2.1
    unfold SizeM szTh Scale.delta1 at hM
    have hX : (256 : ℝ) ≤ (Fm.L x i).sc.x := by
      rw [Fm.L_x x i hx1]
      exact h256
    have h4 := key _ _ hX (Fm.L x i).sc.eps_pos (Fm.L x i).sc.eps_lt
    exact_mod_cast h4.trans hM.1
  exact levelPrime_setting_of_sizes le_rfl hN hW hTu hm u

/- English proof (translation)
Take `⟨x1, hx1⟩` from `setting_fam Fm hT hDl`. Take `⟨C, x0, hB⟩` from `hB`. Use `⟨C, max x0 x1, fun x hx i => levelPrime_budget_of_fifth (fun u => hB x (le_trans (le_max_left _ _) hx) i u (hx1 x (le_trans (le_max_right _ _) hx) i u))⟩` and prove the remaining obligations.
-/
theorem family_levelPrime_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hB : product_first_zeroth_parts.BudF Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨x1, hx1⟩ := setting_fam Fm hT hDl
  obtain ⟨C, x0, hB⟩ := hB
  refine ⟨C, max x0 x1, fun x hx i => levelPrime_budget_of_fifth (fun u =>
    hB x (le_trans (le_max_left _ _) hx) i u (hx1 x (le_trans (le_max_right _ _) hx) i u))⟩

/- English proof (translation)
Unfold `WeightDegreeSizes.StabiliserLogBound`. Unfold `FactDGam at hG`. Introduce `u`. Establish `hNu` using `hN u`. Unfold `flipTwoThree.Nums at hNu`.

Take `⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩` from `hNu`. Establish `hfk : D.R.f ≤ D.R.k`. Unfold `Ranks.f`. Conclude with `D.R.f_le_k`. Establish `hmf : D.R.m ≤ D.R.f`.

Unfold `Ranks.f`. Conclude with `D.R.m_le_f`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`. Establish `hkN : D.R.k ≤ D.R.N D.R.m`. Unfold `Ranks.N`.

Use linear arithmetic over natural numbers and integers. Establish `hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ)` using `by exact_mod_cast hfk.trans hkN`. Establish `hf2 : (2 : ℝ) ≤ D.R.f` using `by exact_mod_cast hm2.trans hmf`. Establish `hm2r : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm2`. Establish `hN0 : (0 : ℝ) < D.R.N D.R.m` using `by linarith`.

Establish `hx1` using `L.sc.one_lt_alt`. Establish `hLr : 1 ≤ L.sc.L`. Unfold `Scale.L`. Conclude with `Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b`.

Clear the denominators using the available nonvanishing facts. Rewrite `hb'` using `[hbb]`. Establish `hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b`. Establish `: (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L)`.

Apply `mul_le_mul_of_nonneg_left _ hN0.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L`. Establish `hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L`.

Establish `: (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L` using `le_mul_of_one_le_right hN0.le hLr`. Establish `hb : L.sc.b = Real.exp L.sc.L` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Establish `hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ)` using `Real.log_le_log (by linarith) hfN`.

Establish `hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L`. Rewrite using `[Real.log_mul (by linarith) hN0.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L` using `rfl`. Establish `hb0' : 0 < L.sc.b` using `Real.exp_pos _`.

Establish `key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0`. Establish `h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L)` using `mul_le_mul_of_nonneg_left hlog (by positivity)`. Establish `h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b` using `mul_le_mul_of_nonneg_left hNL' (by positivity)`. Establish `h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L)` using `mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)`. Rewrite using `[hB0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hG'` using `hG u`. Use `mul_le_mul_of_nonneg_left key hCG` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

/- English proof (translation)
Take `⟨CG, x0, hG⟩` from `hG`. Take `⟨Cn₀, hCn⟩` from `numsL_wtsL_fam Fm hT hDl`. Take `⟨x2, hx2⟩` from `hCn Cn₀ le_rfl 3 le_rfl`. Use `⟨4 * max CG 0, max x0 x2, fun x hx i => ?_⟩` and prove the remaining obligations. Conclude with `gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hx2 x (le_trans (le_max_right _ _) hx) i).1 (factDGam_mono (hG x (le_trans (le_max_left _ _) hx) i) (le_max_left _ _))`.
-/
theorem family_gammaDiscriminant_budget {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hDl : DlSize Fm) (hG : DGamSize Fm) :
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  obtain ⟨CG, x0, hG⟩ := hG
  obtain ⟨Cn₀, hCn⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x2, hx2⟩ := hCn Cn₀ le_rfl 3 le_rfl
  refine ⟨4 * max CG 0, max x0 x2, fun x hx i => ?_⟩
  exact gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hx2 x (le_trans (le_max_right _ _) hx) i).1
    (factDGam_mono (hG x (le_trans (le_max_left _ _) hx) i) (le_max_left _ _))

end Formalism.MainNotions.J

end
