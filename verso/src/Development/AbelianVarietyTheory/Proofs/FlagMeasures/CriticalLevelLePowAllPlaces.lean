import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstVandermondeNodeLargeOfSmallThreshold
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelUpper

/- English proof (translation)
Establish `hb0 : 0 < b` using `by linarith`. Establish `hk0 : 0 < k` using `by nlinarith`. Establish `hkm : 0 ≤ k * m` using `by positivity`. Establish `hE1a : 0 ≤ (m - 1) * k + m * (m - 1) / 2` using `by nlinarith`. Establish `hE1b : (m - 1) * k + m * (m - 1) / 2 ≤ 3 / 2 * (k * m)` using `by nlinarith`.

Establish `hE3a : 0 ≤ k * m + m * (m - 1) / 2` using `by nlinarith`. Establish `hE3b : k * m + m * (m - 1) / 2 ≤ 3 / 2 * (k * m)` using `by nlinarith`. Establish `hP1 : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) ≤ b ^ (3 / 2 * (k * m))`. Rewrite using `[Real.rpow_neg hka0.le, ← Real.inv_rpow hka0.le]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hP10 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2))` using `Real.rpow_nonneg hka0.le _`. Establish `hP2 : rd ^ (-((m - 1) / 2)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hrd1 (by linarith)`. Establish `hP20 : 0 ≤ rd ^ (-((m - 1) / 2))` using `Real.rpow_nonneg (by linarith) _`. Establish `hP3 : g ^ (k * m + m * (m - 1) / 2) ≤ b ^ (3 * Cg * (k * m))`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.rpow_le_rpow_of_exponent_le hb1.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hP30 : 0 ≤ g ^ (k * m + m * (m - 1) / 2)` using `Real.rpow_nonneg hg0 _`. Establish `hX0 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q` using `by positivity`. Establish `hXb : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q ≤ b ^ (k * ((4 * Cg + 12) * m))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_add hb0, Real.rpow_add hb0]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ b ^ (k * ((4 * Cg + 12) * m)) := by`. Apply `Real.rpow_le_rpow_of_exponent_le hb1.le` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hb0.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem root_le (ka rd g Q b Cg m k : ℝ) (hb1 : 1 < b) (hm : 2 ≤ m) (hmk : 40 * m ^ 2 ≤ k)
    (hka0 : 0 < ka) (hki : ka⁻¹ ≤ b) (hrd1 : 1 ≤ rd) (hg0 : 0 ≤ g) (hgg : g ≤ b ^ (2 * Cg)) (hCg : 0 ≤ Cg)
    (hQ0 : 0 ≤ Q) (hQ : Q ≤ b ^ (10 * k * m)) :
    (ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q) ^
      ((1 : ℝ) / k) ≤ b ^ ((4 * Cg + 12) * m) := by
  have hb0 : 0 < b := by linarith
  have hk0 : 0 < k := by nlinarith
  have hkm : 0 ≤ k * m := by positivity
  have hE1a : 0 ≤ (m - 1) * k + m * (m - 1) / 2 := by nlinarith
  have hE1b : (m - 1) * k + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hE3a : 0 ≤ k * m + m * (m - 1) / 2 := by nlinarith
  have hE3b : k * m + m * (m - 1) / 2 ≤ 3 / 2 * (k * m) := by nlinarith
  have hP1 : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) ≤ b ^ (3 / 2 * (k * m)) := by
    rw [Real.rpow_neg hka0.le, ← Real.inv_rpow hka0.le]
    calc ka⁻¹ ^ ((m - 1) * k + m * (m - 1) / 2) ≤ b ^ ((m - 1) * k + m * (m - 1) / 2) :=
          Real.rpow_le_rpow (by positivity) hki hE1a
      _ ≤ b ^ (3 / 2 * (k * m)) := Real.rpow_le_rpow_of_exponent_le hb1.le hE1b
  have hP10 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) := Real.rpow_nonneg hka0.le _
  have hP2 : rd ^ (-((m - 1) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hrd1 (by linarith)
  have hP20 : 0 ≤ rd ^ (-((m - 1) / 2)) := Real.rpow_nonneg (by linarith) _
  have hP3 : g ^ (k * m + m * (m - 1) / 2) ≤ b ^ (3 * Cg * (k * m)) := by
    calc g ^ (k * m + m * (m - 1) / 2) ≤ (b ^ (2 * Cg)) ^ (k * m + m * (m - 1) / 2) :=
          Real.rpow_le_rpow hg0 hgg hE3a
      _ = b ^ (2 * Cg * (k * m + m * (m - 1) / 2)) := (Real.rpow_mul hb0.le _ _).symm
      _ ≤ b ^ (3 * Cg * (k * m)) := by
        apply Real.rpow_le_rpow_of_exponent_le hb1.le
        nlinarith
  have hP30 : 0 ≤ g ^ (k * m + m * (m - 1) / 2) := Real.rpow_nonneg hg0 _
  have hX0 : 0 ≤ ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q := by positivity
  have hXb : ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) *
      g ^ (k * m + m * (m - 1) / 2) * Q ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
    calc ka ^ (-((m - 1) * k + m * (m - 1) / 2)) * rd ^ (-((m - 1) / 2)) * g ^ (k * m + m * (m - 1) / 2) * Q
        ≤ b ^ (3 / 2 * (k * m)) * 1 * b ^ (3 * Cg * (k * m)) * b ^ (10 * k * m) := by
          gcongr
      _ = b ^ (3 / 2 * (k * m) + 3 * Cg * (k * m) + 10 * k * m) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0]; ring
      _ ≤ b ^ (k * ((4 * Cg + 12) * m)) := by
          apply Real.rpow_le_rpow_of_exponent_le hb1.le
          nlinarith
  calc _ ≤ (b ^ (k * ((4 * Cg + 12) * m))) ^ ((1 : ℝ) / k) :=
        Real.rpow_le_rpow hX0 hXb (by positivity)
    _ = b ^ ((4 * Cg + 12) * m) := by
        rw [← Real.rpow_mul hb0.le]
        congr 1
        field_simp

/- English proof (translation)
Introduce `hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 u τ`. Use `haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩`. Establish `hH` using `h.1`. Take `⟨_, _, _, _, _, _, hm2L, _, _, _, hlogrd, hkg1, hg1, _, hg2, -⟩` from `hH`. Establish `hL : 1 ≤ large₂.sc.L` using `Formalism.MainNotions.BridgeLemma.one_le_L large₂`.

Establish `hbexp : large₂.sc.b = Real.exp large₂.sc.L` using `rfl`. Establish `hb1 : 1 < large₂.sc.b`. Rewrite using `[hbexp]; exact lt_of_lt_of_le (by linarith) (Real.add_one_le_exp large₂.sc.L)`. Establish `hb0 : 0 < large₂.sc.b` using `by linarith`. Establish `hm : (2 : ℝ) ≤ (D.R.m : ℝ)` using `by have := D.R.two_le_m; exact_mod_cast this`.

Establish `hmk : 40 * (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ)`. Establish `h1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L` using `le_mul_of_one_le_right (by positivity) hL`. Establish `h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L)` using `mul_le_mul_of_nonneg_right h40 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (1 : ℝ) ≤ (D.R.k : ℝ)` using `by nlinarith`.

Establish `hCL : 1 ≤ Cl * large₂.sc.L` using `by nlinarith`. Establish `hVV` using `Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT h.1 hCL τ`. Establish `hlam0 : 0 < vand (lamSH D.R (D.hc τ))` using `Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (Formalism.MainNotions.BridgeLemma.szh_anti h.1 τ (Finset.mem_filter.1 hb).2)`. Establish `hvand : vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ)` using `GlobalTheory.RowVand.vand_lamSH_le D large₂ C' Cl Cg cb Cu cT CT C0 h h40 u τ`. Establish `hexp : Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) = large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m)`.

Rewrite using `[hbexp, ← Real.exp_mul]`. Put the polynomial expressions in normal form. Rewrite `hvand` using `[hexp]`. Establish `hbp : 0 < large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m)` using `Real.rpow_pos_of_pos hb0 _`. Establish `hu0 : 0 < vand (uS D u τ)` using `(pos_iff_pos_of_mul_pos (hlam0.trans_le hvand)).1 hbp`.

Establish `hQ0 : 0 ≤ VV D τ / vand (uS D u τ)` using `by rw [hVV]; positivity`. Establish `hQ : VV D τ / vand (uS D u τ) ≤ large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m)`. Rewrite using `[div_le_iff₀ hu0, hVV]`. Conclude with `hvand`. Establish `hrd1 : 1 ≤ D.host.rdE`.

Establish `h1 : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)|`. Conclude with `Int.one_le_abs (NumberField.discr_ne_zero D.host.E)` after adjusting the coercions. Conclude with `Real.one_le_rpow h1 (by positivity)`. Establish `hrd0 : 0 < D.host.rdE` using `by linarith`. Establish `hrdb : D.host.rdE ≤ large₂.sc.b`.

Establish `hCl0 : 0 < Cl` using `by linarith`. Establish `h1 : Real.log D.host.rdE ≤ large₂.sc.L`. Use `hlogrd.trans ?_` and prove the remaining obligations. Rewrite using `[div_le_iff₀ hCl0]`. Use the polynomial consequences of the given equalities and inequalities.

Combine the equalities or inequalities in the displayed calculation. Establish `hka : D.host.ka = 2 * Real.pi / D.host.rdE` using `by show Real.pi / (D.host.rdE / 2) = 2 * Real.pi / D.host.rdE`. Clear the denominators using the available nonvanishing facts. Establish `hka0 : 0 < D.host.ka` using `by rw [hka]; positivity`. Establish `hki : D.host.ka⁻¹ ≤ large₂.sc.b`.

Rewrite using `[hka, inv_div, div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[Real.pi_gt_three]`. Establish `hg1ge : 1 ≤ (D.host.g 0 : ℝ)` using `le_trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1.le)) hkg1`. Establish `hCg : 0 ≤ Cg`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Use `Real.rpow_lt_one_of_one_lt_of_neg hb1 hc` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgg : gg D ≤ large₂.sc.b ^ (2 * Cg)`. Rewrite using `[show 2 * Cg = Cg + Cg by ring, Real.rpow_add hb0]`.

Unfold `gg`. Conclude with `mul_le_mul hg1 hg2 (by positivity) (by positivity)`. Establish `hgg0 : 0 ≤ gg D` using `by unfold gg; positivity`. Establish `key` using `root_le D.host.ka D.host.rdE (gg D) (VV D τ / vand (uS D u τ)) large₂.sc.b Cg D.R.m D.R.k hb1 hm hmk hka0 hki hrd1 hgg0 hgg hCg hQ0 hQ`. Unfold `Tcrit`.

Rewrite using `[mul_div_assoc]`. Conclude with `key`.
-/
theorem tcrit_le_pow : Formalism.L2.SG.Pf.SzHypFD.DsigHC → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), Ties D → Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → 40 ≤ Cl → ∀ u τ, Tcrit D u τ ≤ large₂.sc.b ^ ((4 * Cg + 12) * (D.R.m : ℝ)) := by
  intro hDs D large₂ C' Cl Cg cb Cu cT CT C0 hT h h40 u τ
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  have hH := h.1
  obtain ⟨_, _, _, _, _, _, hm2L, _, _, _, hlogrd, hkg1, hg1, _, hg2, -⟩ := hH
  have hL : 1 ≤ large₂.sc.L := Formalism.MainNotions.BridgeLemma.one_le_L large₂
  have hbexp : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hb1 : 1 < large₂.sc.b := by
    rw [hbexp]; exact lt_of_lt_of_le (by linarith) (Real.add_one_le_exp large₂.sc.L)
  have hb0 : 0 < large₂.sc.b := by linarith
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by have := D.R.two_le_m; exact_mod_cast this
  have hmk : 40 * (D.R.m : ℝ) ^ 2 ≤ (D.R.k : ℝ) := by
    have h1 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right (by positivity) hL
    have h2 : 40 * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right h40 (by positivity)
    linarith
  have hk1 : (1 : ℝ) ≤ (D.R.k : ℝ) := by nlinarith

  have hCL : 1 ≤ Cl * large₂.sc.L := by nlinarith
  have hVV := Formalism.L2.SG.Pf.SzHypFD.vv_eq_vand hT h.1 hCL τ
  have hlam0 : 0 < vand (lamSH D.R (D.hc τ)) :=
    Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb =>
      sub_pos.2 (Formalism.MainNotions.BridgeLemma.szh_anti h.1 τ (Finset.mem_filter.1 hb).2)
  have hvand : vand (lamSH D.R (D.hc τ)) ≤ Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) * vand (uS D u τ) :=
    GlobalTheory.RowVand.vand_lamSH_le D large₂ C' Cl Cg cb Cu cT CT C0 h h40 u τ
  have hexp : Real.exp (10 * D.R.k * D.R.m * large₂.sc.L) = large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [hbexp, ← Real.exp_mul]; ring_nf
  rw [hexp] at hvand
  have hbp : 0 < large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := Real.rpow_pos_of_pos hb0 _
  have hu0 : 0 < vand (uS D u τ) := (pos_iff_pos_of_mul_pos (hlam0.trans_le hvand)).1 hbp
  have hQ0 : 0 ≤ VV D τ / vand (uS D u τ) := by rw [hVV]; positivity
  have hQ : VV D τ / vand (uS D u τ) ≤ large₂.sc.b ^ (10 * (D.R.k : ℝ) * D.R.m) := by
    rw [div_le_iff₀ hu0, hVV]; exact hvand

  have hrd1 : 1 ≤ D.host.rdE := by
    have h1 : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
    exact Real.one_le_rpow h1 (by positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have hCl0 : 0 < Cl := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := by
      refine hlogrd.trans ?_
      rw [div_le_iff₀ hCl0]; nlinarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log hrd0).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr h1
      _ = large₂.sc.b := hbexp.symm

  have hka : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / (D.host.rdE / 2) = 2 * Real.pi / D.host.rdE
    field_simp
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hki : D.host.ka⁻¹ ≤ large₂.sc.b := by
    rw [hka, inv_div, div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]

  have hg1ge : 1 ≤ (D.host.g 0 : ℝ) :=
    le_trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hk1 hb1.le)) hkg1
  have hCg : 0 ≤ Cg := by
    by_contra hc
    push_neg at hc
    have := Real.rpow_lt_one_of_one_lt_of_neg hb1 hc
    linarith
  have hgg : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add hb0]
    unfold gg
    exact mul_le_mul hg1 hg2 (by positivity) (by positivity)
  have hgg0 : 0 ≤ gg D := by unfold gg; positivity
  have key := root_le D.host.ka D.host.rdE (gg D) (VV D τ / vand (uS D u τ)) large₂.sc.b Cg D.R.m D.R.k
    hb1 hm hmk hka0 hki hrd1 hgg0 hgg hCg hQ0 hQ
  unfold Tcrit
  rw [mul_div_assoc]
  exact key

end GlobalTheory.CritLevelUpper
