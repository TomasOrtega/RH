import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdmissibleRanksAllMembers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HypOver
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BinaryHermitianFormRepresentsTotallyPositive
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FdegHCRowsMulSuperfactorialLeVandermondeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CloudAddNodeLeTenBaseSizeStatement
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPrimeUpper

open Formalism.MainNotions.StandardLattice Finset

/- English proof (translation)
Use `haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩`. Establish `h2b` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.standardLattice_aux2b D`. Establish `h43` using `index_product_formulas_and_ratio D`. Establish `hv` using `host_v_pos D`. Establish `hk` using `D.R.k_ge`.

Establish `hm` using `D.R.two_le_m`. Establish `hr : D.R.r = D.R.k + (D.R.m - 1)`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hg : ∀ i : Fin 2, (2 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).two_le`.

Establish `hfac : ∀ (i : Fin 2) (j : ℕ), 1 ≤ j → 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹`. Introduce `i j hj`. Conclude with `one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj`. Use `set R := ∏ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), ratioH D M with hR`. Establish `hmass : massI D D.R.r = massI D D.R.k * R`.

Rewrite using `[hr]; exact mass_telescope D h2b hv D.R.k (by omega) (D.R.m - 1)`. Establish `hRpos : 0 < R` using `Finset.prod_pos fun M hM => mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)`. Use `set Q := ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2)) * ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f with hQ`. Establish `hgg : 0 < (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)` using `mul_pos (by linarith [hg 0]) (by linarith [hg 1])`. Establish `hQ2 : 0 < ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f` using `Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _`.

Establish `hQpos : 0 < Q` using `mul_pos (pow_pos hgg _) hQ2`. Establish `h3 : idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) = Q` using `h43.2.2`. Establish `hidx : idxPi D (D.host.g 0) (D.host.g 1) ≠ 0`. Introduce `h0`. Rewrite `h3` using `[h0, div_zero]`.

Conclude with `hQpos.ne h3`. Establish `hmk : massI D D.R.k ≠ 0` using `(massI_pos D D.R.k).ne'`. Establish `hdim : ∀ ρ, 0 < dimV (uColR D u ρ)` using `fun ρ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`. Establish `hP : 0 < ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))` using `Finset.prod_pos fun ρ _ => div_pos (D.dsig_pos ρ) (hdim ρ)`. Establish `e2 : DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u = R * Q * ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))`.

Unfold `DstarP duStarU duStarP`. Rewrite using `[hmass, Finset.prod_div_distrib, ← h3]`. Establish `hd : (∏ ρ, dimV (uColR D u ρ)) ≠ 0` using `(Finset.prod_pos fun ρ _ => hdim ρ).ne'`. Clear the denominators using the available nonvanishing facts. Establish `eR : Real.log R = ∑ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), Real.log (ratioH D M)` using `Real.log_prod fun M hM => (mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)).ne'`.

Establish `eQ : Real.log Q = ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) + (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Rewrite using `[hQ, Real.log_mul (pow_pos hgg _).ne' hQ2.ne', Real.log_pow, Real.log_prod]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Real.log_prod, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => Real.log_pow _ _`. Conclude with `fun j hj => (pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`. Conclude with `fun i _ => (Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`. Establish `eP : Real.log (∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))) = ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (D.R.f : ℝ) * (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`.

Rewrite using `[Real.log_prod fun ρ _ => (div_pos (D.dsig_pos ρ) (hdim ρ)).ne']`. Establish `: ∀ ρ, Real.log (D.dsig ρ / dimV (uColR D u ρ)) = Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Introduce `ρ`. Establish `hvd : 0 < vand (uColR D u ρ)`. Use `hdim ρ` as an intermediate fact.

Unfold `dimV at this`. Conclude with `(div_pos_iff_of_pos_right (factorial_product_pos _)).1 this`. Unfold `dimV`. Rewrite using `[Real.log_div (D.dsig_pos ρ).ne' (div_pos hvd (factorial_product_pos _)).ne', Real.log_div hvd.ne' (factorial_product_pos _).ne', Real.log_div (mul_pos (D.dsig_pos ρ) (factorial_product_pos _)).ne' hvd.ne', Real.log_mul (D.dsig_pos ρ).ne' (factorial_product_pos _).ne']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl fun ρ _ => this ρ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Establish `he : ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2)`. Take `⟨c, hc⟩` from `D.R.m_even`. Establish `h1 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 = c * (2 * D.R.k + D.R.m - 1)`. Establish `: D.R.m * (2 * D.R.k + D.R.m - 1) = 2 * (c * (2 * D.R.k + D.R.m - 1))`.

Generalize the expression as in `2 * D.R.k + D.R.m - 1 = X`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hX : ((2 * D.R.k + D.R.m - 1 : ℕ) : ℝ) = 2 * (D.R.k : ℝ) + D.R.m - 1`.

Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring`. Establish `hmc : (D.R.m : ℝ) = 2 * c` using `by rw [hc]; push_cast; ring`. Rewrite using `[h1, Nat.cast_mul, Nat.cast_mul, hX, hmc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`.

Rewrite using `[e2, Real.log_mul (mul_pos hRpos hQpos).ne' hP.ne', Real.log_mul hRpos.ne' hQpos.ne', eR, eQ, eP, log_mass_ratio_telescoping D D.R.k (by omega) (D.R.m - 1), he, hn, Ico_succ_eq_Ioc, ← hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_ratio_eq (D : D7) (u : D.what₂.Word) :
    Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) =
      (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
          Real.log (D.host.v / Real.pi)
      - (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) / 2) * Real.log (2 * D.host.v)
      + ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)
      + (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2) *
          Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))
      + (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r,
          Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)
      + ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.BinaryRep.represents_totallyPositive⟩
  have h2b := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.standardLattice_aux2b D
  have h43 := index_product_formulas_and_ratio D
  have hv := host_v_pos D
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + (D.R.m - 1) := by
    have er : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hg : ∀ i : Fin 2, (2 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hfac : ∀ (i : Fin 2) (j : ℕ), 1 ≤ j → 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹ := by
    intro i j hj
    exact one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj
  set R := ∏ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), ratioH D M with hR
  have hmass : massI D D.R.r = massI D D.R.k * R := by
    rw [hr]; exact mass_telescope D h2b hv D.R.k (by omega) (D.R.m - 1)
  have hRpos : 0 < R := Finset.prod_pos fun M hM => mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)
  set Q := ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2)) *
      ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f with hQ
  have hgg : 0 < (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := mul_pos (by linarith [hg 0]) (by linarith [hg 1])
  have hQ2 : 0 < ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f :=
    Finset.prod_pos fun i _ => Finset.prod_pos fun j hj =>
      pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _
  have hQpos : 0 < Q := mul_pos (pow_pos hgg _) hQ2
  have h3 : idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) = Q := h43.2.2
  have hidx : idxPi D (D.host.g 0) (D.host.g 1) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h3
    exact hQpos.ne h3
  have hmk : massI D D.R.k ≠ 0 := (massI_pos D D.R.k).ne'
  have hdim : ∀ ρ, 0 < dimV (uColR D u ρ) := fun ρ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)
  have hP : 0 < ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ)) :=
    Finset.prod_pos fun ρ _ => div_pos (D.dsig_pos ρ) (hdim ρ)
  have e2 : DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u =
      R * Q * ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ)) := by
    unfold DstarP duStarU duStarP
    rw [hmass, Finset.prod_div_distrib, ← h3]
    have hd : (∏ ρ, dimV (uColR D u ρ)) ≠ 0 := (Finset.prod_pos fun ρ _ => hdim ρ).ne'
    field_simp
  have eR : Real.log R = ∑ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), Real.log (ratioH D M) :=
    Real.log_prod fun M hM => (mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)).ne'
  have eQ : Real.log Q = ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) *
        Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) +
      (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
    rw [hQ, Real.log_mul (pow_pos hgg _).ne' hQ2.ne', Real.log_pow, Real.log_prod]
    · congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.log_prod, Finset.mul_sum]
      · exact Finset.sum_congr rfl fun j _ => Real.log_pow _ _
      · exact fun j hj => (pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'
    · exact fun i _ => (Finset.prod_pos fun j hj =>
        pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'
  have eP : Real.log (∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))) =
      ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) -
        (D.R.f : ℝ) * (Real.log (facProd D.R.r) - Real.log (facProd D.R.k)) := by
    rw [Real.log_prod fun ρ _ => (div_pos (D.dsig_pos ρ) (hdim ρ)).ne']
    have : ∀ ρ, Real.log (D.dsig ρ / dimV (uColR D u ρ)) =
        Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) -
          (Real.log (facProd D.R.r) - Real.log (facProd D.R.k)) := by
      intro ρ
      have hvd : 0 < vand (uColR D u ρ) := by
        have := hdim ρ
        unfold dimV at this
        exact (div_pos_iff_of_pos_right (factorial_product_pos _)).1 this
      unfold dimV
      rw [Real.log_div (D.dsig_pos ρ).ne' (div_pos hvd (factorial_product_pos _)).ne',
        Real.log_div hvd.ne' (factorial_product_pos _).ne',
        Real.log_div (mul_pos (D.dsig_pos ρ) (factorial_product_pos _)).ne' hvd.ne',
        Real.log_mul (D.dsig_pos ρ).ne' (factorial_product_pos _).ne']
      ring
    rw [Finset.sum_congr rfl fun ρ _ => this ρ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      D.what₂.card_Tau, nsmul_eq_mul]
  have he : ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) =
      (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2) := by
    obtain ⟨c, hc⟩ := D.R.m_even
    have h1 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 = c * (2 * D.R.k + D.R.m - 1) := by
      have : D.R.m * (2 * D.R.k + D.R.m - 1) = 2 * (c * (2 * D.R.k + D.R.m - 1)) := by
        generalize 2 * D.R.k + D.R.m - 1 = X
        rw [hc]
        ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    have hX : ((2 * D.R.k + D.R.m - 1 : ℕ) : ℝ) = 2 * (D.R.k : ℝ) + D.R.m - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hmc : (D.R.m : ℝ) = 2 * c := by rw [hc]; push_cast; ring
    rw [h1, Nat.cast_mul, Nat.cast_mul, hX, hmc]
    ring
  have hn : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [e2, Real.log_mul (mul_pos hRpos hQpos).ne' hP.ne', Real.log_mul hRpos.ne' hQpos.ne', eR, eQ, eP,
    log_mass_ratio_telescoping D D.R.k (by omega) (D.R.m - 1), he, hn, Ico_succ_eq_Ioc, ← hr]
  ring

end GlobalTheory.LevelPrimeUpper

namespace GlobalTheory.LevelPrimeUpper

open Formalism.MainNotions.StandardLattice Finset

/- English proof (translation)
Establish `hf0 : 0 < f` using `by linarith`. Establish `hk0 : 0 < k` using `by linarith`. Establish `hm0 : 0 ≤ m` using `by linarith`. Establish `hkm0 : 0 ≤ k * m + m ^ 2` using `by positivity`. Establish `hA1 : 0 ≤ (m - 1) * k + m * (m - 1) / 2`.

Establish `: 0 ≤ (m - 1) * k` using `mul_nonneg (by linarith) hk0.le`. Establish `: 0 ≤ m * (m - 1)` using `mul_nonneg hm0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA1' : (m - 1) * k + m * (m - 1) / 2 ≤ k * m + m ^ 2`. Establish `: (m - 1) * k + m * (m - 1) / 2 = k * m + m ^ 2 - (k + m ^ 2 / 2 + m / 2)` using `by ring`.

Establish `: 0 ≤ k + m ^ 2 / 2 + m / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA4 : 0 ≤ m * (2 * k + m - 1) / 2`. Establish `: 0 ≤ m * (2 * k + m - 1)` using `mul_nonneg hm0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA4' : m * (2 * k + m - 1) / 2 ≤ k * m + m ^ 2`. Establish `: m * (2 * k + m - 1) / 2 = k * m + m ^ 2 - (m ^ 2 / 2 + m / 2)` using `by ring`. Establish `: 0 ≤ m ^ 2 / 2 + m / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t1 : ((m - 1) * k + m * (m - 1) / 2) * lv ≤ (k * m + m ^ 2) * LL` using `(mul_le_mul_of_nonneg_left hlv hA1).trans (mul_le_mul_of_nonneg_right hA1' (by linarith))`.

Establish `t2 : 0 ≤ ((m - 1) / 2) * l2v` using `mul_nonneg (by linarith) hl2v`. Establish `t4 : m * (2 * k + m - 1) / 2 * lg ≤ (k * m + m ^ 2) * (18 * LL)`. Break down `le_or_gt 0 lg with h0 | h0` into its components or cases. Conclude with `(mul_le_mul_of_nonneg_left hlg hA4).trans (mul_le_mul_of_nonneg_right hA4' (by linarith))`. Establish `: m * (2 * k + m - 1) / 2 * lg ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hA4 h0.le`.

Establish `: 0 ≤ (k * m + m ^ 2) * (18 * LL)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : k * X ≤ (k * m + m ^ 2) * (20 * LL + 3) + m`. Establish `e : f * (k * X) = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL + f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6` using `by rw [← hX]; ring`. Establish `b1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((k * m + m ^ 2) * LL)`.

Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left t1 hf0.le`. Establish `b2 : 0 ≤ f * ((m - 1) / 2) * l2v` using `by rw [mul_assoc]; exact mul_nonneg hf0.le t2`. Establish `b4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * ((k * m + m ^ 2) * (18 * LL))`. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left t4 hf0.le`. Establish `b5 : f * S5 ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hf0.le hS5`. Establish `e2 : f * ((k * m + m ^ 2) * (20 * LL + 3) + m) = f * ((k * m + m ^ 2) * LL) + f * m + f * ((k * m + m ^ 2) * (18 * LL)) + f * ((k * m + m ^ 2) * (LL + 3))` using `by ring`. Establish `hsum : f * (k * X) ≤ f * ((k * m + m ^ 2) * (20 * LL + 3) + m)`. Rewrite using `[e, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left hsum hf0`. Establish `hm2 : m ^ 2 ≤ 0.01 * (k * m)`. Establish `h1 : m ^ 2 ≤ 0.01 * k` using `by linarith`. Establish `h2 : 0.01 * k ≤ 0.01 * (k * m)`.

Establish `: k ≤ k * m` using `le_mul_of_one_le_right hk0.le (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmk' : m ≤ k` using `by nlinarith`. Establish `h20 : 0 ≤ 20 * LL + 3` using `by linarith`.

Establish `key2 : k * X ≤ k * (1.01 * m * (20 * LL + 3) + 1)`. Establish `h1 : (k * m + m ^ 2) * (20 * LL + 3) ≤ (1.01 * (k * m)) * (20 * LL + 3)` using `mul_le_mul_of_nonneg_right (by linarith) h20`. Establish `e3 : k * (1.01 * m * (20 * LL + 3) + 1) = (1.01 * (k * m)) * (20 * LL + 3) + k` using `by ring`. Rewrite using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hXle : X ≤ 1.01 * m * (20 * LL + 3) + 1` using `le_of_mul_le_mul_left key2 hk0`. Establish `hfk : 1 / (f * k) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Establish `: 1 * 1 ≤ f * k` using `mul_le_mul hf hk zero_le_one hf0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmL : m ≤ m * LL` using `le_mul_of_one_le_right hm0 hL`. Establish `e4 : 1.01 * m * (20 * LL + 3) + 1 = 20.2 * (m * LL) + 3.03 * m + 1` using `by ring`. Rewrite `hXle` using `[e4]`. Establish `e5 : 25 * m * LL = 25 * (m * LL)` using `by ring`. Rewrite using `[e5]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arith (f k m LL lv l2v SL lg S5 S6 X : ℝ) (hf : 1 ≤ f) (hk : 1 ≤ k) (hm : 2 ≤ m)
    (hmk : 100 * m ^ 2 ≤ k) (hL : 1 ≤ LL) (hlv : lv ≤ LL) (hl2v : 0 ≤ l2v) (hSL : SL ≤ f * m)
    (hlg : lg ≤ 18 * LL) (hS5 : S5 ≤ 0) (hS6 : S6 ≤ f * ((k * m + m ^ 2) * (LL + 3)))
    (hX : f * k * X = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
      f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6) :
    X + 1 / (f * k) ≤ 25 * m * LL := by
  have hf0 : 0 < f := by linarith
  have hk0 : 0 < k := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hkm0 : 0 ≤ k * m + m ^ 2 := by positivity
  have hA1 : 0 ≤ (m - 1) * k + m * (m - 1) / 2 := by
    have : 0 ≤ (m - 1) * k := mul_nonneg (by linarith) hk0.le
    have : 0 ≤ m * (m - 1) := mul_nonneg hm0 (by linarith)
    linarith
  have hA1' : (m - 1) * k + m * (m - 1) / 2 ≤ k * m + m ^ 2 := by
    have : (m - 1) * k + m * (m - 1) / 2 = k * m + m ^ 2 - (k + m ^ 2 / 2 + m / 2) := by ring
    have : 0 ≤ k + m ^ 2 / 2 + m / 2 := by positivity
    linarith
  have hA4 : 0 ≤ m * (2 * k + m - 1) / 2 := by
    have : 0 ≤ m * (2 * k + m - 1) := mul_nonneg hm0 (by linarith)
    linarith
  have hA4' : m * (2 * k + m - 1) / 2 ≤ k * m + m ^ 2 := by
    have : m * (2 * k + m - 1) / 2 = k * m + m ^ 2 - (m ^ 2 / 2 + m / 2) := by ring
    have : 0 ≤ m ^ 2 / 2 + m / 2 := by positivity
    linarith
  have t1 : ((m - 1) * k + m * (m - 1) / 2) * lv ≤ (k * m + m ^ 2) * LL :=
    (mul_le_mul_of_nonneg_left hlv hA1).trans (mul_le_mul_of_nonneg_right hA1' (by linarith))
  have t2 : 0 ≤ ((m - 1) / 2) * l2v := mul_nonneg (by linarith) hl2v
  have t4 : m * (2 * k + m - 1) / 2 * lg ≤ (k * m + m ^ 2) * (18 * LL) := by
    rcases le_or_gt 0 lg with h0 | h0
    · exact (mul_le_mul_of_nonneg_left hlg hA4).trans (mul_le_mul_of_nonneg_right hA4' (by linarith))
    · have : m * (2 * k + m - 1) / 2 * lg ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA4 h0.le
      have : 0 ≤ (k * m + m ^ 2) * (18 * LL) := by positivity
      linarith
  have key : k * X ≤ (k * m + m ^ 2) * (20 * LL + 3) + m := by
    have e : f * (k * X) = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
        f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6 := by rw [← hX]; ring
    have b1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((k * m + m ^ 2) * LL) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left t1 hf0.le
    have b2 : 0 ≤ f * ((m - 1) / 2) * l2v := by rw [mul_assoc]; exact mul_nonneg hf0.le t2
    have b4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * ((k * m + m ^ 2) * (18 * LL)) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left t4 hf0.le
    have b5 : f * S5 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf0.le hS5
    have e2 : f * ((k * m + m ^ 2) * (20 * LL + 3) + m) = f * ((k * m + m ^ 2) * LL) + f * m +
        f * ((k * m + m ^ 2) * (18 * LL)) + f * ((k * m + m ^ 2) * (LL + 3)) := by ring
    have hsum : f * (k * X) ≤ f * ((k * m + m ^ 2) * (20 * LL + 3) + m) := by
      rw [e, e2]; linarith
    exact le_of_mul_le_mul_left hsum hf0
  have hm2 : m ^ 2 ≤ 0.01 * (k * m) := by
    have h1 : m ^ 2 ≤ 0.01 * k := by linarith
    have h2 : 0.01 * k ≤ 0.01 * (k * m) := by
      have : k ≤ k * m := le_mul_of_one_le_right hk0.le (by linarith)
      linarith
    linarith
  have hmk' : m ≤ k := by nlinarith
  have h20 : 0 ≤ 20 * LL + 3 := by linarith
  have key2 : k * X ≤ k * (1.01 * m * (20 * LL + 3) + 1) := by
    have h1 : (k * m + m ^ 2) * (20 * LL + 3) ≤ (1.01 * (k * m)) * (20 * LL + 3) :=
      mul_le_mul_of_nonneg_right (by linarith) h20
    have e3 : k * (1.01 * m * (20 * LL + 3) + 1) = (1.01 * (k * m)) * (20 * LL + 3) + k := by ring
    rw [e3]; linarith
  have hXle : X ≤ 1.01 * m * (20 * LL + 3) + 1 := le_of_mul_le_mul_left key2 hk0
  have hfk : 1 / (f * k) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : 1 * 1 ≤ f * k := mul_le_mul hf hk zero_le_one hf0.le
    linarith
  have hmL : m ≤ m * LL := le_mul_of_one_le_right hm0 hL
  have e4 : 1.01 * m * (20 * LL + 3) + 1 = 20.2 * (m * LL) + 3.03 * m + 1 := by ring
  rw [e4] at hXle
  have e5 : 25 * m * LL = 25 * (m * LL) := by ring
  rw [e5]
  linarith

end GlobalTheory.LevelPrimeUpper

namespace GlobalTheory.LevelPrimeUpper

open Formalism.MainNotions.StandardLattice Finset

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hkN` using `D.R.k_ge`. Establish `hmN` using `D.R.two_le_m`. Establish `hfN` using `degree_pos_alt D`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hf : (0 : ℝ) < D.R.f` using `by exact_mod_cast hfN`.

Establish `hf1 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hfN`. Establish `hk1 : (1 : ℝ) ≤ D.R.k` using `by exact_mod_cast (by omega : 1 ≤ D.R.k)`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hmN`. Establish `hL1 : 1 ≤ L.sc.L` using `by linarith`. Establish `hb : L.sc.b = Real.exp L.sc.L` using `rfl`.

Establish `hb1 : 1 ≤ L.sc.b` using `by rw [hb]; exact Real.one_le_exp (by linarith)`. Establish `hmk : 100 * (D.R.m : ℝ) ^ 2 ≤ D.R.k`. Establish `h1` using `N.params.k_ge_m2L`. Establish `h2 : 100 * (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT` using `GlobalTheory.Core.RkFamModel.log_T_lt D u`. Establish `hdu0 : (0 : ℝ) < (D.mem u).A.duStar` using `by exact_mod_cast (D.mem u).A.duStar_pos`. Establish `hDs0 : 0 < (D.mem u).A.Dstar` using `(D.mem u).A.Dstar_pos`. Establish `hXu : Real.log (D.mem u).A.Xu = (1 / ((D.R.f : ℝ) * D.R.k)) * Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u)` using `by show Real.log (((D.mem u).A.Dstar / (D.mem u).A.duStar) ^ ((1 : ℝ) / ((D.R.f : ℝ) * D.R.k))) = _`. Rewrite using `[Real.log_rpow (div_pos hDs0 hdu0), D.Dstar_eq u, hDs, hdu u]`.

Establish `hid` using `log_ratio_eq D u`. Establish `hv0` using `host_v_pos D`. Establish `hrd1 : 1 ≤ D.host.rdE` using `N.sizes.2.2.2.2.2.2.1.2.2.2.2.2.2.1`. Establish `hlv : Real.log (D.host.v / Real.pi) ≤ L.sc.L`. Establish `h1 : Real.log (D.host.v / Real.pi) ≤ Real.log D.host.v` using `Real.log_le_log (div_pos hv0 Real.pi_pos) (div_le_self hv0.le (by linarith [Real.pi_gt_three]))`.

Establish `h2 : Real.log D.host.v ≤ Real.log D.host.rdE` using `Real.log_le_log hv0 (by unfold Formalism.BasicNotions.Host.v; linarith)`. Combine the linear relations using `[Formalism.BasicNotions.log_rdE_le_scL N.params]`. Establish `hl2v : 0 ≤ Real.log (2 * D.host.v)`. Apply `Real.log_nonneg` to reduce the goal to its premises. Unfold `Formalism.BasicNotions.Host.v`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcard : ((Finset.Ioc D.R.k D.R.r).card : ℝ) ≤ D.R.m`. Rewrite using `[Nat.card_Ioc]; exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)`. Establish `hSL : ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) * D.R.m`. Establish `h1 : ∀ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ)`.

Introduce `M hM`. Establish `hM2 : 2 ≤ M` using `by have := (Finset.mem_Ioc.1 hM).1; omega`. Establish `a` using `massIdentity_holds D M hM2`. Establish `b` using `Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2`. Rewrite `b` using `[← zetaR_eq]`.

Establish `c` using `mul_le_mul_of_nonneg_left b hf.le`. Combine the linear relations using `[le_abs_self (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))]`. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`. Rewrite `h2` using `[nsmul_eq_mul]`. Establish `h3` using `mul_le_mul_of_nonneg_right hcard hf.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le`. Establish `hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 18 * L.sc.L`. Rewrite using `[Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])]`. Establish `a0` using `Real.log_le_log (by linarith [hg1 0]) (N.g_le 0)`.

Establish `a1` using `Real.log_le_log (by linarith [hg1 1]) (N.g_le 1)`. Rewrite `a0`, `a1` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0`. Use `Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_` and prove the remaining obligations.

Establish `hj1 : 1 ≤ j` using `by have := (Finset.mem_Ioc.1 hj).1; omega`. Establish `p` using `one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1`. Use `Real.log_nonpos p.le ?_` and prove the remaining obligations. Establish `: 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlog10 : Real.log 10 ≤ 3`. Rewrite using `[Real.log_le_iff_le_exp (by norm_num)]`. Establish `h` using `Real.exp_one_gt_d9`. Establish `e : Real.exp 3 = Real.exp 1 ^ 3` using `by rw [← Real.exp_nat_mul]; norm_num`. Rewrite using `[e]`.

Establish `h27 : (2.7 : ℝ) ≤ Real.exp 1` using `by linarith`. Establish `h3 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3` using `pow_le_pow_left₀ (by norm_num) h27 3`. Evaluate the numerical expressions using `at h3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) ≤ (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2`.

Establish `h1 : (D.R.k - 1) * D.R.m ≤ D.R.k * D.R.m` using `Nat.mul_le_mul_right _ (Nat.sub_le _ _)`. Establish `h2 : D.R.m * (D.R.m - 1) / 2 ≤ D.R.m * D.R.m` using `le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))`. Establish `h3 : (D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 ≤ D.R.k * D.R.m + D.R.m * D.R.m` using `by omega`. Establish `h4 : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) ≤ ((D.R.k * D.R.m + D.R.m * D.R.m : ℕ) : ℝ)`. Conclude with `h3` after adjusting the coercions.

Establish `h5 : ((D.R.k * D.R.m + D.R.m * D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2` using `by push_cast; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : 0 < 10 * L.sc.b` using `by linarith`. Establish `hlB : Real.log (10 * L.sc.b) ≤ L.sc.L + 3`. Rewrite using `[Real.log_mul (by norm_num) (by linarith), hb, Real.log_exp]; linarith`.

Establish `hlB0 : 0 ≤ Real.log (10 * L.sc.b)` using `Real.log_nonneg (by linarith)`. Establish `hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ (D.R.f : ℝ) * (((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3))`. Establish `h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3)`. Introduce `ρ _`. Establish `hnb` using `GlobalTheory.T.cloud_add_node_le_ten_base_size C cD ch D L hv N.sizes hX ρ`.

Establish `hP` using `GlobalTheory.T.fdegHC_rows_mul_superfactorial_le_vandermonde D.R (D.hc ρ) (D.hcW u ρ) (by rw [D.hcW_v]) (by rw [D.hcW_b]) (10 * L.sc.b) (by linarith) hnb.1 hnb.2`. Establish `hdim` using `dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`. Establish `hvd : 0 < vand (uColR D u ρ)`. Unfold `dimV at hdim`. Conclude with `(div_pos_iff_of_pos_right (factorial_product_pos _)).1 hdim`.

Establish `hdsg : D.dsig ρ * facProd D.R.r ≤ (10 * L.sc.b) ^ ((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2) * vand (uColR D u ρ)`. Rewrite using `[hds ρ]`. Conclude with `hP`. Establish `hpos : 0 < D.dsig ρ * facProd D.R.r` using `mul_pos (D.dsig_pos ρ) (factorial_product_pos _)`. Establish `h2 : D.dsig ρ * facProd D.R.r / vand (uColR D u ρ) ≤ (10 * L.sc.b) ^ ((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2)`.

Rewrite using `[div_le_iff₀ hvd]`. Conclude with `hdsg`. Establish `h3` using `Real.log_le_log (div_pos hpos hvd) h2`. Rewrite `h3` using `[Real.log_pow]`. Establish `h4 : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) * Real.log (10 * L.sc.b) ≤ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3)` using `mul_le_mul hE hlB hlB0 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`. Rewrite `h2` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Conclude with `h2`. Establish `hfk : (D.R.f : ℝ) * D.R.k ≠ 0` using `by positivity`.

Establish `key` using `arith (D.R.f : ℝ) D.R.k D.R.m L.sc.L _ _ _ _ _ _ (Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) / ((D.R.f : ℝ) * D.R.k)) hf1 hk1 hm2 hmk hL1 hlv hl2v hSL hlg hS5 hS6 (by rw [← hid]; field_simp)`. Establish `hlogT : Real.log (Formalism.MainNotions.S.Tr D u) ≤ 25 * D.R.m * L.sc.L`. Establish `e : (1 / ((D.R.f : ℝ) * D.R.k)) * Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) = Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) / ((D.R.f : ℝ) * D.R.k)`. Expand and normalize the polynomial expressions, which then agree. Unfold `Formalism.MainNotions.S.Tr`.

Rewrite `hT` using `[hXu, e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTpos : 0 < Formalism.MainNotions.S.Tr D u`. Unfold `Formalism.MainNotions.S.Tr`. Conclude with `(D.mem u).A.T_prime.pos` after adjusting the coercions.

Rewrite using `[hC, hb, ← Real.exp_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tr_le_of (C : Formalism.MainNotions.Inhab.FC) (hC : C.CTu = 25) (cD ch : ℝ) {D : D7} (L : SizeData₂ D) (hv : Val C cD ch L)
    (N : Formalism.MainNotions.Inhab.NumAt C L) (hX : L.sc.x ≤ L.sc.X') (hL100 : 100 ≤ L.sc.L)
    (hDs : D.what₂.Dstar = DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig)
    (hdu : ∀ u, ((D.mem u).A.duStar : ℝ) = duStarU D u)
    (hds : ∀ τ, D.dsig τ = GlobalTheory.Mem.Vol.trueDsig D.R (D.hc τ)) (u : D.what₂.Word) :
    Formalism.MainNotions.S.Tr D u ≤ L.sc.b ^ (C.CTu * (D.R.m : ℝ)) := by
  have hkN := D.R.k_ge
  have hmN := D.R.two_le_m
  have hfN := degree_pos_alt D
  have er : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast hfN
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hfN
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hmN
  have hL1 : 1 ≤ L.sc.L := by linarith
  have hb : L.sc.b = Real.exp L.sc.L := rfl
  have hb1 : 1 ≤ L.sc.b := by rw [hb]; exact Real.one_le_exp (by linarith)
  have hmk : 100 * (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have h1 := N.params.k_ge_m2L
    have h2 : 100 * (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := by nlinarith
    linarith

  have hT := GlobalTheory.Core.RkFamModel.log_T_lt D u
  have hdu0 : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
  have hDs0 : 0 < (D.mem u).A.Dstar := (D.mem u).A.Dstar_pos
  have hXu : Real.log (D.mem u).A.Xu = (1 / ((D.R.f : ℝ) * D.R.k)) *
      Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) := by
    show Real.log (((D.mem u).A.Dstar / (D.mem u).A.duStar) ^ ((1 : ℝ) / ((D.R.f : ℝ) * D.R.k))) = _
    rw [Real.log_rpow (div_pos hDs0 hdu0), D.Dstar_eq u, hDs, hdu u]
  have hid := log_ratio_eq D u

  have hv0 := host_v_pos D
  have hrd1 : 1 ≤ D.host.rdE := N.sizes.2.2.2.2.2.2.1.2.2.2.2.2.2.1
  have hlv : Real.log (D.host.v / Real.pi) ≤ L.sc.L := by
    have h1 : Real.log (D.host.v / Real.pi) ≤ Real.log D.host.v :=
      Real.log_le_log (div_pos hv0 Real.pi_pos) (div_le_self hv0.le (by linarith [Real.pi_gt_three]))
    have h2 : Real.log D.host.v ≤ Real.log D.host.rdE :=
      Real.log_le_log hv0 (by unfold Formalism.BasicNotions.Host.v; linarith)
    linarith [Formalism.BasicNotions.log_rdE_le_scL N.params]
  have hl2v : 0 ≤ Real.log (2 * D.host.v) := by
    apply Real.log_nonneg
    unfold Formalism.BasicNotions.Host.v; linarith

  have hcard : ((Finset.Ioc D.R.k D.R.r).card : ℝ) ≤ D.R.m := by
    rw [Nat.card_Ioc]; exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)
  have hSL : ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) * D.R.m := by
    have h1 : ∀ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) := by
      intro M hM
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ioc.1 hM).1; omega
      have a := massIdentity_holds D M hM2
      have b := Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2
      rw [← zetaR_eq] at b
      have c := mul_le_mul_of_nonneg_left b hf.le
      linarith [le_abs_self (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))]
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [nsmul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_right hcard hf.le
    linarith

  have hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 18 * L.sc.L := by
    rw [Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])]
    have a0 := Real.log_le_log (by linarith [hg1 0]) (N.g_le 0)
    have a1 := Real.log_le_log (by linarith [hg1 1]) (N.g_le 1)
    rw [Real.log_exp] at a0 a1
    linarith
  have hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_
    have hj1 : 1 ≤ j := by have := (Finset.mem_Ioc.1 hj).1; omega
    have p := one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1
    refine Real.log_nonpos p.le ?_
    have : 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹ := by positivity
    linarith

  have hlog10 : Real.log 10 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
    have h3 : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h27 3
    norm_num at h3 ⊢
    linarith
  have hE : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) ≤ (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2 := by
    have h1 : (D.R.k - 1) * D.R.m ≤ D.R.k * D.R.m := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have h2 : D.R.m * (D.R.m - 1) / 2 ≤ D.R.m * D.R.m :=
      le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h3 : (D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 ≤ D.R.k * D.R.m + D.R.m * D.R.m := by omega
    have h4 : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) ≤ ((D.R.k * D.R.m + D.R.m * D.R.m : ℕ) : ℝ) := by
      exact_mod_cast h3
    have h5 : ((D.R.k * D.R.m + D.R.m * D.R.m : ℕ) : ℝ) = (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2 := by
      push_cast; ring
    linarith
  have hB0 : 0 < 10 * L.sc.b := by linarith
  have hlB : Real.log (10 * L.sc.b) ≤ L.sc.L + 3 := by
    rw [Real.log_mul (by norm_num) (by linarith), hb, Real.log_exp]; linarith
  have hlB0 : 0 ≤ Real.log (10 * L.sc.b) := Real.log_nonneg (by linarith)
  have hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
      (D.R.f : ℝ) * (((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3)) := by
    have h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
        ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3) := by
      intro ρ _
      have hnb := GlobalTheory.T.cloud_add_node_le_ten_base_size C cD ch D L hv N.sizes hX ρ
      have hP := GlobalTheory.T.fdegHC_rows_mul_superfactorial_le_vandermonde D.R (D.hc ρ) (D.hcW u ρ) (by rw [D.hcW_v]) (by rw [D.hcW_b]) (10 * L.sc.b)
        (by linarith) hnb.1 hnb.2
      have hdim := dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)
      have hvd : 0 < vand (uColR D u ρ) := by
        unfold dimV at hdim
        exact (div_pos_iff_of_pos_right (factorial_product_pos _)).1 hdim
      have hdsg : D.dsig ρ * facProd D.R.r ≤
          (10 * L.sc.b) ^ ((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2) * vand (uColR D u ρ) := by
        rw [hds ρ]; exact hP
      have hpos : 0 < D.dsig ρ * facProd D.R.r := mul_pos (D.dsig_pos ρ) (factorial_product_pos _)
      have h2 : D.dsig ρ * facProd D.R.r / vand (uColR D u ρ) ≤
          (10 * L.sc.b) ^ ((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2) := by
        rw [div_le_iff₀ hvd]; exact hdsg
      have h3 := Real.log_le_log (div_pos hpos hvd) h2
      rw [Real.log_pow] at h3
      have h4 : (((D.R.k - 1) * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) * Real.log (10 * L.sc.b) ≤
          ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) ^ 2) * (L.sc.L + 3) :=
        mul_le_mul hE hlB hlB0 (by positivity)
      linarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at h2
    exact h2

  have hfk : (D.R.f : ℝ) * D.R.k ≠ 0 := by positivity
  have key := arith (D.R.f : ℝ) D.R.k D.R.m L.sc.L _ _ _ _ _ _
    (Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) / ((D.R.f : ℝ) * D.R.k))
    hf1 hk1 hm2 hmk hL1 hlv hl2v hSL hlg hS5 hS6 (by rw [← hid]; field_simp)
  have hlogT : Real.log (Formalism.MainNotions.S.Tr D u) ≤ 25 * D.R.m * L.sc.L := by
    have e : (1 / ((D.R.f : ℝ) * D.R.k)) *
        Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) =
        Real.log (DstarP D (D.host.g 0) (D.host.g 1) (massI D D.R.r) D.dsig / duStarU D u) / ((D.R.f : ℝ) * D.R.k) := by
      ring
    unfold Formalism.MainNotions.S.Tr
    rw [hXu, e] at hT
    linarith
  have hTpos : 0 < Formalism.MainNotions.S.Tr D u := by
    unfold Formalism.MainNotions.S.Tr; exact_mod_cast (D.mem u).A.T_prime.pos
  rw [hC, hb, ← Real.exp_mul]
  calc Formalism.MainNotions.S.Tr D u = Real.exp (Real.log (Formalism.MainNotions.S.Tr D u)) := (Real.exp_log hTpos).symm
    _ ≤ Real.exp (L.sc.L * (25 * (D.R.m : ℝ))) := Real.exp_le_exp.2 (by linarith)

end GlobalTheory.LevelPrimeUpper

namespace GlobalTheory.LevelPrimeUpper

open Formalism.MainNotions.StandardLattice Finset

/- English proof (translation)
Establish `h3 : 0 < eps / 3` using `by positivity`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop h3).bound one_pos)`. Use `⟨max (max x0 1) ((100 : ℝ) ^ (1 / eps)), fun x hx => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : (100 : ℝ) ^ (1 / eps) ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `h2` using `Real.rpow_le_rpow (by positivity) h1 he.le`.

Rewrite `h2` using `[← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one]`. Then use the resulting hypothesis. Establish `hx1 : 1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hb` using `hx0 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)`. Rewrite `hb` using `[Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eventually_rpow_ge_hundred_and_le_exp (eps : ℝ) (he : 0 < eps) : ∃ x2 : ℝ, ∀ x, x2 ≤ x → 100 ≤ x ^ eps ∧ x ≤ Real.exp (x ^ (eps / 3)) := by
  have h3 : 0 < eps / 3 := by positivity
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop h3).bound one_pos)
  refine ⟨max (max x0 1) ((100 : ℝ) ^ (1 / eps)), fun x hx => ⟨?_, ?_⟩⟩
  · have h1 : (100 : ℝ) ^ (1 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have h2 := Real.rpow_le_rpow (by positivity) h1 he.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel he.ne', Real.rpow_one] at h2
  · have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hb := hx0 x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hb
    calc x = Real.exp (Real.log x) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (x ^ (eps / 3)) := Real.exp_le_exp.2 hb

/- English proof (translation)
Use `⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩` and prove the remaining obligations. Take `⟨c1, hN⟩` from `szRow_numAt eps he he52 C hStd`. Use `⟨c1, fun cD hcD => ?_⟩` and prove the remaining obligations. Take `⟨c2, hN⟩` from `hN cD hcD`. Use `⟨c2, fun ch hch _ => ?_⟩` and prove the remaining obligations.

Take `⟨x1, hN⟩` from `hN ch hch`. Take `⟨x2, hx2⟩` from `eventually_rpow_ge_hundred_and_le_exp eps he`. Use `⟨max x1 x2, fun K hK hx β u => ?_⟩` and prove the remaining obligations. Take `⟨hC, hcD', hch', heps, -⟩` from `hK`. Establish `hsc : β.O.L.sc = K.s` using `β.sc`.

Establish `hx' : max x1 x2 ≤ β.O.L.sc.x` using `by rw [hsc]; exact hx`. Establish `hse : β.O.L.sc.eps = eps` using `by rw [hsc]; exact heps`. Establish `hv : Val C cD ch β.O.L`. Rewrite using `[show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]`. Conclude with `β.p.pt_val β.val`.

Take `⟨⟨N⟩, -, -⟩` from `hN _ _ hse (le_trans (le_max_left _ _) hx') hv (GlobalTheory.Plug.hostArith_bpt β)`. Establish `hL` using `hx2 β.O.L.sc.x (le_trans (le_max_right _ _) hx')`. Establish `hL100 : 100 ≤ β.O.L.sc.L` using `by show 100 ≤ β.O.L.sc.x ^ β.O.L.sc.eps`. Rewrite using `[hse]`. Conclude with `hL.1`.

Establish `hX : β.O.L.sc.x ≤ β.O.L.sc.X'` using `by show β.O.L.sc.x ≤ Real.exp (β.O.L.sc.x ^ (β.O.L.sc.eps / 3))`. Rewrite using `[hse]`. Conclude with `hL.2`. Establish `hCT : C.CTu = 25` using `hStd.2.2.2.2.2.2.2.2.2.2.1`. Conclude with `tr_le_of C hCT cD ch β.O.L hv N hX hL100 (GlobalTheory.MemberRanks.dstar_mass K β.X β.c.isOver β.c.dsig_eq) β.O.ex.duStar_def (fun τ => β.c.dsig_eq τ) u`.
-/
theorem eventually_trace_le : EvP fun κ K => ∀ β : BPt K, ∀ u : β.D.what₂.Word,
    Formalism.MainNotions.S.Tr β.D u ≤ β.O.L.sc.b ^ (κ.C.CTu * (β.D.R.m : ℝ)) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ he52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hStd _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps he he52 C hStd
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch hch
  obtain ⟨x2, hx2⟩ := eventually_rpow_ge_hundred_and_le_exp eps he
  refine ⟨max x1 x2, fun K hK hx β u => ?_⟩
  obtain ⟨hC, hcD', hch', heps, -⟩ := hK
  have hsc : β.O.L.sc = K.s := β.sc
  have hx' : max x1 x2 ≤ β.O.L.sc.x := by rw [hsc]; exact hx
  have hse : β.O.L.sc.eps = eps := by rw [hsc]; exact heps
  have hv : Val C cD ch β.O.L := by
    rw [show C = K.C from hC.symm, show cD = K.cD from hcD'.symm, show ch = K.ch from hch'.symm]
    exact β.p.pt_val β.val
  obtain ⟨⟨N⟩, -, -⟩ := hN _ _ hse (le_trans (le_max_left _ _) hx') hv (GlobalTheory.Plug.hostArith_bpt β)
  have hL := hx2 β.O.L.sc.x (le_trans (le_max_right _ _) hx')
  have hL100 : 100 ≤ β.O.L.sc.L := by
    show 100 ≤ β.O.L.sc.x ^ β.O.L.sc.eps
    rw [hse]; exact hL.1
  have hX : β.O.L.sc.x ≤ β.O.L.sc.X' := by
    show β.O.L.sc.x ≤ Real.exp (β.O.L.sc.x ^ (β.O.L.sc.eps / 3))
    rw [hse]; exact hL.2
  have hCT : C.CTu = 25 := hStd.2.2.2.2.2.2.2.2.2.2.1
  exact tr_le_of C hCT cD ch β.O.L hv N hX hL100 (GlobalTheory.MemberRanks.dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    β.O.ex.duStar_def (fun τ => β.c.dsig_eq τ) u

/- English proof (translation)
Introduce `hL p`. Conclude with `eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β`.
-/
theorem levelPrime_le_at_points : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p)
      (fun κ D O _ _ => ∀ u : D.what₂.Word, Formalism.MainNotions.S.Tr D u ≤ O.L.sc.b ^ (κ.C.CTu * (D.R.m : ℝ))) := by
  intro hL p
  exact eventually_trace_le.mono fun _ _ _ H β _ _ _ _ => H β

end GlobalTheory.LevelPrimeUpper
