import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfPartStatementsWithDelta
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.SharpRestriction.GlobalSchurBounds.TotallyPositiveTraceGeOfNormDiscr
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.UpperSlopeOfMaximalConstant
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IntegralityOfCommutation
import Formalism.LocalToGlobal.GlobalTheory.GL6.CongruenceNoKernelOfHeckeRamified
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveExplicitHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.FamilyPartFiveOfExplicitConstants
import Formalism.LocalToGlobal.GlobalTheory.PlacesMin

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset

/- English proof (translation)
Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop heps).eventually_ge_atTop (9 * max C3 0 * C0))`. Use `⟨x0, fun D sc he hx Δ w hB => ?_⟩` and prove the remaining obligations. Establish `hB'` using `hB`. Take `⟨-, -, -, -, h5, -, -⟩` from `hB'`. Introduce `ρ a b hab`.

Use `le_trans ?_ (parameter_gap_under_section_B D sc C0 Δ w hB ρ a b hab)` and prove the remaining obligations. Use `le_trans (gap_bound_mono D C3 (max C3 0) _ (le_max_left _ _)) ?_` and prove the remaining obligations. Use `le_trans (gap_bound_at_one_third D (max C3 0) (le_max_right _ _)) ?_` and prove the remaining obligations. Establish `hC0` using `exponent_pos_of_rank_le_pow D sc C0 h5`. Establish `hL : 9 * max C3 0 * C0 ≤ sc.L` using `by unfold Scale.L; rw [he]; exact hx0 sc.x hx`.

Establish `hr : (1 : ℝ) ≤ D.R.r`. Use `D.R.k_ge` as an intermediate fact. Use `D.R.r_eq` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.r)` after adjusting the coercions.

Establish `hf : (1 : ℝ) ≤ D.R.f`. Establish `h2 : 2 ≤ D.R.f` using `le_trans D.R.two_le_m D.R.m_le_f`. Conclude with `le_trans one_le_two h2` after adjusting the coercions. Establish `hL0 : 0 ≤ sc.L` using `le_trans (by have := le_max_right C3 0; positivity) hL`. Rewrite using `[le_div_iff₀ hC0]`.

Establish `e1 : (D.R.r : ℝ) ^ 9 ≤ (D.R.r : ℝ) ^ 19` using `pow_le_pow_right₀ hr (by norm_num)`. Establish `e2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5` using `one_le_pow₀ hf`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem gapB_ev (eps C3 C0 : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x →
      ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
        ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D C3 (1 / 3)) := by
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop heps).eventually_ge_atTop (9 * max C3 0 * C0))
  refine ⟨x0, fun D sc he hx Δ w hB => ?_⟩
  have hB' := hB
  obtain ⟨-, -, -, -, h5, -, -⟩ := hB'
  intro ρ a b hab
  refine le_trans ?_ (parameter_gap_under_section_B D sc C0 Δ w hB ρ a b hab)
  refine le_trans (gap_bound_mono D C3 (max C3 0) _ (le_max_left _ _)) ?_
  refine le_trans (gap_bound_at_one_third D (max C3 0) (le_max_right _ _)) ?_
  have hC0 := exponent_pos_of_rank_le_pow D sc C0 h5
  have hL : 9 * max C3 0 * C0 ≤ sc.L := by unfold Scale.L; rw [he]; exact hx0 sc.x hx
  have hr : (1 : ℝ) ≤ D.R.r := by
    have := D.R.k_ge; have := D.R.r_eq; have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h2 : 2 ≤ D.R.f := le_trans D.R.two_le_m D.R.m_le_f
    exact_mod_cast le_trans one_le_two h2
  have hL0 : 0 ≤ sc.L := le_trans (by have := le_max_right C3 0; positivity) hL
  rw [le_div_iff₀ hC0]
  have e1 : (D.R.r : ℝ) ^ 9 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hr (by norm_num)
  have e2 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  calc 9 * max C3 0 * (D.R.r : ℝ) ^ 9 * C0 = (D.R.r : ℝ) ^ 9 * (9 * max C3 0 * C0) := by ring
    _ ≤ (D.R.r : ℝ) ^ 9 * sc.L := mul_le_mul_of_nonneg_left hL (by positivity)
    _ = (D.R.r : ℝ) ^ 9 * 1 * sc.L := by ring
    _ ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * sc.L :=
        mul_le_mul_of_nonneg_right (mul_le_mul e1 e2 zero_le_one (by positivity)) hL0

/- English proof (translation)
Set `_` to `D.host.cmStar`. Establish `h43` using `index_product_formulas_and_ratio D`. Introduce `u`. Establish `hv` using `host_v_pos D`. Establish `hk` using `D.R.k_ge`.

Establish `hm` using `D.R.two_le_m`. Establish `hr : D.R.r = D.R.k + (D.R.m - 1)`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hf : (0 : ℝ) < D.R.f` using `by exact_mod_cast degree_pos_alt D`.

Establish `hkR : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by omega : 0 < D.R.k)`. Establish `hg : ∀ i : Fin 2, (2 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).two_le`. Establish `hfac : ∀ (i : Fin 2) (j : ℕ), 1 ≤ j → 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹`. Introduce `i j hj`. Establish `h1 : (2 : ℝ) ≤ (D.host.g i : ℝ) ^ j` using `le_trans (hg i) (le_self_pow₀ (by linarith [hg i]) (by omega))`.

Establish `h2 : ((D.host.g i : ℝ) ^ j)⁻¹ ≤ 2⁻¹` using `inv_anti₀ (by norm_num) h1`. Evaluate the numerical expressions using `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : (D.R.f : ℝ) * D.R.k * logXuD D u = Real.log (DstarD D / duStarU D u)`. Unfold `logXuD logXu`.

Clear the denominators using the available nonvanishing facts. Use `set R := ∏ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), ratioH D M with hR`. Establish `hmass : massI D D.R.r = massI D D.R.k * R`. Rewrite using `[hr]; exact mass_telescope D h2b hv D.R.k (by omega) (D.R.m - 1)`. Establish `hRpos : 0 < R` using `Finset.prod_pos fun M hM => mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)`.

Use `set Q := ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2)) * ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f with hQ`. Establish `hgg : 0 < (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)` using `mul_pos (by linarith [hg 0]) (by linarith [hg 1])`. Establish `hQ2 : 0 < ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f` using `Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _`. Establish `hQpos : 0 < Q` using `mul_pos (pow_pos hgg _) hQ2`. Establish `h3 : idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) = Q` using `h43.2.2`.

Establish `hidx : idxPi D (D.host.g 0) (D.host.g 1) ≠ 0`. Introduce `h0`. Rewrite `h3` using `[h0, div_zero]`. Conclude with `hQpos.ne h3`. Establish `hmk : massI D D.R.k ≠ 0` using `(massI_pos D D.R.k).ne'`.

Establish `hdim : ∀ ρ, 0 < dimV (uColR D u ρ)` using `fun ρ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`. Establish `hP : 0 < ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))` using `Finset.prod_pos fun ρ _ => div_pos (D.dsig_pos ρ) (hdim ρ)`. Establish `e2 : DstarD D / duStarU D u = R * Q * ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))`. Unfold `DstarD DstarP duStarU duStarP`. Rewrite using `[show volY0 D = massI D D.R.r from h41, hmass, Finset.prod_div_distrib, ← h3]`.

Establish `hd : (∏ ρ, dimV (uColR D u ρ)) ≠ 0` using `(Finset.prod_pos fun ρ _ => hdim ρ).ne'`. Clear the denominators using the available nonvanishing facts. Establish `eR : Real.log R = ∑ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), Real.log (ratioH D M)` using `Real.log_prod fun M hM => (mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)).ne'`. Establish `eQ : Real.log Q = ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) + (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Rewrite using `[hQ, Real.log_mul (pow_pos hgg _).ne' hQ2.ne', Real.log_pow, Real.log_prod]`.

Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_prod, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => Real.log_pow _ _`.

Conclude with `fun j hj => (pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`. Conclude with `fun i _ => (Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`. Establish `eP : Real.log (∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))) = ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (D.R.f : ℝ) * (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Rewrite using `[Real.log_prod fun ρ _ => (div_pos (D.dsig_pos ρ) (hdim ρ)).ne']`. Establish `: ∀ ρ, Real.log (D.dsig ρ / dimV (uColR D u ρ)) = Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`.

Introduce `ρ`. Establish `hvd : 0 < vand (uColR D u ρ)`. Use `hdim ρ` as an intermediate fact. Unfold `dimV at this`. Conclude with `(div_pos_iff_of_pos_right (factorial_product_pos _)).1 this`.

Unfold `dimV`. Rewrite using `[Real.log_div (D.dsig_pos ρ).ne' (div_pos hvd (factorial_product_pos _)).ne', Real.log_div hvd.ne' (factorial_product_pos _).ne', Real.log_div (mul_pos (D.dsig_pos ρ) (factorial_product_pos _)).ne' hvd.ne', Real.log_mul (D.dsig_pos ρ).ne' (factorial_product_pos _).ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun ρ _ => this ρ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Establish `he : ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2)`.

Take `⟨c, hc⟩` from `D.R.m_even`. Establish `h1 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 = c * (2 * D.R.k + D.R.m - 1)`. Establish `: D.R.m * (2 * D.R.k + D.R.m - 1) = 2 * (c * (2 * D.R.k + D.R.m - 1))`. Generalize the expression as in `2 * D.R.k + D.R.m - 1 = X`. Rewrite using `[hc]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hX : ((2 * D.R.k + D.R.m - 1 : ℕ) : ℝ) = 2 * (D.R.k : ℝ) + D.R.m - 1`. Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring`. Establish `hmc : (D.R.m : ℝ) = 2 * c` using `by rw [hc]; push_cast; ring`.

Rewrite using `[h1, Nat.cast_mul, Nat.cast_mul, hX, hmc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Rewrite using `[e1, e2, Real.log_mul (mul_pos hRpos hQpos).ne' hP.ne', Real.log_mul hRpos.ne' hQpos.ne', eR, eQ, eP, log_mass_ratio_telescoping D D.R.k (by omega) (D.R.m - 1), he, hn, Ico_succ_eq_Ioc, ← hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem family_of_global_statements (D : D7) (h2b : MassRatio₂ D) (h41 : BaseVolumeEqualsMass D) : LemmaFiveOneIdentity D := by
  let _ := D.host.cmStar
  have h43 := index_product_formulas_and_ratio D
  intro u
  have hv := host_v_pos D
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + (D.R.m - 1) := by
    have er : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hg : ∀ i : Fin 2, (2 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hfac : ∀ (i : Fin 2) (j : ℕ), 1 ≤ j → 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹ := by
    intro i j hj
    have h1 : (2 : ℝ) ≤ (D.host.g i : ℝ) ^ j :=
      le_trans (hg i) (le_self_pow₀ (by linarith [hg i]) (by omega))
    have h2 : ((D.host.g i : ℝ) ^ j)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) h1
    norm_num at h2 ⊢
    linarith
  have e1 : (D.R.f : ℝ) * D.R.k * logXuD D u = Real.log (DstarD D / duStarU D u) := by
    unfold logXuD logXu
    field_simp
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
  have e2 : DstarD D / duStarU D u = R * Q * ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ)) := by
    unfold DstarD DstarP duStarU duStarP
    rw [show volY0 D = massI D D.R.r from h41, hmass, Finset.prod_div_distrib, ← h3]
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
  rw [e1, e2, Real.log_mul (mul_pos hRpos hQpos).ne' hP.ne', Real.log_mul hRpos.ne' hQpos.ne', eR, eQ, eP,
    log_mass_ratio_telescoping D D.R.k (by omega) (D.R.m - 1), he, hn, Ico_succ_eq_Ioc, ← hr]
  ring

/- English proof (translation)
Set `_` to `D.host.cmStar`. Take `⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩` from `hA`. Establish `hk` using `D.R.k_ge`. Establish `hm` using `D.R.two_le_m`. Establish `hL` using `scale_one_le_L sc`.

Establish `hx0 : 0 < sc.x` using `lt_trans one_pos sc.one_lt_alt`. Establish `hpi : Real.pi ≤ D.host.v` using `hB.1`. Establish `hv0 : 0 < D.host.v` using `lt_of_lt_of_le Real.pi_pos hpi`. Establish `er : D.R.r = D.R.k + (D.R.m - 1)` using `by have := D.R.r_eq; omega`. Establish `hF : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast (degree_pos_alt D)`.

Establish `hM : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast r3`. Establish `hMK : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast r4`. Establish `hK0 : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `he : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3`. Establish `hr : (2 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 2 ≤ D.R.r)`.

Establish `h1 : (D.R.r : ℝ) + 1 ≤ Real.exp (D.R.r : ℝ)` using `Real.add_one_le_exp _`. Rewrite using `[Real.exp_neg, one_div]`. Conclude with `inv_anti₀ (by norm_num) (by linarith)`. Establish `hd : ∀ ρ, (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ`. Introduce `ρ`.

Use `(h3 (1 / 3) he (by norm_num) ρ (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap Δ w hB ρ a b hab))).1` as an intermediate fact. Establish `e : (1 - 1 / 3 : ℝ) = 2 / 3` using `by norm_num`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hSL : -((D.R.f : ℝ) * ((D.R.m : ℝ) - 1)) ≤ ∑ M ∈ Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)`. Establish `e1 : ∀ M ∈ Ioc D.R.k D.R.r, -(D.R.f : ℝ) ≤ Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)`.

Introduce `M hM`. Establish `hM2 : 2 ≤ M` using `by have := (Finset.mem_Ioc.1 hM).1; omega`. Establish `a` using `massIdentity_holds D M hM2`. Establish `b` using `Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2`. Rewrite `b` using `[← zetaR_eq]`.

Establish `c : (D.R.f : ℝ) * Real.log (zetaR M) ≤ D.R.f * 1` using `mul_le_mul_of_nonneg_left b (by linarith)`. Use `(abs_le.1 a).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2` using `Finset.card_nsmul_le_sum _ _ _ e1`. Rewrite `e2` using `[Nat.card_Ioc, nsmul_eq_mul]`.

Establish `e3 : ((D.R.r - D.R.k : ℕ) : ℝ) = (D.R.m : ℝ) - 1`. Rewrite using `[er, Nat.add_sub_cancel_left, Nat.cast_sub (by omega : 1 ≤ D.R.m)]`. Simplify using the standard rewrite rules. Rewrite `e2` using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hSG : -2 ≤ ∑ i : Fin 2, ∑ j ∈ Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Establish `e1 : ∀ i : Fin 2, -1 ≤ ∑ j ∈ Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Introduce `i`. Establish `hg2 : 2 ≤ D.host.g i` using `(D.host.g_prime i).two_le`. Rewrite using `[← Real.log_prod (fun j hj => (one_sub_inv_pow_pos _ hg2 j (by have := (Finset.mem_Ioc.1 hj).1; omega)).ne')]`.

Establish `hs` using `piN_split D.R.k (D.R.m - 1) (D.host.g i)`. Rewrite `hs` using `[← er]`. Establish `hp` using `piN_pos D.R.k (D.host.g i) hg2`. Establish `hq` using `((local_index_formulas_and_bounds D).1 i).2.2.1`. Rewrite `hq` using `[hs, mul_div_cancel_left₀ _ hp.ne']`.

Establish `hg4 : (4 : ℝ) ≤ (D.host.g i : ℝ) ^ (D.R.k + 1)`. Establish `h2 : (2 : ℝ) ≤ D.host.g i` using `by exact_mod_cast hg2`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ((D.host.g i : ℝ) ^ (D.R.k + 1))⁻¹ ≤ (4 : ℝ)⁻¹` using `inv_anti₀ (by norm_num) hg4`. Establish `hhalf : (1 / 2 : ℝ) ≤ ∏ j ∈ Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`.

Evaluate the numerical expressions using `at hinv ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5` using `Real.log_le_log (by norm_num) hhalf`. Establish `l3 : -1 ≤ Real.log (1 / 2 : ℝ)`. Rewrite using `[one_div, Real.log_inv]`.

Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Fin.sum_univ_two]`. Combine the linear relations using `[e1 0, e1 1]`.

Establish `l23 : -1 ≤ Real.log (2 / 3 : ℝ)`. Rewrite using `[Real.le_log_iff_exp_le (by norm_num), Real.exp_neg]`. Establish `h1 : (1 : ℝ) + 1 ≤ Real.exp 1` using `Real.add_one_le_exp _`. Establish `: (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹` using `inv_anti₀ (by norm_num) (by linarith)`. Evaluate the numerical expressions using `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSPW : (D.R.f : ℝ) * (-1 - 5 * D.R.k * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L)) ≤ (∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ))) - (D.R.k : ℝ) * ∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ)`. Establish `e1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), (-1 - 5 * D.R.k * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L)) ≤ Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ)`. Introduce `ρ _`. Establish `a` using `place_dimension_lower_bound D sc C0 Δ w hB r6 hx u ρ (hd ρ)`.

Establish `b : (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) ≤ (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x + 2 * sc.L)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_le_card_nsmul (range D.R.m) _ _ (fun j hj => log_weight_minus_log_b_bound D sc C0 Δ w hB ρ j (Finset.mem_range.1 hj))` as an intermediate fact. Rewrite `this` using `[Finset.card_range, nsmul_eq_mul]`. Then use the resulting hypothesis. Establish `c : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x + 2 * sc.L) ≤ (D.R.k : ℝ) + 2 * D.R.k * sc.L`.

Establish `c0 : (D.R.m : ℝ) / sc.x ≤ 1` using `(div_le_one hx0).2 r5`. Establish `c1 : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x) ≤ D.R.k`. Combine the equalities or inequalities in the displayed calculation. Establish `c2 : (D.R.m : ℝ) * (2 * sc.L) ≤ (D.R.k : ℝ) * (2 * sc.L)` using `mul_le_mul_of_nonneg_right hMK (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e2` using `Finset.card_nsmul_le_sum _ _ _ e1`. Rewrite `e2` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Conclude with `e2`. Establish `hg0 : ∀ i, (0 : ℝ) < (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).pos`.

Establish `eG : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = ∑ i : Fin 2, Real.log (D.host.g i : ℝ)`. Rewrite using `[Fin.sum_univ_two, Real.log_mul (hg0 0).ne' (hg0 1).ne']`. Establish `hid` using `family_of_global_statements D h2b h2v u`. Rewrite `hid` using `[eG]`. Establish `hFne : (D.R.f : ℝ) ≠ 0` using `by linarith`.

Establish `hlo : (D.R.f : ℝ) * D.R.k * lowS D sc w = (D.R.k : ℝ) * (∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ)) + (D.R.f : ℝ) * D.R.k * D.R.m * Real.log (D.host.v / Real.pi) + (D.R.f : ℝ) * D.R.k * D.R.m * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) - 11 * (D.R.f : ℝ) * D.R.k * sc.L`. Establish `e1 : ∀ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) = (1 / (D.R.f : ℝ)) * (∑ ρ, Real.log (w j ρ)) + Real.log (D.host.v / Real.pi)`. Introduce `j hj`. Establish `hj'` using `Finset.mem_range.1 hj`. Establish `e0 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (w j ρ * D.host.v / Real.pi) = Real.log (w j ρ) + Real.log (D.host.v / Real.pi)`.

Introduce `ρ _`. Establish `hw : 0 < w j ρ` using `lt_of_lt_of_le one_pos (weights_ge_one_section_B D sc C0 Δ w hB ρ j hj')`. Rewrite using `[mul_div_assoc, Real.log_mul hw.ne' (div_pos hv0 Real.pi_pos).ne']`. Rewrite using `[Finset.sum_congr rfl e0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts.

Unfold `lowS`. Rewrite using `[Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_comm]`. Clear the denominators using the available nonvanishing facts. Establish `hlv0 : 0 ≤ Real.log (D.host.v / Real.pi)` using `Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)`. Establish `hlv : Real.log (D.host.v / Real.pi) ≤ sc.L`.

Rewrite using `[Real.log_div hv0.ne' Real.pi_pos.ne']`. Establish `: 0 ≤ Real.log Real.pi` using `Real.log_nonneg (by have := Real.pi_gt_three; linarith)`. Combine the linear relations using `[hB.2.1]`. Establish `hG : 0 ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ)` using `Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)`. Conclude with `log_X_lower_arithmetic _ _ _ _ _ _ _ _ _ _ _ _ _ hF hM hMK hL hlv0 hlv r1 hG hSL hSG hSPW hid hlo`.
-/
theorem upper_weight_bound_eventually (D : D7) (sc : Scale) (C0 CY : ℝ)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L)
    (h2b : MassRatio₂ D) (h2v : BaseVolumeEqualsMass D) (h3 : SigmaDegreeTwoSidedBoundOfGap D) (hgap : ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
      ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3)))
    (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hA : DataA D sc C0 CY Δ w) (u : D.what₂.Word) :
    lowS D sc w ≤ logXuD D u := by
  let _ := D.host.cmStar
  obtain ⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩ := hA
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hL := scale_one_le_L sc
  have hx0 : 0 < sc.x := lt_trans one_pos sc.one_lt_alt
  have hpi : Real.pi ≤ D.host.v := hB.1
  have hv0 : 0 < D.host.v := lt_of_lt_of_le Real.pi_pos hpi
  have er : D.R.r = D.R.k + (D.R.m - 1) := by have := D.R.r_eq; omega
  have hF : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (degree_pos_alt D)
  have hM : (44 : ℝ) ≤ D.R.m := by exact_mod_cast r3
  have hMK : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast r4
  have hK0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have he : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
    have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 2 ≤ D.R.r)
    have h1 : (D.R.r : ℝ) + 1 ≤ Real.exp (D.R.r : ℝ) := Real.add_one_le_exp _
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hd : ∀ ρ, (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ := by
    intro ρ
    have := (h3 (1 / 3) he (by norm_num) ρ
      (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap Δ w hB ρ a b hab))).1
    have e : (1 - 1 / 3 : ℝ) = 2 / 3 := by norm_num
    rwa [e] at this

  have hSL : -((D.R.f : ℝ) * ((D.R.m : ℝ) - 1)) ≤
      ∑ M ∈ Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
    have e1 : ∀ M ∈ Ioc D.R.k D.R.r, -(D.R.f : ℝ) ≤ Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
      intro M hM
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ioc.1 hM).1; omega
      have a := massIdentity_holds D M hM2
      have b := Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2
      rw [← zetaR_eq] at b
      have c : (D.R.f : ℝ) * Real.log (zetaR M) ≤ D.R.f * 1 := mul_le_mul_of_nonneg_left b (by linarith)
      have := (abs_le.1 a).1
      linarith
    have e2 := Finset.card_nsmul_le_sum _ _ _ e1
    rw [Nat.card_Ioc, nsmul_eq_mul] at e2
    have e3 : ((D.R.r - D.R.k : ℕ) : ℝ) = (D.R.m : ℝ) - 1 := by
      rw [er, Nat.add_sub_cancel_left, Nat.cast_sub (by omega : 1 ≤ D.R.m)]
      simp
    rw [e3] at e2
    linarith

  have hSG : -2 ≤ ∑ i : Fin 2, ∑ j ∈ Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
    have e1 : ∀ i : Fin 2, -1 ≤ ∑ j ∈ Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
      intro i
      have hg2 : 2 ≤ D.host.g i := (D.host.g_prime i).two_le
      rw [← Real.log_prod (fun j hj => (one_sub_inv_pow_pos _ hg2 j (by have := (Finset.mem_Ioc.1 hj).1; omega)).ne')]
      have hs := piN_split D.R.k (D.R.m - 1) (D.host.g i)
      rw [← er] at hs
      have hp := piN_pos D.R.k (D.host.g i) hg2
      have hq := ((local_index_formulas_and_bounds D).1 i).2.2.1
      rw [hs, mul_div_cancel_left₀ _ hp.ne'] at hq
      have hg4 : (4 : ℝ) ≤ (D.host.g i : ℝ) ^ (D.R.k + 1) := by
        have h2 : (2 : ℝ) ≤ D.host.g i := by exact_mod_cast hg2
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (D.R.k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
          _ ≤ _ := pow_le_pow_left₀ (by norm_num) h2 _
      have hinv : ((D.host.g i : ℝ) ^ (D.R.k + 1))⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hg4
      have hhalf : (1 / 2 : ℝ) ≤ ∏ j ∈ Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
        norm_num at hinv ⊢
        linarith
      have h5 := Real.log_le_log (by norm_num) hhalf
      have l3 : -1 ≤ Real.log (1 / 2 : ℝ) := by
        rw [one_div, Real.log_inv]
        have := Real.log_two_lt_d9
        linarith
      linarith
    rw [Fin.sum_univ_two]
    linarith [e1 0, e1 1]

  have l23 : -1 ≤ Real.log (2 / 3 : ℝ) := by
    rw [Real.le_log_iff_exp_le (by norm_num), Real.exp_neg]
    have h1 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp _
    have : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    norm_num at this ⊢
    linarith
  have hSPW : (D.R.f : ℝ) * (-1 - 5 * D.R.k * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L)) ≤
      (∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ))) -
        (D.R.k : ℝ) * ∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ) := by
    have e1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau),
        (-1 - 5 * D.R.k * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L)) ≤
        Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) -
          (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ) := by
      intro ρ _
      have a := place_dimension_lower_bound D sc C0 Δ w hB r6 hx u ρ (hd ρ)
      have b : (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ) -
          ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) ≤
          (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x + 2 * sc.L) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        have := Finset.sum_le_card_nsmul (range D.R.m) _ _
          (fun j hj => log_weight_minus_log_b_bound D sc C0 Δ w hB ρ j (Finset.mem_range.1 hj))
        rwa [Finset.card_range, nsmul_eq_mul] at this
      have c : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x + 2 * sc.L) ≤ (D.R.k : ℝ) + 2 * D.R.k * sc.L := by
        have c0 : (D.R.m : ℝ) / sc.x ≤ 1 := (div_le_one hx0).2 r5
        have c1 : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x) ≤ D.R.k := by
          calc (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x) = (D.R.k : ℝ) * ((D.R.m : ℝ) / sc.x) := by ring
            _ ≤ (D.R.k : ℝ) * 1 := mul_le_mul_of_nonneg_left c0 hK0
            _ = D.R.k := mul_one _
        have c2 : (D.R.m : ℝ) * (2 * sc.L) ≤ (D.R.k : ℝ) * (2 * sc.L) :=
          mul_le_mul_of_nonneg_right hMK (by linarith)
        linarith
      linarith
    have e2 := Finset.card_nsmul_le_sum _ _ _ e1
    rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at e2
    exact e2

  have hg0 : ∀ i, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).pos
  have eG : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = ∑ i : Fin 2, Real.log (D.host.g i : ℝ) := by
    rw [Fin.sum_univ_two, Real.log_mul (hg0 0).ne' (hg0 1).ne']
  have hid := family_of_global_statements D h2b h2v u
  rw [eG] at hid

  have hFne : (D.R.f : ℝ) ≠ 0 := by linarith
  have hlo : (D.R.f : ℝ) * D.R.k * lowS D sc w =
      (D.R.k : ℝ) * (∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ)) +
        (D.R.f : ℝ) * D.R.k * D.R.m * Real.log (D.host.v / Real.pi) +
        (D.R.f : ℝ) * D.R.k * D.R.m * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) -
        11 * (D.R.f : ℝ) * D.R.k * sc.L := by
    have e1 : ∀ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) =
        (1 / (D.R.f : ℝ)) * (∑ ρ, Real.log (w j ρ)) + Real.log (D.host.v / Real.pi) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have e0 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (w j ρ * D.host.v / Real.pi) =
          Real.log (w j ρ) + Real.log (D.host.v / Real.pi) := by
        intro ρ _
        have hw : 0 < w j ρ := lt_of_lt_of_le one_pos (weights_ge_one_section_B D sc C0 Δ w hB ρ j hj')
        rw [mul_div_assoc, Real.log_mul hw.ne' (div_pos hv0 Real.pi_pos).ne']
      rw [Finset.sum_congr rfl e0, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        D.what₂.card_Tau, nsmul_eq_mul]
      field_simp
    unfold lowS
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum, Finset.sum_comm]
    field_simp
  have hlv0 : 0 ≤ Real.log (D.host.v / Real.pi) :=
    Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)
  have hlv : Real.log (D.host.v / Real.pi) ≤ sc.L := by
    rw [Real.log_div hv0.ne' Real.pi_pos.ne']
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by have := Real.pi_gt_three; linarith)
    linarith [hB.2.1]
  have hG : 0 ≤ ∑ i : Fin 2, Real.log (D.host.g i : ℝ) :=
    Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (D.host.g_prime i).one_lt.le)
  exact log_X_lower_arithmetic _ _ _ _ _ _ _ _ _ _ _ _ _ hF hM hMK hL hlv0 hlv r1 hG hSL hSG hSPW hid hlo

/- English proof (translation)
Establish `h1` using `(isLittleO_log_rpow_atTop heps).bound (show (0 : ℝ) < 1 / 4 by norm_num)`. Establish `h2` using `(tendsto_rpow_atTop heps).eventually_ge_atTop (4 * (Real.log 8 + 1))`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 (h1.and h2)`. Use `⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `hx0 sc.x hx`.

Establish `hL : sc.L = sc.x ^ eps` using `by unfold Scale.L; rw [he]`. Establish `hpos : 0 ≤ sc.x ^ eps` using `Real.rpow_nonneg (lt_trans one_pos sc.one_lt_alt).le _`. Rewrite `a` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos]`. Establish `a'` using `le_trans (le_abs_self _) a`. Conclude with `upper_weight_bound_eventually D sc C0 CY (by rw [hL]; linarith) h2b h2v h3 h4B Δ w hA u`.
-/
theorem ramified_rank_lines_of_free (eps C0 CY : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → MassRatio₂ D → BaseVolumeEqualsMass D → SigmaDegreeTwoSidedBoundOfGap D →
      (∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
        ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3))) → ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ u : D.what₂.Word,
        lowS D sc w ≤ logXuD D u := by
  have h1 := (isLittleO_log_rpow_atTop heps).bound (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 := (tendsto_rpow_atTop heps).eventually_ge_atTop (4 * (Real.log 8 + 1))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩
  obtain ⟨a, b⟩ := hx0 sc.x hx
  have hL : sc.L = sc.x ^ eps := by unfold Scale.L; rw [he]
  have hpos : 0 ≤ sc.x ^ eps := Real.rpow_nonneg (lt_trans one_pos sc.one_lt_alt).le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos] at a
  have a' := le_trans (le_abs_self _) a
  exact upper_weight_bound_eventually D sc C0 CY (by rw [hL]; linarith) h2b h2v h3 h4B Δ w hA u

/- English proof (translation)
Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop heps).eventually_ge_atTop 9)`. Use `⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩` and prove the remaining obligations. Set `_` to `D.host.cmStar`. Establish `hL9 : 9 ≤ sc.L` using `by unfold Scale.L; rw [he]; exact hx0 sc.x hx`. Take `⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩` from `hA`.

Establish `hgap` using `h4B Δ w hB`. Establish `id` using `family_of_global_statements D h2b h2v u`. Establish `hkN` using `D.R.k_ge`. Establish `hmN` using `D.R.two_le_m`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hkN`. Establish `hm44 : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast r3`. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast r4`. Establish `hf : (0 : ℝ) < D.R.f` using `by exact_mod_cast degree_pos_alt D`. Establish `hv` using `host_v_pos D`.

Establish `hpi` using `hB.1`. Establish `hpi3 : (3 : ℝ) < Real.pi` using `Real.pi_gt_three`. Establish `hlv0 : 0 ≤ Real.log (D.host.v / Real.pi)` using `Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)`. Establish `hlv : Real.log (D.host.v / Real.pi) ≤ sc.L`. Use `le_trans (Real.log_le_log (div_pos hv Real.pi_pos) ?_) hB.2.1` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ Real.pi_pos]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2v0 : 0 ≤ Real.log (2 * D.host.v)` using `Real.log_nonneg (by linarith)`. Establish `hcard : ((Finset.Ioc D.R.k D.R.r).card : ℝ) ≤ D.R.m`. Rewrite using `[Nat.card_Ioc]; exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)`.

Establish `hSL : ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) * D.R.m`. Establish `h1 : ∀ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ)`. Introduce `M hM`. Establish `hM2 : 2 ≤ M` using `by have := (Finset.mem_Ioc.1 hM).1; omega`. Establish `a` using `massIdentity_holds D M hM2`.

Establish `b` using `Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2`. Rewrite `b` using `[← zetaR_eq]`. Establish `c` using `mul_le_mul_of_nonneg_left b hf.le`. Combine the linear relations using `[le_abs_self (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))]`. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`.

Rewrite `h2` using `[nsmul_eq_mul]`. Establish `h3` using `mul_le_mul_of_nonneg_right hcard hf.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le`. Establish `elg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)` using `Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])`.

Establish `hlg0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))`. Rewrite using `[elg]`. Combine the linear relations using `[Real.log_nonneg (hg1 0), Real.log_nonneg (hg1 1)]`. Establish `hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 2 * CY * sc.L`. Rewrite using `[elg]`.

Combine the linear relations using `[r2 0, r2 1]`. Establish `hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0`. Use `Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_` and prove the remaining obligations. Establish `hj1 : 1 ≤ j` using `by have := (Finset.mem_Ioc.1 hj).1; omega`. Establish `p` using `one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1`.

Use `Real.log_nonpos p.le ?_` and prove the remaining obligations. Establish `: 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith` as an intermediate fact.

Establish `hrR : (D.R.r : ℝ) ≤ 2 * D.R.k`. Establish `: D.R.r ≤ 2 * D.R.k` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 1 ≤ D.R.r)`. Establish `hlr : Real.log (D.R.r : ℝ) ≤ sc.L` using `le_trans (Real.log_le_log (by linarith) hrR) r6`.

Establish `hlr0 : 0 ≤ Real.log (D.R.r : ℝ)` using `Real.log_nonneg hr1`. Establish `hrlr : (D.R.r : ℝ) * Real.log (D.R.r : ℝ) ≤ 2 * D.R.k * sc.L` using `mul_le_mul hrR hlr hlr0 (by linarith)`. Establish `hrk : ((D.R.r - D.R.k : ℕ) : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)`. Establish `hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ (D.R.f : ℝ) * ((D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L))`. Establish `h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L)`.

Introduce `ρ _`. Establish `hdim` using `dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`. Establish `hV : 0 < vand (uColR D u ρ)`. Unfold `dimV at hdim`. Conclude with `(div_pos_iff_of_pos_right (facProd_pos' _)).1 hdim`.

Establish `e1 : Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) = (Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ))) + (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Unfold `dimV`. Rewrite using `[Real.log_div (mul_pos (D.dsig_pos ρ) (facProd_pos' _)).ne' hV.ne', Real.log_mul (D.dsig_pos ρ).ne' (facProd_pos' _).ne', Real.log_div hV.ne' (facProd_pos' _).ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Establish `a` using `place_dimension_upper_bound D sc C0 Δ w hB h3 hgap u ρ`. Establish `b` using `log_factorial_product_difference D.R.k D.R.r (by omega) (by omega)`. Establish `hkm : 0 ≤ (D.R.k : ℝ) * D.R.m` using `by positivity`. Establish `a' : (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) ≤ (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10)` using `mul_le_mul_of_nonneg_left (by linarith) hkm`. Establish `b' : ((D.R.r - D.R.k : ℕ) : ℝ) * ((D.R.r : ℝ) * Real.log (D.R.r : ℝ)) ≤ D.R.m * (2 * D.R.k * sc.L)` using `mul_le_mul hrk hrlr (mul_nonneg (by linarith) hlr0) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`. Rewrite `h2` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Conclude with `h2`. Conclude with `log_X_upper_arithmetic (D.R.f : ℝ) D.R.k D.R.m sc.L CY _ _ _ _ _ _ _ hf hk5 hm44 hmk hL9 hlv0 hlv h2v0 hSL hlg0 hlg hS5 hS6 id`.
-/
theorem part_five_family_of_mass_volume (eps C0 CY : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → MassRatio₂ D → BaseVolumeEqualsMass D → SigmaDegreeTwoSidedBoundOfGap D →
      (∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
        ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3))) → ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ u : D.what₂.Word,
        logXuD D u ≤ (15 + 3 * CY) * D.R.m * sc.L := by
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop heps).eventually_ge_atTop 9)
  refine ⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩
  let _ := D.host.cmStar
  have hL9 : 9 ≤ sc.L := by unfold Scale.L; rw [he]; exact hx0 sc.x hx
  obtain ⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩ := hA
  have hgap := h4B Δ w hB
  have id := family_of_global_statements D h2b h2v u
  have hkN := D.R.k_ge
  have hmN := D.R.two_le_m
  have er : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hm44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast r3
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast r4
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv := host_v_pos D
  have hpi := hB.1
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three

  have hlv0 : 0 ≤ Real.log (D.host.v / Real.pi) := Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)
  have hlv : Real.log (D.host.v / Real.pi) ≤ sc.L := by
    refine le_trans (Real.log_le_log (div_pos hv Real.pi_pos) ?_) hB.2.1
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have h2v0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg (by linarith)

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
  have elg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
    Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])
  have hlg0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [elg]; linarith [Real.log_nonneg (hg1 0), Real.log_nonneg (hg1 1)]
  have hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 2 * CY * sc.L := by
    rw [elg]; linarith [r2 0, r2 1]
  have hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_
    have hj1 : 1 ≤ j := by have := (Finset.mem_Ioc.1 hj).1; omega
    have p := one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1
    refine Real.log_nonpos p.le ?_
    have : 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹ := by positivity
    linarith

  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hrR : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have : D.R.r ≤ 2 * D.R.k := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hlr : Real.log (D.R.r : ℝ) ≤ sc.L := le_trans (Real.log_le_log (by linarith) hrR) r6
  have hlr0 : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg hr1
  have hrlr : (D.R.r : ℝ) * Real.log (D.R.r : ℝ) ≤ 2 * D.R.k * sc.L :=
    mul_le_mul hrR hlr hlr0 (by linarith)
  have hrk : ((D.R.r - D.R.k : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)
  have hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L)) := by
    have h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau),
        Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
          (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L) := by
      intro ρ _
      have hdim := dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)
      have hV : 0 < vand (uColR D u ρ) := by
        unfold dimV at hdim
        exact (div_pos_iff_of_pos_right (facProd_pos' _)).1 hdim
      have e1 : Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) =
          (Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ))) +
            (Real.log (facProd D.R.r) - Real.log (facProd D.R.k)) := by
        unfold dimV
        rw [Real.log_div (mul_pos (D.dsig_pos ρ) (facProd_pos' _)).ne' hV.ne',
          Real.log_mul (D.dsig_pos ρ).ne' (facProd_pos' _).ne',
          Real.log_div hV.ne' (facProd_pos' _).ne']
        ring
      rw [e1]
      have a := place_dimension_upper_bound D sc C0 Δ w hB h3 hgap u ρ
      have b := log_factorial_product_difference D.R.k D.R.r (by omega) (by omega)
      have hkm : 0 ≤ (D.R.k : ℝ) * D.R.m := by positivity
      have a' : (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) ≤
          (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) :=
        mul_le_mul_of_nonneg_left (by linarith) hkm
      have b' : ((D.R.r - D.R.k : ℕ) : ℝ) * ((D.R.r : ℝ) * Real.log (D.R.r : ℝ)) ≤
          D.R.m * (2 * D.R.k * sc.L) :=
        mul_le_mul hrk hrlr (mul_nonneg (by linarith) hlr0) (by linarith)
      linarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at h2
    exact h2
  exact log_X_upper_arithmetic (D.R.f : ℝ) D.R.k D.R.m sc.L CY _ _ _ _ _ _ _ hf hk5 hm44 hmk hL9 hlv0 hlv h2v0 hSL hlg0 hlg hS5
    hS6 id

/- English proof (translation)
Introduce `C0 CY`. Establish `heps : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.

Take `⟨xa, ha⟩` from `ramified_rank_lines_of_free eps C0 CY heps`. Take `⟨xb, hb⟩` from `part_five_family_of_mass_volume eps C0 CY heps`. Take `⟨xg, hg⟩` from `gapB_ev eps 8192 C0 heps`. Take `⟨x1, h2b⟩` from `h2b`. Take `⟨x2, h2v⟩` from `h2v`.

Take `⟨x3, h3⟩` from `h3`. Use `⟨max (max xa xb) (max xg (max x1 (max x2 x3))), fun x hx hxx i => ?_⟩` and prove the remaining obligations. Establish `ea : xa ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `eb : xb ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `eg : xg ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`.

Establish `e1 : x1 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `e2 : x2 ≤ x` using `le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `e3 : x3 ≤ x` using `le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `hsx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hxx`. Establish `gap` using `hg (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact eg)`.

Establish `h5 : Conclusion5Sharp (Fm.D x i) (Fm.L x i).sc C0 CY` using `fun Δ w hA u => ⟨ha (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact ea) (h2b x e1 hxx i) (h2v x e2 hxx i) (h3 x e3 hxx i) gap Δ w hA u, hb (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact eb) (h2b x e1 hxx i) (h2v x e2 hxx i) (h3 x e3 hxx i) gap Δ w hA u⟩`. Conclude with `part_five_explicit_of_propositions _ _ C0 CY h5 (vandermonde_variation_holds _ _ C0 CY)`.
-/
theorem division_level_prime_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h2b : flipTwoThree.fam0 Fm MassRatio₂) (h2v : flipTwoThree.fam0 Fm BaseVolumeEqualsMass)
    (h3 : flipTwoThree.fam0 Fm SigmaDegreeTwoSidedBoundOfGap) : FamilyVandermondeCountExplicit Fm := by
  intro C0 CY
  have heps : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨xa, ha⟩ := ramified_rank_lines_of_free eps C0 CY heps
  obtain ⟨xb, hb⟩ := part_five_family_of_mass_volume eps C0 CY heps
  obtain ⟨xg, hg⟩ := gapB_ev eps 8192 C0 heps
  obtain ⟨x1, h2b⟩ := h2b
  obtain ⟨x2, h2v⟩ := h2v
  obtain ⟨x3, h3⟩ := h3
  refine ⟨max (max xa xb) (max xg (max x1 (max x2 x3))), fun x hx hxx i => ?_⟩
  have ea : xa ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have eb : xb ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have eg : xg ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e2 : x2 ≤ x :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hx
  have e3 : x3 ≤ x :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) hx
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hxx
  have gap := hg (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact eg)
  have h5 : Conclusion5Sharp (Fm.D x i) (Fm.L x i).sc C0 CY := fun Δ w hA u =>
    ⟨ha (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact ea) (h2b x e1 hxx i) (h2v x e2 hxx i) (h3 x e3 hxx i)
        gap Δ w hA u,
      hb (Fm.D x i) (Fm.L x i).sc (Fm.L_eps x i) (by rw [hsx]; exact eb) (h2b x e1 hxx i) (h2v x e2 hxx i) (h3 x e3 hxx i)
        gap Δ w hA u⟩
  exact part_five_explicit_of_propositions _ _ C0 CY h5 (vandermonde_variation_holds _ _ C0 CY)

end Formalism.MainNotions.StandardLattice

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions

variable (D : D7) (u : D.what₂.Word)

def family_property_and : Prop :=
  ((D.mem u).A.du : ℚ) = (D.duS u : ℚ) * (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) ^ D.R.f ∧
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
  (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax

variable {D u}

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, h.2.1, h.2.2.1⟩`.
-/
theorem ramified_rank_lines_of_full (h : Conclusion2 D u) : family_property_and D u := ⟨h.1, h.2.1, h.2.2.1⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨rank_line W, hμ, muMax_line' hS W⟩`.
-/
theorem division_side_conditions_at_sizeData (hS : HidaSetting D u) (W : FreeT D u) (hμ : SlopeLine D u) : family_property_and D u :=
  ⟨rank_line W, hμ, muMax_line' hS W⟩

end Formalism.MainNotions.product_first_zeroth_parts

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

/- English proof (translation)
Introduce `u`. Take `⟨h1, h2, h3⟩` from `h u`. Take `⟨e1, e2, -⟩` from `D.ram_slopes u`. Establish `hM : LocalQuadraticParts.MuH D u = { D.div.Nu u with L` using `DV.MramL D u } := rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1'` using `congrArg (Rat.cast : ℚ → ℝ) h1`. Move the coercions through the operations in `at h1'`. Rewrite using `[h1']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hM, e1]`.

Conclude with `h2`. Rewrite using `[hM, e2]`. Conclude with `h3`.
-/
theorem RamifiedRankLines (D : D7) (h : ∀ u, product_first_zeroth_parts.family_property_and D u) : LevelPrimeBasicClauses D := by
  intro u
  obtain ⟨h1, h2, h3⟩ := h u
  obtain ⟨e1, e2, -⟩ := D.ram_slopes u
  have hM : LocalQuadraticParts.MuH D u = { D.div.Nu u with L := DV.MramL D u } := rfl
  refine ⟨?_, ?_, ?_⟩
  · have h1' := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h1'
    rw [h1']
    ring
  · rw [hM, e1]
    exact h2
  · rw [hM, e2]
    exact h3

/- English proof (translation)
Introduce `u`. Take `⟨c1, c2, c3⟩` from `RamifiedRankLines D h2 u`. Use `⟨c1, c2, c3, ?_, ?_⟩` and prove the remaining obligations. Introduce `w hw x hx`. Establish `h1 : InLoc (D.plEq w) (L.NuLat u) x` using `⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩`.

Establish `h2 : D.nuIn u x ∈ product_first_zeroth_parts.Nlam D u w` using `(hAtT u w hw x).mp h1`. Establish `h3 : D.nuIn u x ∈ (D.fm u).S 0 w` using `((h5 u w hw).1 h2).1`. Take `⟨s, hs, hsx⟩` from `hLoc u w _ h3`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.one_eq_top, Submodule.top_smul]`.

Use `show (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L`. Rewrite using `[map_smul]`. Conclude with `hsx`. Introduce `F hFT`. Establish `hx0 : 0 < L.sc.x` using `lt_trans zero_lt_one L.sc.one_lt_alt`.

Establish `ha : 0 < L.sc.a` using `mul_pos hx0 (Real.exp_pos _)`. Establish `hb' : 0 < L.sc.b'` using `div_pos ha (Real.exp_pos _)`. Establish `hk : (0 : ℝ) ≤ D.R.k` using `Nat.cast_nonneg _`. Establish `hm : (0 : ℝ) ≤ D.R.m` using `Nat.cast_nonneg _`. Establish `hd : (0 : ℝ) ≤ D.duS u` using `Nat.cast_nonneg _`.

Establish `hTT : (0 : ℝ) ≤ LocalQuadraticParts.nTT D` using `Nat.cast_nonneg _`. Establish `hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ)` using `Real.log_natCast_nonneg _`. Use `set B : ℝ := C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hterm : ∀ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤ (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * (2 * (D.R.m * D.duS u * B))`.

Introduce `w hw`. Establish `hwT : D.what₂.places.resChar w = (D.mem u).A.T` using `hFT w hw`. Take `⟨-, n, hn, hle⟩` from `h5 u w hwT`. Establish `hl` using `hNu.2.2 u w n (by rw [hLen u w hwT, hn])`. Establish `hlw` using `logWeight_nonneg w`.

Establish `he : (0 : ℝ) ≤ D.what₂.places.ramIdx w` using `Nat.cast_nonneg _`. Establish `hSw` using `hS u w hwT`. Establish `h1 : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B)` using `le_trans hle (by gcongr)`. Unfold `SizeData₂.sz`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : ∑ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤ Real.log ((D.mem u).A.T : ℝ) * (2 * (D.R.m * D.duS u * B))`. Use `le_trans (Finset.sum_le_sum hterm) ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Conclude with `mul_le_mul_of_nonneg_right (sum_lwP_e_le D _ (D.mem u).A.T_prime F hFT) (by positivity)`. Establish `hN1 : 1 ≤ D.R.N D.R.m` using `by have := D.R.m_add_three_le_k; unfold Ranks.N; omega`.

Establish `hTf : 2 * D.R.f + 1 < (D.mem u).A.T`. Establish `h` using `(hSet u).1`. Establish `: 2 * D.R.f ≤ 2 * D.R.f * D.R.N D.R.m` using `Nat.le_mul_of_pos_right _ hN1`. Use linear arithmetic over natural numbers and integers. Establish `hTfR : 2 * (D.R.f : ℝ) + 1 < (D.mem u).A.T` using `by exact_mod_cast hTf`.

Establish `hf : (0 : ℝ) ≤ D.R.f` using `Nat.cast_nonneg _`. Establish `hT1 : 0 < ((D.mem u).A.T : ℝ) - 1` using `by linarith`. Establish `hT2 : (2 : ℝ) ≤ (D.mem u).A.T` using `by exact_mod_cast (D.mem u).A.T_prime.two_le`. Establish `hr : (1 / 2 : ℝ) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f`. Establish `hb` using `one_add_mul_le_pow (a := -(1 / (((D.mem u).A.T : ℝ) - 1))) (by`.

Establish `: 1 / (((D.mem u).A.T : ℝ) - 1) ≤ 1`. Rewrite using `[div_le_one hT1]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the proof step `linarith) D.R.f`. Establish `h3 : (D.R.f : ℝ) * (1 / (((D.mem u).A.T : ℝ) - 1)) ≤ 1 / 2`.

Rewrite using `[mul_one_div, div_le_iff₀ hT1]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (1 + -(1 / (((D.mem u).A.T : ℝ) - 1))) = 1 - 1 / (((D.mem u).A.T : ℝ) - 1)` using `by ring`. Rewrite `hb` using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hgoal : (4 * C1) * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') * Real.log ((D.mem u).A.T : ℝ) = 4 * (D.R.m * B * Real.log ((D.mem u).A.T : ℝ))`. Rewrite using `[hB]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hgoal]`. Break down `eq_or_lt_of_le hd with h0 | h0` into its components or cases.

Rewrite using `[c1, ← h0, mul_zero, div_zero]`. Check the signs of the components of the expression. Establish `hdu : 0 < ((D.mem u).A.du : ℝ)` using `by rw [c1]; positivity`. Rewrite using `[div_le_iff₀ hdu]`. Use `le_trans hsum ?_` and prove the remaining obligations.

Rewrite using `[c1]`. Establish `: (D.duS u : ℝ) * (1 / 2) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ)`. Rewrite using `[mul_comm]`. Use `gcongr`. Establish `hP : 0 ≤ D.R.m * B * Real.log ((D.mem u).A.T : ℝ)` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem division_rank_slopes_of_lines (D : D7) (L : SizeData₂ D) (C1 : ℝ) (h2 : ∀ u, product_first_zeroth_parts.family_property_and D u)
    (h5 : ∀ u, CongruenceLatticeLengthBound D u) (hNu : DV.NuDef D L) (hAtT : NuAtTDef D L) (hLoc : LocSpan D)
    (hLen : LenAtT D L) (hS : LevelPrimeSizeBounds D L C1)
    (hSet : ∀ u, product_first_zeroth_parts.HidaSetting D u) (hC1 : 0 ≤ C1) : LocalQuadraticParts.adm26 L (4 * C1) := by
  classical
  intro u
  obtain ⟨c1, c2, c3⟩ := RamifiedRankLines D h2 u
  refine ⟨c1, c2, c3, ?_, ?_⟩
  · intro w hw x hx
    have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
    have h2 : D.nuIn u x ∈ product_first_zeroth_parts.Nlam D u w := (hAtT u w hw x).mp h1
    have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := ((h5 u w hw).1 h2).1
    obtain ⟨s, hs, hsx⟩ := hLoc u w _ h3
    refine ⟨s, hs, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    show (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · intro F hFT
    have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    have ha : 0 < L.sc.a := mul_pos hx0 (Real.exp_pos _)
    have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ D.duS u := Nat.cast_nonneg _
    have hTT : (0 : ℝ) ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
    set B : ℝ := C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * (2 * (D.R.m * D.duS u * B)) := by
      intro w hw
      have hwT : D.what₂.places.resChar w = (D.mem u).A.T := hFT w hw
      obtain ⟨-, n, hn, hle⟩ := h5 u w hwT
      have hl := hNu.2.2 u w n (by rw [hLen u w hwT, hn])
      have hlw := logWeight_nonneg w
      have he : (0 : ℝ) ≤ D.what₂.places.ramIdx w := Nat.cast_nonneg _
      have hSw := hS u w hwT
      have h1 : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B) :=
        le_trans hle (by gcongr)
      unfold SizeData₂.sz
      calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ))
          = 2 * SizeData₂.lwP w * (n : ℝ) := by rw [hl]; ring
        _ ≤ 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B)) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        Real.log ((D.mem u).A.T : ℝ) * (2 * (D.R.m * D.duS u * B)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_lwP_e_le D _ (D.mem u).A.T_prime F hFT) (by positivity)

    have hN1 : 1 ≤ D.R.N D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.N; omega
    have hTf : 2 * D.R.f + 1 < (D.mem u).A.T := by
      have h := (hSet u).1
      have : 2 * D.R.f ≤ 2 * D.R.f * D.R.N D.R.m := Nat.le_mul_of_pos_right _ hN1
      omega
    have hTfR : 2 * (D.R.f : ℝ) + 1 < (D.mem u).A.T := by exact_mod_cast hTf
    have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hT1 : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
    have hT2 : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hr : (1 / 2 : ℝ) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := by
      have hb := one_add_mul_le_pow (a := -(1 / (((D.mem u).A.T : ℝ) - 1))) (by
        have : 1 / (((D.mem u).A.T : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hT1]; linarith
        linarith) D.R.f
      have h3 : (D.R.f : ℝ) * (1 / (((D.mem u).A.T : ℝ) - 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hT1]; linarith
      have h4 : (1 + -(1 / (((D.mem u).A.T : ℝ) - 1))) = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by ring
      rw [h4] at hb
      linarith
    have hgoal : (4 * C1) * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') *
        Real.log ((D.mem u).A.T : ℝ) = 4 * (D.R.m * B * Real.log ((D.mem u).A.T : ℝ)) := by
      rw [hB]; ring
    rw [hgoal]
    rcases eq_or_lt_of_le hd with h0 | h0
    · rw [c1, ← h0, mul_zero, div_zero]; positivity
    · have hdu : 0 < ((D.mem u).A.du : ℝ) := by rw [c1]; positivity
      rw [div_le_iff₀ hdu]
      refine le_trans hsum ?_
      rw [c1]
      have : (D.duS u : ℝ) * (1 / 2) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) := by
        rw [mul_comm]; gcongr
      have hP : 0 ≤ D.R.m * B * Real.log ((D.mem u).A.T : ℝ) := by positivity
      nlinarith

def LvlF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (∀ u, product_first_zeroth_parts.family_property_and (Fm.D x i) u) ∧ ∀ u, CongruenceLatticeLengthBound (Fm.D x i) u

/- English proof (translation)
Establish `hDl : DlSize Fm` using `⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩`. Take `⟨Cn, hN⟩` from `numsL_wtsL_fam Fm hT hDl`. Take `⟨x0, hN⟩` from `hN Cn le_rfl 3 le_rfl`. Take `⟨x1, hT⟩` from `hT`. Take `⟨x2, hE⟩` from `hE`.

Take `⟨x3, h3⟩` from `flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4`. Use `⟨4 * 9, max (max x0 x1) (max (max x2 x3) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `e0 : x ≥ x0` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `e1 : x ≥ x1` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `e2 : x ≥ x2` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx`.

Establish `e3 : x3 ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `e4 : 4 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `e5 : Fm.x1 < x`. Use `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsx : (Fm.L x i).sc.x = x` using `Fm.L_x x i e5`. Establish `hm : 4 ≤ (Fm.D x i).R.m`. Establish `z1` using `(flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1`. Rewrite `z1` using `[hsx]`. Establish `: (4 : ℝ) ≤ (Fm.D x i).R.m` using `le_trans (h3 x e3) z1`.

Conclude with `this` after adjusting the coercions. Conclude with `division_rank_slopes_of_lines _ _ 9 (hE x e2 i).1 (hE x e2 i).2 (Fm.nuDef x e5 i) (Fm.ex x e5 i).lat.atT (locSpan _) (lenAtT _ _ (Fm.ex x e5 i).lat.atT) (fifthLevelSizes_of_weights (by norm_num) (hN x e0 i).1 (hN x e0 i).2) (levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x …`.
-/
theorem lemma_five_one_of_theorem_two {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm) (hE : LvlF Fm) : LocalQuadraticParts.LevelTFamily Fm := by
  have hDl : DlSize Fm :=
    ⟨Fm.x1 + 1, fun x hx i => (Fm.sizes x (by linarith) i).2.2.2.2.2.2.1.2.2.2.2.2.1⟩
  obtain ⟨Cn, hN⟩ := numsL_wtsL_fam Fm hT hDl
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨x1, hT⟩ := hT
  obtain ⟨x2, hE⟩ := hE
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  refine ⟨4 * 9, max (max x0 x1) (max (max x2 x3) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have e1 : x ≥ x1 := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e2 : x ≥ x2 := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have e4 : 4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hm : 4 ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; exact e4)).1
    rw [hsx] at z1
    have : (4 : ℝ) ≤ (Fm.D x i).R.m := le_trans (h3 x e3) z1
    exact_mod_cast this
  exact division_rank_slopes_of_lines _ _ 9 (hE x e2 i).1 (hE x e2 i).2 (Fm.nuDef x e5 i) (Fm.ex x e5 i).lat.atT (locSpan _)
    (lenAtT _ _ (Fm.ex x e5 i).lat.atT) (fifthLevelSizes_of_weights (by norm_num) (hN x e0 i).1 (hN x e0 i).2)
    (levelPrime_setting_of_sizes le_rfl (hN x e0 i).1 (hN x e0 i).2 (hT x e1 i).1 hm) (by norm_num)

end Formalism.MainNotions.J

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

variable {eps : ℝ}

def FamU (Fm : FamP eps) (P : (D : D7) → D.what₂.Word → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    product_first_zeroth_parts.HidaSetting (Fm.D x i) u → P (Fm.D x i) u

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Take `⟨b, hb⟩` from `h'`. Conclude with `⟨max a b, fun x hx hx1 i u hs => ⟨ha x (le_of_max_le_left hx) hx1 i u hs, hb x (le_of_max_le_right hx) hx1 i u hs⟩⟩`.
-/
theorem FamU.and {Fm : FamP eps} {P Q : (D : D7) → D.what₂.Word → Prop} (h : FamU Fm P) (h' : FamU Fm Q) :
    FamU Fm fun D u => P D u ∧ Q D u := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨max a b, fun x hx hx1 i u hs =>
    ⟨ha x (le_of_max_le_left hx) hx1 i u hs, hb x (le_of_max_le_right hx) hx1 i u hs⟩⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Conclude with `⟨a, fun x hx hx1 i u hs => hPQ _ u hs (ha x hx hx1 i u hs)⟩`.
-/
theorem FamU.mono {Fm : FamP eps} {P Q : (D : D7) → D.what₂.Word → Prop} (h : FamU Fm P)
    (hPQ : ∀ (D : D7) (u : D.what₂.Word), product_first_zeroth_parts.HidaSetting D u → P D u → Q D u) : FamU Fm Q := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun x hx hx1 i u hs => hPQ _ u hs (ha x hx hx1 i u hs)⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `tSet`. Take `⟨b, hb⟩` from `hT2`. Take `⟨c, hc⟩` from `hT5`. Use `⟨max (max a b) (max c (Fm.x1 + 1)), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hxa : a ≤ x` using `le_of_max_le_left (le_of_max_le_left hx)`.

Establish `hxb : b ≤ x` using `le_of_max_le_right (le_of_max_le_left hx)`. Establish `hxc : c ≤ x` using `le_of_max_le_left (le_of_max_le_right hx)`. Establish `hx1 : Fm.x1 < x`. Use `le_of_max_le_right (le_of_max_le_right hx)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `⟨fun u => hb x hxb hx1 i u (ha x hxa hx1 i u), fun u => hc x hxc hx1 i u (ha x hxa hx1 i u)⟩`.
-/
theorem lvlF_of (Fm : FamP eps) (tSet : SettingEventually Fm) (hT2 : FamU Fm product_first_zeroth_parts.family_property_and) (hT5 : FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound) :
    J.LvlF Fm := by
  obtain ⟨a, ha⟩ := tSet
  obtain ⟨b, hb⟩ := hT2
  obtain ⟨c, hc⟩ := hT5
  refine ⟨max (max a b) (max c (Fm.x1 + 1)), fun x hx i => ?_⟩
  have hxa : a ≤ x := le_of_max_le_left (le_of_max_le_left hx)
  have hxb : b ≤ x := le_of_max_le_right (le_of_max_le_left hx)
  have hxc : c ≤ x := le_of_max_le_left (le_of_max_le_right hx)
  have hx1 : Fm.x1 < x := by
    have := le_of_max_le_right (le_of_max_le_right hx)
    linarith
  exact ⟨fun u => hb x hxb hx1 i u (ha x hxa hx1 i u), fun u => hc x hxc hx1 i u (ha x hxa hx1 i u)⟩

/- English proof (translation)
Take `⟨a0, hE⟩` from `hE`. Use `⟨max a0 (Fm.x1 + 1), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `e0 : a0 ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `e2 : Fm.x1 < x` using `by have := le_trans (le_max_right a0 (Fm.x1 + 1)) hx; linarith`. Conclude with `nuCommens_of (Fm.nuDef x e2 i) (nuAtT_of (Fm.ex x e2 i).lat.atT (fun u w hw => ((hE x e0 i).2 u w hw).1))`.
-/
theorem nuCommensF_min (Fm : FamP eps) (hE : J.LvlF Fm) : NuCommensF Fm := by
  obtain ⟨a0, hE⟩ := hE
  refine ⟨max a0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have e0 : a0 ≤ x := le_trans (le_max_left _ _) hx
  have e2 : Fm.x1 < x := by have := le_trans (le_max_right a0 (Fm.x1 + 1)) hx; linarith
  exact nuCommens_of (Fm.nuDef x e2 i) (nuAtT_of (Fm.ex x e2 i).lat.atT (fun u w hw => ((hE x e0 i).2 u w hw).1))

/- English proof (translation)
Take `⟨a0, hE⟩` from `hE`. Use `⟨a0, fun x hx i u => ?_⟩` and prove the remaining obligations. Establish `h` using `((hE x hx i).1 u).1`. Conclude with `h` after adjusting the coercions.
-/
theorem ramRankF_min (Fm : FamP eps) (hE : J.LvlF Fm) : RamRankF Fm := by
  obtain ⟨a0, hE⟩ := hE
  refine ⟨a0, fun x hx i u => ?_⟩
  have h := ((hE x hx i).1 u).1
  exact_mod_cast h

/- English proof (translation)
Take `⟨a3, hP⟩` from `cPr`. Take `⟨a0, hN⟩` from `hN`. Take `⟨a1, hE⟩` from `hE`. Take `⟨a2, hS⟩` from `hS`. Use `⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩` and prove the remaining obligations.

Establish `b0 : a0 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `b1 : a1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `b2 : a2 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `b3 : a3 ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `b4 : Fm.x1 < x`.

Use `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSet` using `hS x b2 b4 i u`. Establish `h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du` using `(hN x b0 i).rank u`. Rewrite using `[h1]`.

Establish `hd : 0 < (Fm.D x i).duS u` using `jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u`. Establish `hT' : (2 : ℚ) < (((Fm.D x i).mem u).A.T : ℚ)` using `by exact_mod_cast two_lt_level_prime _ u hSet`. Establish `h2 : (0 : ℚ) < 1 - 1 / ((((Fm.D x i).mem u).A.T : ℚ) - 1)`. Rewrite using `[sub_pos, div_lt_one (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : (0 : ℚ) < (((Fm.D x i).mem u).A.du : ℚ)`. Rewrite using `[((hE x b1 i).1 u).1]`. Establish `: (0 : ℚ) < ((Fm.D x i).duS u : ℚ)` using `by exact_mod_cast hd`. Check the signs of the components of the expression. Conclude with `h3` after adjusting the coercions.
-/
theorem muRank_min (Fm : FamP eps) {C0 : ℝ} (hC0 : 0 < C0) (cPr : ChosenProviso Fm C0) (hN : NuFullF Fm)
    (hE : J.LvlF Fm) (hS : SettingEventually Fm) : J.MuRank Fm := by
  obtain ⟨a3, hP⟩ := cPr
  obtain ⟨a0, hN⟩ := hN
  obtain ⟨a1, hE⟩ := hE
  obtain ⟨a2, hS⟩ := hS
  refine ⟨max (max a0 a1) (max (max a2 a3) (Fm.x1 + 1)), fun x hx i u => ?_⟩
  have b0 : a0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have b1 : a1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have b2 : a2 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b3 : a3 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have b4 : Fm.x1 < x := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  have hSet := hS x b2 b4 i u
  have h1 : ((Fm.D x i).div.Nu u).rank = ((Fm.D x i).mem u).A.du := (hN x b0 i).rank u
  rw [h1]
  have hd : 0 < (Fm.D x i).duS u := jnt_duS_pos_of_proviso (Fm.L x i) C0 hC0 (hP x b3 i) u
  have hT' : (2 : ℚ) < (((Fm.D x i).mem u).A.T : ℚ) := by exact_mod_cast two_lt_level_prime _ u hSet
  have h2 : (0 : ℚ) < 1 - 1 / ((((Fm.D x i).mem u).A.T : ℚ) - 1) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have h3 : (0 : ℚ) < (((Fm.D x i).mem u).A.du : ℚ) := by
    rw [((hE x b1 i).1 u).1]
    have : (0 : ℚ) < ((Fm.D x i).duS u : ℚ) := by exact_mod_cast hd
    positivity
  exact_mod_cast h3

/- English proof (translation)
Introduce `hTu hCh hIn`. Take `⟨C5', c6, hC5, hc6, cT2, cTT, cBad, cW, cQD, cTh, cPr, cCo⟩` from `hCh`. Take `⟨lG, lS, lI, lD, lMu⟩` from `hIn`. Establish `tSet : SettingEventually Fm` using `Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu`. Establish `hE : J.LvlF Fm` using `lvlF_of Fm tSet hT2 hT5`.

Establish `hNC : NuCommensF Fm` using `nuCommensF_min Fm hE`. Establish `hNF : NuFullF Fm` using `nuFullF_of Fm hNC`. Establish `hRank : J.MuRank Fm` using `muRank_min Fm (by linarith) cPr hNF hE tSet`. Establish `hRR : RRRankF Fm` using `rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD`. Establish `hCount : CountF Fm` using `countF_fam Fm h5`.

Establish `hDl` using `dl_of_chosen Fm C5' cQD`. Establish `hSM : SlopesMF Fm` using `flipTwoThree.slopesMF_of_count_fam Fm hZ2 hZ3 hCount hDl tCV`. Establish `hSN : SlopesNF Fm` using `slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_min' Fm (J.lemma_five_one_of_theorem_two Fm hTu hE) hNC hTu hRank lG lMu)`. Establish `hLat : LatF Fm` using `latF Fm lD hNF hRank hRR`. Establish `hFr : FrameF Fm CH` using `frameF_of Fm CH C0 hCH (by linarith) (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_min Fm hE) (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) hLat cPr cCo hNF`.

Conclude with `linkCore Fm Cabs CH 0 C5' c6 hCabs hCH.le le_rfl hc6 hCount hSM hSN hLat (nodesF Fm) hFr (lossF_of_7 Fm (Formalism.L2.GlobalTheoryTheory.Loss7.stLoss7 eps Fm cTT cBad lG) cW) (charF Fm) (size_windows_of_thick_density Fm cT2) cTT cQD cTh lI lD`.
-/
theorem linkGLOBAL7_items (Fm : FamP eps) (Cabs CH C0 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)

    (h5 : StandardLattice.PartFiveFamilyBounds Fm)

    (hZ2 : flipTwoThree.ConclusionF5 Fm) (hZ3 : flipTwoThree.ConclusionF6 Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))

    (hT2 : FamU Fm product_first_zeroth_parts.family_property_and) (hT5 : FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 := by
  intro hTu hCh hIn
  obtain ⟨C5', c6, hC5, hc6, cT2, cTT, cBad, cW, cQD, cTh, cPr, cCo⟩ := hCh
  obtain ⟨lG, lS, lI, lD, lMu⟩ := hIn
  have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
  have hE : J.LvlF Fm := lvlF_of Fm tSet hT2 hT5
  have hNC : NuCommensF Fm := nuCommensF_min Fm hE
  have hNF : NuFullF Fm := nuFullF_of Fm hNC
  have hRank : J.MuRank Fm := muRank_min Fm (by linarith) cPr hNF hE tSet
  have hRR : RRRankF Fm := rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD
  have hCount : CountF Fm := countF_fam Fm h5
  have hDl := dl_of_chosen Fm C5' cQD
  have hSM : SlopesMF Fm := flipTwoThree.slopesMF_of_count_fam Fm hZ2 hZ3 hCount hDl tCV
  have hSN : SlopesNF Fm :=
    slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_min' Fm (J.lemma_five_one_of_theorem_two Fm hTu hE) hNC hTu hRank lG lMu)
  have hLat : LatF Fm := latF Fm lD hNF hRank hRR
  have hFr : FrameF Fm CH := frameF_of Fm CH C0 hCH (by linarith)
    (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_min Fm hE)
      (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) hLat cPr cCo hNF
  exact linkCore Fm Cabs CH 0 C5' c6 hCabs hCH.le le_rfl hc6 hCount hSM hSN hLat (nodesF Fm) hFr
    (lossF_of_7 Fm (Formalism.L2.GlobalTheoryTheory.Loss7.stLoss7 eps Fm cTT cBad lG) cW) (charF Fm) (size_windows_of_thick_density Fm cT2) cTT cQD cTh lI lD

/- English proof (translation)
The claim follows from `linkGLOBAL7_items Fm Cabs CH C0 hCabs hCH hC0 (family_part_five_of_explicit_constants Fm (StandardLattice.division_level_prime_family Fm h2b h2v h3)) (flipTwoThree.familySlopeLower_of_open Fm hZa) (flipTwoThree.familySlopeMax_of_open Fm C5 hZb) tCV ((hW.and hμ).mono fun _ _ hS h …`.
-/
theorem linkGLOBAL7_min (Fm : FamP eps) (Cabs CH C0 C5 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)

    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)

    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))

    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)

    (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_items Fm Cabs CH C0 hCabs hCH hC0 (family_part_five_of_explicit_constants Fm (StandardLattice.division_level_prime_family Fm h2b h2v h3))
    (flipTwoThree.familySlopeLower_of_open Fm hZa) (flipTwoThree.familySlopeMax_of_open Fm C5 hZb) tCV
    ((hW.and hμ).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zeroth_parts.division_side_conditions_at_sizeData hS W hm)
    ((hB.and (hI.and hR)).mono fun _ _ hS h => LocalLatticeBases.congruence_no_kernel_minimal hS h.1 h.2.1 h.2.2)

/- English proof (translation)
Introduce `hTu cPr`. Establish `tSet : SettingEventually Fm` using `Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu`. Establish `hE : J.LvlF Fm` using `lvlF_of Fm tSet hT2 hT5`. Establish `hNF : NuFullF Fm` using `nuFullF_of Fm (nuCommensF_min Fm hE)`. Conclude with `⟨hNF, muRank_min Fm hC0 cPr hNF hE tSet⟩`.
-/
theorem muRank_items (Fm : FamP eps) (C0 : ℝ) (hC0 : 0 < C0) (hT2 : FamU Fm product_first_zeroth_parts.family_property_and) (hT5 : FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound) :
    TuSize Fm → ChosenProviso Fm C0 → NuFullF Fm ∧ J.MuRank Fm := by
  intro hTu cPr
  have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
  have hE : J.LvlF Fm := lvlF_of Fm tSet hT2 hT5
  have hNF : NuFullF Fm := nuFullF_of Fm (nuCommensF_min Fm hE)
  exact ⟨hNF, muRank_min Fm hC0 cPr hNF hE tSet⟩

/- English proof (translation)
Introduce `hCov hTu _ hCh hIn`. Establish `tSet : SettingEventually Fm` using `Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu`. Establish `hE : J.LvlF Fm` using `lvlF_of Fm tSet hT2 hT5`. Establish `hNC : NuCommensF Fm` using `nuCommensF_min Fm hE`. Establish `hNF : NuFullF Fm` using `nuFullF_of Fm hNC`.

Establish `hCount : CountF Fm` using `countF_fam Fm h5`. Choose the witnesses or unpack the hypotheses as in `⟨hRank, hRR, hSM⟩ : J.MuRank Fm ∧ RRRankF Fm ∧ SlopesMF Fm := by`. Take `⟨C5', c6, Cb, -, -, -, -, -, -, cQD, -, cPr, -⟩` from `hCh`. Take `⟨-, lS, lI, lD, -⟩` from `hIn`. Conclude with `⟨muRank_min Fm (by linarith) cPr hNF hE tSet, rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD, flipTwoThree.slopesMF_of_count_fam Fm hZ2 hZ3 hCount (dl_of_chosen Fm C5' cQD) tCV⟩`.

Conclude with `linkGLOBAL Fm Cabs CH C0 eL hCabs hCH.le heL hCount hSM (fun lG lMu => slopesNF_of Fm (Formalism.L2.GlobalTheoryTheory.Places.placesF_min' Fm (J.lemma_five_one_of_theorem_two Fm hTu hE) hNC hTu hRank lG lMu)) hNF hRank hRR (fun cPr cCo lS lI lD => frameF_of Fm CH C0 hCH (by linar …`.
-/
theorem linkGLOBAL_items (Fm : FamP eps) (Cabs CH C0 eL : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (heL : 0 ≤ eL) (hC0 : 3 ≤ C0)
    (h5 : StandardLattice.PartFiveFamilyBounds Fm) (hZ2 : flipTwoThree.ConclusionF5 Fm) (hZ3 : flipTwoThree.ConclusionF6 Fm)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))
    (hT2 : FamU Fm product_first_zeroth_parts.family_property_and) (hT5 : FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound) :
    Fm.CoverAll → TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 Cabs eL := by
  intro hCov hTu _ hCh hIn
  have tSet : SettingEventually Fm := Formalism.L2.GlobalTheoryTheory.Places.settingF_of Fm hTu
  have hE : J.LvlF Fm := lvlF_of Fm tSet hT2 hT5
  have hNC : NuCommensF Fm := nuCommensF_min Fm hE
  have hNF : NuFullF Fm := nuFullF_of Fm hNC
  have hCount : CountF Fm := countF_fam Fm h5
  obtain ⟨hRank, hRR, hSM⟩ : J.MuRank Fm ∧ RRRankF Fm ∧ SlopesMF Fm := by
    obtain ⟨C5', c6, Cb, -, -, -, -, -, -, cQD, -, cPr, -⟩ := hCh
    obtain ⟨-, lS, lI, lD, -⟩ := hIn
    exact ⟨muRank_min Fm (by linarith) cPr hNF hE tSet, rrRankF_of Fm Cabs CH C0 (by linarith) lS cPr lI lD,
      flipTwoThree.slopesMF_of_count_fam Fm hZ2 hZ3 hCount (dl_of_chosen Fm C5' cQD) tCV⟩
  exact linkGLOBAL Fm Cabs CH C0 eL hCabs hCH.le heL hCount hSM
    (fun lG lMu => slopesNF_of Fm
      (Formalism.L2.GlobalTheoryTheory.Places.placesF_min' Fm (J.lemma_five_one_of_theorem_two Fm hTu hE) hNC hTu hRank lG lMu)) hNF hRank hRR
    (fun cPr cCo lS lI lD => frameF_of Fm CH C0 hCH (by linarith)
      (frameRealF_of'' Fm Cabs CH C0 hCH.le lD lI lS cPr hNF hRank hTu (ramRankF_min Fm hE)
        (matKF_of Fm Cabs CH C0 (by linarith) lS cPr lD)) (latF Fm lD hNF hRank hRR) cPr cCo hNF)
    (fun Cb _ cTT cBad lG => losses_family_of_division_side Fm eL (Formalism.L2.GlobalTheoryTheory.Loss.slope_loss_lemma_family Fm Cb eL heL cTT cBad lG hCov) (askIsF Fm))
    (charF Fm) hCov hCh hIn

/- English proof (translation)
Assemble the required witnesses or components as `⟨family_part_five_of_explicit_constants Fm (StandardLattice.division_level_prime_family Fm h2b h2v h3), flipTwoThree.familySlopeLower_of_open Fm hZa, flipTwoThree.familySlopeMax_of_open Fm C5 hZb, (hW.and hμ).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zero …`.
-/
theorem items_of_min (Fm : FamP eps) (C5 : ℝ)
    (h2b : flipTwoThree.fam0 Fm StandardLattice.MassRatio₂) (h2v : flipTwoThree.fam0 Fm StandardLattice.BaseVolumeEqualsMass) (h3 : flipTwoThree.fam0 Fm StandardLattice.SigmaDegreeTwoSidedBoundOfGap)
    (hZa : flipTwoThree.FamilySlopeLowerOpenPart Fm) (hZb : flipTwoThree.FamilySlopeMaxOpenPart Fm C5)
    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine)
    (hI : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero) (hR : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero) (hB : FamU Fm LocalLatticeBases.SecondBranchInclusionLength) :
    StandardLattice.PartFiveFamilyBounds Fm ∧ flipTwoThree.ConclusionF5 Fm ∧ flipTwoThree.ConclusionF6 Fm ∧ FamU Fm product_first_zeroth_parts.family_property_and ∧ FamU Fm LocalLatticeBases.CongruenceLatticeLengthBound :=
  ⟨family_part_five_of_explicit_constants Fm (StandardLattice.division_level_prime_family Fm h2b h2v h3), flipTwoThree.familySlopeLower_of_open Fm hZa, flipTwoThree.familySlopeMax_of_open Fm C5 hZb,
    (hW.and hμ).mono fun _ _ hS h => by obtain ⟨⟨W⟩, hm⟩ := h; exact product_first_zeroth_parts.division_side_conditions_at_sizeData hS W hm,
    (hB.and (hI.and hR)).mono fun _ _ hS h => LocalLatticeBases.congruence_no_kernel_minimal hS h.1 h.2.1 h.2.2⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Take `⟨b, hb⟩` from `h'`. Conclude with `⟨max a b, fun x hx hx1 i => ⟨ha x (le_of_max_le_left hx) hx1 i, hb x (le_of_max_le_right hx) hx1 i⟩⟩`.
-/
theorem low_weight_bound_at {Fm : FamP eps} {P Q : D7 → Prop} (h : flipTwoThree.fam0 Fm P) (h' : flipTwoThree.fam0 Fm Q) :
    flipTwoThree.fam0 Fm fun D => P D ∧ Q D := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  exact ⟨max a b, fun x hx hx1 i =>
    ⟨ha x (le_of_max_le_left hx) hx1 i, hb x (le_of_max_le_right hx) hx1 i⟩⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `h`. Conclude with `⟨a, fun x hx hx1 i => hPQ _ (ha x hx hx1 i)⟩`.
-/
theorem family_property_mono {Fm : FamP eps} {P Q : D7 → Prop} (h : flipTwoThree.fam0 Fm P) (hPQ : ∀ D, P D → Q D) : flipTwoThree.fam0 Fm Q := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun x hx hx1 i => hPQ _ (ha x hx hx1 i)⟩

/- English proof (translation)
The claim follows from `linkGLOBAL7_min Fm Cabs CH C0 4 hCabs hCH hC0 (family_property_mono (low_weight_bound_at h2U h2v0) fun D h => StandardLattice.massRatio_of_definiteVolume D (StandardLattice.volumeMass_of_unfolding D h.1) h.2) (family_property_mono (low_weight_bound_at h2U h2v0) fun D h => Standar …`.
-/
theorem family_of_global_sources (Fm : FamP eps) (Cabs CH C0 : ℝ) (hCabs : 0 ≤ Cabs) (hCH : 0 < CH) (hC0 : 3 ≤ C0)

    (h2U : flipTwoThree.fam0 Fm StandardLattice.VolumeRatio₂) (h2v0 : flipTwoThree.fam0 Fm StandardLattice.DefiniteVolumeEqMass)

    (h3S : flipTwoThree.fam0 Fm StandardLattice.DiscreteSeriesDegreeBoundsOfGap) (hWK : DiscreteSeriesWeylDimension.WeylForK) (hLK : DiscreteSeriesWeylDimension.LowKMultOne) (tDs : flipTwoThree.fam0 Fm StandardLattice.DsigEx)

    (hCS : flipTwoThree.fam0 Fm flipTwoThree.ColSlopeEq) (hSMx : flipTwoThree.fam0 Fm flipTwoThree.SlopeMaxGiven)
    (tCV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u))

    (hW : FamU Fm fun D u => Nonempty (product_first_zeroth_parts.FreeT D u)) (hμ : FamU Fm product_first_zeroth_parts.SlopeLine) (hB : FamU Fm product_first_zeroth_parts.LemB)

    (hI : FamU Fm product_first_zeroth_parts.IntAtT) (hFi : FamU Fm product_first_zeroth_parts.FiSt) (hX : FamU Fm product_first_zeroth_parts.CrossDia) (hU : FamU Fm product_first_zeroth_parts.UnfAll) :
    TuSize Fm → LinkGLOBAL7 Fm Cabs CH C0 Cabs 0 :=
  linkGLOBAL7_min Fm Cabs CH C0 4 hCabs hCH hC0
    (family_property_mono (low_weight_bound_at h2U h2v0) fun D h => StandardLattice.massRatio_of_definiteVolume D (StandardLattice.volumeMass_of_unfolding D h.1) h.2)
    (family_property_mono (low_weight_bound_at h2U h2v0) fun D h => StandardLattice.volumeY0EqualsMass_of_aux2v D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D h.1) h.2))
    (family_property_mono (low_weight_bound_at h3S tDs) fun D h => StandardLattice.theorem_three_sigma_holds D h.1 (DiscreteSeriesWeylDimension.lowest_K_type_count_of_weyl D hWK hLK) h.2)
    (flipTwoThree.familySlopeLowerOpen_of_std flipTwoThree.stdSlopeLow_holds flipTwoThree.hookBound_holds Fm hCS) (flipTwoThree.family_slope_bound_of_max_slope flipTwoThree.hookBound_holds Fm hSMx) tCV hW hμ
    (hI.mono fun _ _ _ h => fun w hw hs v => h 0 (Nat.zero_le _) w hw hs v)
    ((hFi.and (hX.and hU)).mono fun _ _ _ h => fun v φ hφ => by
      have h9 := product_first_zeroth_parts.ram_of h.1 (product_first_zeroth_parts.DiaMul_of h.1 h.2.2) h.2.1 h.2.2 0 (Nat.zero_le _) v φ hφ
      exact ⟨h9.1, h9.2.1, h9.2.2.2.2.2⟩)
    (hB.mono fun _ _ _ h => LocalLatticeBases.secondBranchInclusionLength_of_lemB h)

end Formalism.MainNotions

end
