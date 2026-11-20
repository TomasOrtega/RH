import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PartFiveExplicitOfPropositions

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Finset.mem_Ico, Finset.mem_Ioc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Ico_succ_eq_Ioc (a b : ℕ) : Ico (a + 1) (b + 1) = Ioc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Ioc]
  omega

/- English proof (translation)
Establish `hv` using `host_v_pos D`. Establish `hL` using `lVal_pos D M hM`. Unfold `ratioH`. Establish `hfac : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Establish `hvp : 0 < D.host.v / Real.pi` using `div_pos hv Real.pi_pos`.

Establish `h2v : (0 : ℝ) < 2 * D.host.v` using `by linarith`. Establish `hA : 0 < (((M - 1).factorial : ℕ) : ℝ) * (D.host.v / Real.pi) ^ M` using `mul_pos hfac (pow_pos hvp M)`. Establish `hS : 0 < Real.sqrt ((2 * D.host.v) ^ D.R.f)` using `Real.sqrt_pos.mpr (pow_pos h2v _)`. Rewrite using `[Real.log_mul (div_pos (pow_pos hA _) hS).ne' hL.ne', Real.log_div (pow_pos hA _).ne' hS.ne', Real.log_pow, Real.log_mul hfac.ne' (pow_pos hvp M).ne', Real.log_pow, Real.log_sqrt (pow_pos h2v _).le, Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_mass_ratio_formula (D : D7) (M : ℕ) (hM : 2 ≤ M) :
    letI := D.host.cmStar
    Real.log (ratioH D M) = (D.R.f : ℝ) * (Real.log (((M - 1).factorial : ℕ) : ℝ) +
      M * Real.log (D.host.v / Real.pi)) - (D.R.f : ℝ) / 2 * Real.log (2 * D.host.v) +
      Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
  have hv := host_v_pos D
  have hL := lVal_pos D M hM
  unfold ratioH
  have hfac : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hvp : 0 < D.host.v / Real.pi := div_pos hv Real.pi_pos
  have h2v : (0 : ℝ) < 2 * D.host.v := by linarith
  have hA : 0 < (((M - 1).factorial : ℕ) : ℝ) * (D.host.v / Real.pi) ^ M := mul_pos hfac (pow_pos hvp M)
  have hS : 0 < Real.sqrt ((2 * D.host.v) ^ D.R.f) := Real.sqrt_pos.mpr (pow_pos h2v _)
  rw [Real.log_mul (div_pos (pow_pos hA _) hS).ne' hL.ne', Real.log_div (pow_pos hA _).ne' hS.ne',
    Real.log_pow, Real.log_mul hfac.ne' (pow_pos hvp M).ne', Real.log_pow,
    Real.log_sqrt (pow_pos h2v _).le, Real.log_pow]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e1 : k + (n + 1) + 1 = (k + n + 1) + 1` using `by ring`. Establish `e2 : k + (n + 1) = (k + n) + 1` using `by ring`.

Rewrite using `[e1, Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega), Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega), ih, log_mass_ratio_formula D (k + n + 1) (by omega), e2]`. Establish `hf : facProd (k + n + 1) = facProd (k + n) * (((k + n).factorial : ℕ) : ℝ)`. Unfold `facProd`. Rewrite using `[Finset.prod_range_succ]`. Establish `hpos : 0 < facProd (k + n)`.

Unfold `facProd`. Conclude with `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i`. Establish `hfpos : (0 : ℝ) < (((k + n).factorial : ℕ) : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Rewrite using `[hf, Real.log_mul hpos.ne' hfpos.ne']`. Simplify using `only [Nat.add_sub_cancel]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_mass_ratio_telescoping (D : D7) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    letI := D.host.cmStar
    ∑ M ∈ Ico (k + 1) (k + n + 1), Real.log (ratioH D M) =
      (D.R.f : ℝ) * (Real.log (facProd (k + n)) - Real.log (facProd k)) +
      (D.R.f : ℝ) * ((n : ℝ) * k + (n : ℝ) * ((n : ℝ) + 1) / 2) * Real.log (D.host.v / Real.pi) -
      (D.R.f : ℝ) * ((n : ℝ) / 2) * Real.log (2 * D.host.v) +
      ∑ M ∈ Ico (k + 1) (k + n + 1), Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : k + (n + 1) + 1 = (k + n + 1) + 1 := by ring
    have e2 : k + (n + 1) = (k + n) + 1 := by ring
    rw [e1, Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega),
      Finset.sum_Ico_succ_top (show k + 1 ≤ k + n + 1 by omega), ih,
      log_mass_ratio_formula D (k + n + 1) (by omega), e2]
    have hf : facProd (k + n + 1) = facProd (k + n) * (((k + n).factorial : ℕ) : ℝ) := by
      unfold facProd
      rw [Finset.prod_range_succ]
    have hpos : 0 < facProd (k + n) := by
      unfold facProd
      exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
    have hfpos : (0 : ℝ) < (((k + n).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [hf, Real.log_mul hpos.ne' hfpos.ne']
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

/- English proof (translation)
Set `_` to `D.host.cmStar`. Introduce `h2b h2v h43 u`. Establish `hv` using `host_v_pos D`. Establish `hk` using `D.R.k_ge`. Establish `hm` using `D.R.two_le_m`.

Establish `hr : D.R.r = D.R.k + (D.R.m - 1)`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Use linear arithmetic over natural numbers and integers. Establish `hf : (0 : ℝ) < D.R.f` using `by exact_mod_cast degree_pos_alt D`. Establish `hkR : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by omega : 0 < D.R.k)`.

Establish `hg : ∀ i : Fin 2, (2 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).two_le`. Establish `hfac : ∀ (i : Fin 2) (j : ℕ), 1 ≤ j → 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹`. Introduce `i j hj`. Establish `h1 : (2 : ℝ) ≤ (D.host.g i : ℝ) ^ j` using `le_trans (hg i) (le_self_pow₀ (by linarith [hg i]) (by omega))`. Establish `h2 : ((D.host.g i : ℝ) ^ j)⁻¹ ≤ 2⁻¹` using `inv_anti₀ (by norm_num) h1`.

Evaluate the numerical expressions using `at h2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : (D.R.f : ℝ) * D.R.k * logXuD D u = Real.log (DstarD D / duStarU D u)`. Unfold `logXuD logXu`. Clear the denominators using the available nonvanishing facts.

Use `set R := ∏ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), ratioH D M with hR`. Establish `hmass : massI D D.R.r = massI D D.R.k * R`. Rewrite using `[hr]; exact mass_telescope D h2b hv D.R.k (by omega) (D.R.m - 1)`. Establish `hRpos : 0 < R` using `Finset.prod_pos fun M hM => mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)`. Use `set Q := ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ^ (D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2)) * ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f with hQ`.

Establish `hgg : 0 < (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)` using `mul_pos (by linarith [hg 0]) (by linarith [hg 1])`. Establish `hQ2 : 0 < ∏ i : Fin 2, ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ^ D.R.f` using `Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _`. Establish `hQpos : 0 < Q` using `mul_pos (pow_pos hgg _) hQ2`. Establish `h3 : idxSig D (D.host.g 0) (D.host.g 1) / idxPi D (D.host.g 0) (D.host.g 1) = Q` using `h43.2.2`. Establish `hidx : idxPi D (D.host.g 0) (D.host.g 1) ≠ 0`.

Introduce `h0`. Rewrite `h3` using `[h0, div_zero]`. Conclude with `hQpos.ne h3`. Establish `hmk : massI D D.R.k ≠ 0` using `(massI_pos D D.R.k).ne'`. Establish `hdim : ∀ ρ, 0 < dimV (uColR D u ρ)` using `fun ρ => dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`.

Establish `hP : 0 < ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))` using `Finset.prod_pos fun ρ _ => div_pos (D.dsig_pos ρ) (hdim ρ)`. Establish `e2 : DstarD D / duStarU D u = R * Q * ∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))`. Unfold `DstarD DstarP duStarU duStarP`. Rewrite using `[volume_eq_mass_at_rank D h2v, hmass, Finset.prod_div_distrib, ← h3]`. Establish `hd : (∏ ρ, dimV (uColR D u ρ)) ≠ 0` using `(Finset.prod_pos fun ρ _ => hdim ρ).ne'`.

Clear the denominators using the available nonvanishing facts. Establish `eR : Real.log R = ∑ M ∈ Ico (D.R.k + 1) (D.R.k + (D.R.m - 1) + 1), Real.log (ratioH D M)` using `Real.log_prod fun M hM => (mass_ratio_pos D hv M (by have := (Finset.mem_Ico.1 hM).1; omega)).ne'`. Establish `eQ : Real.log Q = ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) + (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Rewrite using `[hQ, Real.log_mul (pow_pos hgg _).ne' hQ2.ne', Real.log_pow, Real.log_prod]`. Use `congr 1`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_prod, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => Real.log_pow _ _`. Conclude with `fun j hj => (pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`.

Conclude with `fun i _ => (Finset.prod_pos fun j hj => pow_pos (hfac i j (by have := (Finset.mem_Ioc.1 hj).1; omega)) _).ne'`. Establish `eP : Real.log (∏ ρ, (D.dsig ρ / dimV (uColR D u ρ))) = ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (D.R.f : ℝ) * (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Rewrite using `[Real.log_prod fun ρ _ => (div_pos (D.dsig_pos ρ) (hdim ρ)).ne']`. Establish `: ∀ ρ, Real.log (D.dsig ρ / dimV (uColR D u ρ)) = Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Introduce `ρ`.

Establish `hvd : 0 < vand (uColR D u ρ)`. Use `hdim ρ` as an intermediate fact. Unfold `dimV at this`. Conclude with `(div_pos_iff_of_pos_right (factorial_product_pos _)).1 this`. Unfold `dimV`.

Rewrite using `[Real.log_div (D.dsig_pos ρ).ne' (div_pos hvd (factorial_product_pos _)).ne', Real.log_div hvd.ne' (factorial_product_pos _).ne', Real.log_div (mul_pos (D.dsig_pos ρ) (factorial_product_pos _)).ne' hvd.ne', Real.log_mul (D.dsig_pos ρ).ne' (factorial_product_pos _).ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun ρ _ => this ρ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Establish `he : ((D.R.f * (D.R.m * (2 * D.R.k + D.R.m - 1) / 2) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2)`. Take `⟨c, hc⟩` from `D.R.m_even`.

Establish `h1 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 = c * (2 * D.R.k + D.R.m - 1)`. Establish `: D.R.m * (2 * D.R.k + D.R.m - 1) = 2 * (c * (2 * D.R.k + D.R.m - 1))`. Generalize the expression as in `2 * D.R.k + D.R.m - 1 = X`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Nat.mul_div_cancel_left _ (by norm_num)]`. Establish `hX : ((2 * D.R.k + D.R.m - 1 : ℕ) : ℝ) = 2 * (D.R.k : ℝ) + D.R.m - 1`. Rewrite using `[Nat.cast_sub (by omega)]; push_cast; ring`. Establish `hmc : (D.R.m : ℝ) = 2 * c` using `by rw [hc]; push_cast; ring`. Rewrite using `[h1, Nat.cast_mul, Nat.cast_mul, hX, hmc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1` using `by rw [Nat.cast_sub (by omega)]; simp`. Rewrite using `[e1, e2, Real.log_mul (mul_pos hRpos hQpos).ne' hP.ne', Real.log_mul hRpos.ne' hQpos.ne', eR, eQ, eP, log_mass_ratio_telescoping D D.R.k (by omega) (D.R.m - 1), he, hn, Ico_succ_eq_Ioc, ← hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_word_scale_closed_form (D : D7) : LogWordScaleClosedFormOfIndexFormulas D := by
  let _ := D.host.cmStar
  intro h2b h2v h43 u
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
    rw [volume_eq_mass_at_rank D h2v, hmass, Finset.prod_div_distrib, ← h3]
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
Unfold `piN`. Rewrite using `[Finset.prod_Icc_succ_top (by omega)]`.
-/
theorem piN_succ (n g : ℕ) : piN (n + 1) g = piN n g * (1 - ((g : ℝ) ^ (n + 1))⁻¹) := by
  unfold piN
  rw [Finset.prod_Icc_succ_top (by omega)]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [piN]`. Consider the case `succ n ih`. Rewrite using `[piN_succ, ih, Finset.prod_range_succ]`. Use `congr 1`.

Rewrite using `[inv_pow]`.
-/
theorem piN_eq_range (n g : ℕ) : piN n g = ∏ i ∈ range n, (1 - ((g : ℝ)⁻¹) ^ (i + 1)) := by
  induction n with
  | zero => simp [piN]
  | succ n ih =>
    rw [piN_succ, ih, Finset.prod_range_succ]
    congr 1
    rw [inv_pow]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← add_assoc, piN_succ, ih, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega), mul_assoc]`.
-/
theorem piN_split (k n g : ℕ) : piN (k + n) g = piN k g * ∏ j ∈ Ioc k (k + n), (1 - ((g : ℝ) ^ j)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, piN_succ, ih, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega), mul_assoc]

/- English proof (translation)
Establish `hg1 : (1 : ℝ) < (g : ℝ)` using `by exact_mod_cast (show 1 < g by omega)`. Establish `h1 : (1 : ℝ) < (g : ℝ) ^ j` using `one_lt_pow₀ hg1 (by omega)`. Establish `h2 : ((g : ℝ) ^ j)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ h1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_sub_inv_pow_pos (g : ℕ) (hg : 2 ≤ g) (j : ℕ) (hj : 1 ≤ j) : 0 < 1 - ((g : ℝ) ^ j)⁻¹ := by
  have hg1 : (1 : ℝ) < (g : ℝ) := by exact_mod_cast (show 1 < g by omega)
  have h1 : (1 : ℝ) < (g : ℝ) ^ j := one_lt_pow₀ hg1 (by omega)
  have h2 : ((g : ℝ) ^ j)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

/- English proof (translation)
Unfold `piN`. Conclude with `Finset.prod_pos fun i hi => one_sub_inv_pow_pos g hg i (Finset.mem_Icc.mp hi).1`.
-/
theorem piN_pos (n g : ℕ) (hg : 2 ≤ g) : 0 < piN n g := by
  unfold piN
  exact Finset.prod_pos fun i hi => one_sub_inv_pow_pos g hg i (Finset.mem_Icc.mp hi).1

/- English proof (translation)
Establish `hfac : ∀ j : ℕ, 0 ≤ 1 - y ^ j ∧ 1 - y ^ j ≤ 1` using `fun j => ⟨by have := pow_le_one₀ (n := j) hy0 (by linarith); linarith, by have := pow_nonneg hy0 j; linarith⟩`. Establish `low : ∀ n : ℕ, 1 - 2 * y ^ (k + 1) + 2 * y ^ (k + n + 1) ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[← add_assoc, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega)]`. Establish `ht0 : 0 ≤ y ^ (k + n + 1)` using `pow_nonneg hy0 _`. Establish `hmono : y ^ (k + n + 1) ≤ y ^ (k + 1)` using `pow_le_pow_of_le_one hy0 (by linarith) (by omega)`. Establish `e : y ^ (k + n + 1 + 1) = y * y ^ (k + n + 1)` using `by ring`.

Rewrite using `[e]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right ih (hfac (k + n + 1)).1, mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 2 * y), mul_nonneg ht0 (sub_nonneg.mpr hmono)]`. Conclude with `⟨low n, Finset.prod_le_one (fun j _ => (hfac j).1) (fun j _ => (hfac j).2), Finset.prod_nonneg fun j _ => (hfac j).1⟩`.
-/
theorem partial_product_bounds (y : ℝ) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (k n : ℕ) :
    1 - 2 * y ^ (k + 1) + 2 * y ^ (k + n + 1) ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) ∧
      ∏ j ∈ Ioc k (k + n), (1 - y ^ j) ≤ 1 ∧ 0 ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) := by
  have hfac : ∀ j : ℕ, 0 ≤ 1 - y ^ j ∧ 1 - y ^ j ≤ 1 := fun j =>
    ⟨by have := pow_le_one₀ (n := j) hy0 (by linarith); linarith,
     by have := pow_nonneg hy0 j; linarith⟩
  have low : ∀ n : ℕ, 1 - 2 * y ^ (k + 1) + 2 * y ^ (k + n + 1) ≤ ∏ j ∈ Ioc k (k + n), (1 - y ^ j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.prod_Ioc_succ_top (show k ≤ k + n by omega)]
      have ht0 : 0 ≤ y ^ (k + n + 1) := pow_nonneg hy0 _
      have hmono : y ^ (k + n + 1) ≤ y ^ (k + 1) := pow_le_pow_of_le_one hy0 (by linarith) (by omega)
      have e : y ^ (k + n + 1 + 1) = y * y ^ (k + n + 1) := by ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right ih (hfac (k + n + 1)).1,
        mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ 1 - 2 * y), mul_nonneg ht0 (sub_nonneg.mpr hmono)]
  exact ⟨low n, Finset.prod_le_one (fun j _ => (hfac j).1) (fun j _ => (hfac j).2),
    Finset.prod_nonneg fun j _ => (hfac j).1⟩

/- English proof (translation)
Use `⟨k * (k - 1) / 2, rfl, ?_, ?_⟩` and prove the remaining obligations. Establish `h : k * (k + 1) = k * (k - 1) + k * 2`. Consider the cases of `k with`. Consider the case `zero => simp`. Consider the case `succ m`.

Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]`. Establish `h2` using `Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)`. Consider the cases of `k with`.

Consider the case `zero => simp`. Consider the case `succ m`. Simplify using `only [Nat.add_sub_cancel] at h2 ⊢`. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem triangular_number_identities (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  refine ⟨k * (k - 1) / 2, rfl, ?_, ?_⟩
  · have h : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ m =>
        simp only [Nat.add_sub_cancel]
        ring
    rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  · have h2 := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel] at h2 ⊢
      rw [h2]
      ring

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_two_mul_add_one_sq_expand (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring

/- English proof (translation)
Establish `hs` using `add_two_mul_add_one_sq_expand k s`. Establish `hk1 : (k + 1) ^ 2 = k * k + 2 * k + 1` using `by ring`. Prove the components needed by the constructor for the conclusion. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers.
-/
theorem index_exponent_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  have hs := add_two_mul_add_one_sq_expand k s
  have hk1 : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
  constructor
  · omega
  · omega

/- English proof (translation)
Rewrite using `[← Nat.card_eq_fintype_card, Matrix.card_GL_field, Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun i => (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ)) n]`. Establish `hq1 : 1 ≤ Fintype.card F` using `Fintype.card_pos`. Establish `hq : (0 : ℝ) < (Fintype.card F : ℝ)` using `by exact_mod_cast hq1`. Establish `hq0 : (Fintype.card F : ℝ) ≠ 0` using `hq.ne'`. Establish `key : ∀ i ∈ range n, (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ) = (Fintype.card F : ℝ) ^ n * (1 - ((Fintype.card F : ℝ)⁻¹) ^ (n - 1 - i + 1))`.

Introduce `i hi`. Establish `hin : i < n` using `Finset.mem_range.mp hi`. Establish `hle : (Fintype.card F) ^ i ≤ (Fintype.card F) ^ n` using `Nat.pow_le_pow_right hq1 hin.le`. Establish `e1 : n - 1 - i + 1 = n - i` using `by omega`. Establish `e2 : (Fintype.card F : ℝ) ^ n = (Fintype.card F : ℝ) ^ (n - i) * (Fintype.card F : ℝ) ^ i`.

Rewrite using `[← pow_add, Nat.sub_add_cancel hin.le]`. Rewrite using `[Nat.cast_sub hle, e1]`. Use `push_cast`. Rewrite using `[e2, inv_pow]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Finset.prod_congr rfl key, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]`. Use `congr 1`. Conclude with `Finset.prod_range_reflect (fun j => 1 - ((Fintype.card F : ℝ)⁻¹) ^ (j + 1)) n`.
-/
theorem card_GL_eq_pow_mul_prod' (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ)) n]
  have hq1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq1
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := hq.ne'
  have key : ∀ i ∈ range n, (((Fintype.card F) ^ n - (Fintype.card F) ^ i : ℕ) : ℝ) =
      (Fintype.card F : ℝ) ^ n * (1 - ((Fintype.card F : ℝ)⁻¹) ^ (n - 1 - i + 1)) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hle : (Fintype.card F) ^ i ≤ (Fintype.card F) ^ n := Nat.pow_le_pow_right hq1 hin.le
    have e1 : n - 1 - i + 1 = n - i := by omega
    have e2 : (Fintype.card F : ℝ) ^ n = (Fintype.card F : ℝ) ^ (n - i) * (Fintype.card F : ℝ) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hin.le]
    rw [Nat.cast_sub hle, e1]
    push_cast
    rw [e2, inv_pow]
    field_simp
  rw [Finset.prod_congr rfl key, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  congr 1
  exact Finset.prod_range_reflect (fun j => 1 - ((Fintype.card F : ℝ)⁻¹) ^ (j + 1)) n

/- English proof (translation)
Take `⟨A, hA1, hA2, hA3⟩` from `triangular_number_identities k`. Take `⟨t, rfl⟩` from `hev`. Take `⟨s, rfl⟩ : ∃ s, t = s + 1` from `⟨t - 1, by omega⟩`. Establish `hr : k + (s + 1 + (s + 1)) - 1 = k + 2 * s + 1` using `by omega`. Establish `hm2 : (s + 1 + (s + 1)) / 2 - 1 = s` using `by omega`.

Take `⟨h1, h2⟩` from `index_exponent_identities k s A hA3`. Establish `hq : (0 : ℝ) < (Fintype.card F : ℝ)` using `by exact_mod_cast Fintype.card_pos`. Establish `hsq : (k + 2 * s + 1) * (k + 2 * s + 1) = (2 * (s * k) + s + 2 * (s * s)) + A + (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s))`. Establish `hs` using `add_two_mul_add_one_sq_expand k s`. Rewrite `hs` using `[sq]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hr, hm2, h1, h2, hA1, hA2, card_GL_eq_pow_mul_prod', card_GL_eq_pow_mul_prod', hA3, hsq]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[div_eq_iff (pow_pos hq _).ne']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[div_eq_iff (mul_pos (pow_pos hq _) (pow_pos hq _)).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_index_at_place (F : Type) [Field F] [Fintype F] [DecidableEq F] (k m : ℕ) (hm : 2 ≤ m) (hev : Even m) :
    (Fintype.card (GL (Fin k) F) : ℝ) / (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) =
      (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * ∏ i ∈ range k, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) ∧
    (Fintype.card (GL (Fin (k + m - 1)) F) : ℝ) /
        ((Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 - (k + 1) ^ 2 - 2 * (m / 2 - 1)) / 2) *
          (Fintype.card F : ℝ) ^ (k * (k - 1) / 2)) =
      (Fintype.card F : ℝ) ^ (((k + m - 1) ^ 2 + 3 * k + 1 + 2 * (m / 2 - 1)) / 2) *
        ∏ i ∈ range (k + m - 1), (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_number_identities k
  obtain ⟨t, rfl⟩ := hev
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hr : k + (s + 1 + (s + 1)) - 1 = k + 2 * s + 1 := by omega
  have hm2 : (s + 1 + (s + 1)) / 2 - 1 = s := by omega
  obtain ⟨h1, h2⟩ := index_exponent_identities k s A hA3
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : (k + 2 * s + 1) * (k + 2 * s + 1) =
      (2 * (s * k) + s + 2 * (s * s)) + A + (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
    have hs := add_two_mul_add_one_sq_expand k s
    rw [sq] at hs
    omega
  rw [hr, hm2, h1, h2, hA1, hA2, card_GL_eq_pow_mul_prod', card_GL_eq_pow_mul_prod', hA3, hsq]
  constructor
  · rw [div_eq_iff (pow_pos hq _).ne']
    ring
  · rw [div_eq_iff (mul_pos (pow_pos hq _) (pow_pos hq _)).ne']
    ring

/- English proof (translation)
Use `⟨fun i => ?_, fun n g hg => ?_⟩` and prove the remaining obligations. Establish `: Fact (D.host.g i).Prime` using `⟨D.host.g_prime i⟩`. Establish `hc : Fintype.card (ZMod (D.host.g i)) = D.host.g i` using `ZMod.card _`. Establish `hg2 : 2 ≤ D.host.g i` using `(D.host.g_prime i).two_le`. Take `⟨h1, h2⟩` from `local_index_at_place (ZMod (D.host.g i)) D.R.k D.R.m D.R.two_le_m D.R.m_even`.

Rewrite `h1`, `h2` using `[hc]`. Establish `e1 : idxColLoc (D.host.g i) D.R.k = (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i)`. Rewrite using `[piN_eq_range, ← h1]`. Unfold `idxColLoc idxLoc`. Rewrite using `[card_GL_subtype_eq_card_matrix _ det_eq_one_of_unitriangular]`.

Use `Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular (ZMod (D.host.g i)) D.R.k` as an intermediate fact. Rewrite `this` using `[hc]`. Establish `h3 : Nat.card {A : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (D.host.g i)) // IsUnitri A} = D.host.g i ^ (D.R.k * (D.R.k - 1) / 2)` using `this`. Rewrite using `[h3, Nat.card_eq_fintype_card]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `e2 : idxRowLoc (D.host.g i) D.R.k D.R.m = (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * piN D.R.r (D.host.g i)`. Establish `h2' : _ = (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * ∏ j ∈ range D.R.r, (1 - ((D.host.g i : ℝ)⁻¹) ^ (j + 1))` using `h2`. Rewrite using `[piN_eq_range, ← h2']`. Unfold `idxRowLoc idxLoc`.

Rewrite using `[rowLevCard_holds _ _ _ (D.host.g_prime i) D.R.two_le_m D.R.m_even, Nat.card_eq_fintype_card]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hr : D.R.r = D.R.k + (D.R.m - 1)`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Use `D.R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hq : piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) = ∏ j ∈ Ioc D.R.k (D.R.k + (D.R.m - 1)), (1 - ((D.host.g i : ℝ)⁻¹) ^ j)`. Rewrite using `[hr, piN_split, mul_div_cancel_left₀ _ (piN_pos _ _ hg2).ne']`. Conclude with `Finset.prod_congr rfl fun j _ => by rw [inv_pow]`.

Establish `hy0 : (0 : ℝ) ≤ (D.host.g i : ℝ)⁻¹` using `by positivity`. Establish `hy : (D.host.g i : ℝ)⁻¹ ≤ 1 / 2`. Rewrite using `[one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hg2)`. Take `⟨t1, t2, -⟩` from `partial_product_bounds _ hy0 hy D.R.k (D.R.m - 1)`. Use `⟨e1, e2, ?_, by rw [hq]; exact t2⟩` and prove the remaining obligations.

Rewrite using `[hq, ← inv_pow]`. Establish `: 0 ≤ 2 * ((D.host.g i : ℝ)⁻¹) ^ (D.R.k + (D.R.m - 1) + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[piN_eq_range]`. Conclude with `Formalism.LogVandermondeBounds.StandardLattice.eulerProductBounds (g : ℝ) (by exact_mod_cast hg) n`.
-/
theorem local_index_formulas_and_bounds (D : D7) : LocalIndexFormulasAndBounds D := by
  refine ⟨fun i => ?_, fun n g hg => ?_⟩
  · have : Fact (D.host.g i).Prime := ⟨D.host.g_prime i⟩
    have hc : Fintype.card (ZMod (D.host.g i)) = D.host.g i := ZMod.card _
    have hg2 : 2 ≤ D.host.g i := (D.host.g_prime i).two_le
    obtain ⟨h1, h2⟩ := local_index_at_place (ZMod (D.host.g i)) D.R.k D.R.m D.R.two_le_m D.R.m_even
    rw [hc] at h1 h2
    have e1 : idxColLoc (D.host.g i) D.R.k =
        (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i) := by
      rw [piN_eq_range, ← h1]
      unfold idxColLoc idxLoc
      rw [card_GL_subtype_eq_card_matrix _ det_eq_one_of_unitriangular]
      have := Formalism.LogVandermondeBounds.StandardLattice.cardUnitriangular (ZMod (D.host.g i)) D.R.k
      rw [hc] at this
      have h3 : Nat.card {A : Matrix (Fin D.R.k) (Fin D.R.k) (ZMod (D.host.g i)) // IsUnitri A} =
          D.host.g i ^ (D.R.k * (D.R.k - 1) / 2) := this
      rw [h3, Nat.card_eq_fintype_card]
      push_cast
      rfl
    have e2 : idxRowLoc (D.host.g i) D.R.k D.R.m =
        (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * piN D.R.r (D.host.g i) := by
      have h2' : _ = (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) *
          ∏ j ∈ range D.R.r, (1 - ((D.host.g i : ℝ)⁻¹) ^ (j + 1)) := h2
      rw [piN_eq_range, ← h2']
      unfold idxRowLoc idxLoc
      rw [rowLevCard_holds _ _ _ (D.host.g_prime i) D.R.two_le_m D.R.m_even, Nat.card_eq_fintype_card]
      push_cast
      rfl
    have hr : D.R.r = D.R.k + (D.R.m - 1) := by
      have er : D.R.r = D.R.k + D.R.m - 1 := rfl
      have := D.R.two_le_m
      omega
    have hq : piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) =
        ∏ j ∈ Ioc D.R.k (D.R.k + (D.R.m - 1)), (1 - ((D.host.g i : ℝ)⁻¹) ^ j) := by
      rw [hr, piN_split, mul_div_cancel_left₀ _ (piN_pos _ _ hg2).ne']
      exact Finset.prod_congr rfl fun j _ => by rw [inv_pow]
    have hy0 : (0 : ℝ) ≤ (D.host.g i : ℝ)⁻¹ := by positivity
    have hy : (D.host.g i : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hg2)
    obtain ⟨t1, t2, -⟩ := partial_product_bounds _ hy0 hy D.R.k (D.R.m - 1)
    refine ⟨e1, e2, ?_, by rw [hq]; exact t2⟩
    rw [hq, ← inv_pow]
    have : 0 ≤ 2 * ((D.host.g i : ℝ)⁻¹) ^ (D.R.k + (D.R.m - 1) + 1) := by positivity
    linarith
  · rw [piN_eq_range]
    exact Formalism.LogVandermondeBounds.StandardLattice.eulerProductBounds (g : ℝ) (by exact_mod_cast hg) n

/- English proof (translation)
Take `⟨hloc, -⟩` from `h`. Establish `hPi : idxPi D (D.host.g 0) (D.host.g 1) = ∏ i : Fin 2, ((D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i)) ^ D.R.f`. Unfold `idxPi`. Rewrite using `[Fin.prod_univ_two, (hloc 0).1, (hloc 1).1]`. Establish `hSig : idxSig D (D.host.g 0) (D.host.g 1) = ∏ i : Fin 2, ((D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) * piN D.R.r (D.host.g i)) ^ D.R.f`.

Unfold `idxSig`. Rewrite using `[Fin.prod_univ_two, (hloc 0).2.1, (hloc 1).2.1]`. Use `⟨hPi, hSig, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `D.R.m_even`. Establish `hm2` using `D.R.two_le_m`.

Take `⟨A, hA1, hA2, hA3⟩` from `triangular_number_identities D.R.k`. Establish `hE : (D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2 = D.R.k * (D.R.k + 1) / 2 + D.R.m * (2 * D.R.k + D.R.m - 1) / 2`. Take `⟨s, rfl⟩ : ∃ s, t = s + 1` from `⟨t - 1, by omega⟩`. Establish `e1 : D.R.r = D.R.k + 2 * s + 1` using `by show D.R.k + D.R.m - 1 = _`. Use linear arithmetic over natural numbers and integers.

Establish `e2 : D.R.rS = s` using `by show D.R.m / 2 - 1 = _`. Use linear arithmetic over natural numbers and integers. Establish `e3 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 = 2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1`. Rewrite using `[ht]`. Establish `h4 : (s + 1 + (s + 1)) * (2 * D.R.k + (s + 1 + (s + 1)) - 1) = 2 * (2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1)`.

Establish `h5 : 2 * D.R.k + (s + 1 + (s + 1)) - 1 = 2 * D.R.k + 2 * s + 1` using `by omega`. Rewrite using `[h5]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, e2, (index_exponent_identities D.R.k s A hA3).2, e3, hA2]`. Use linear arithmetic over natural numbers and integers. Establish `hg : ∀ i, 2 ≤ D.host.g i` using `fun i => (D.host.g_prime i).two_le`. Establish `hgR : ∀ i, (0 : ℝ) < (D.host.g i : ℝ)` using `fun i => by`. Use `hg i` as an intermediate fact.

Conclude with `(show 0 < D.host.g i by omega)` after adjusting the coercions. Establish `hN : ∀ i, 0 < piN D.R.k (D.host.g i)` using `fun i => piN_pos _ _ (hg i)`. Establish `hr' : D.R.r = D.R.k + (D.R.m - 1)` using `by show D.R.k + D.R.m - 1 = _`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hPi, hSig, hE, hr']`.

Simplify using `only [Fin.prod_univ_two]`. Rewrite using `[piN_split, piN_split, Finset.prod_pow, Finset.prod_pow, div_eq_iff (mul_pos (pow_pos (mul_pos (pow_pos (hgR 0) _) (hN 0)) _) (pow_pos (mul_pos (pow_pos (hgR 1) _) (hN 1)) _)).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem indices_four_three_of_indices_four_two (D : D7) (h : LocalIndexFormulasAndBounds D) : IndexProductFormulasAndRatio D := by
  obtain ⟨hloc, -⟩ := h
  have hPi : idxPi D (D.host.g 0) (D.host.g 1) =
      ∏ i : Fin 2, ((D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) * piN D.R.k (D.host.g i)) ^ D.R.f := by
    unfold idxPi
    rw [Fin.prod_univ_two, (hloc 0).1, (hloc 1).1]
  have hSig : idxSig D (D.host.g 0) (D.host.g 1) =
      ∏ i : Fin 2, ((D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) *
        piN D.R.r (D.host.g i)) ^ D.R.f := by
    unfold idxSig
    rw [Fin.prod_univ_two, (hloc 0).2.1, (hloc 1).2.1]
  refine ⟨hPi, hSig, ?_⟩
  obtain ⟨t, ht⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_number_identities D.R.k
  have hE : (D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2 =
      D.R.k * (D.R.k + 1) / 2 + D.R.m * (2 * D.R.k + D.R.m - 1) / 2 := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have e1 : D.R.r = D.R.k + 2 * s + 1 := by
      show D.R.k + D.R.m - 1 = _
      omega
    have e2 : D.R.rS = s := by
      show D.R.m / 2 - 1 = _
      omega
    have e3 : D.R.m * (2 * D.R.k + D.R.m - 1) / 2 =
        2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1 := by
      rw [ht]
      have h4 : (s + 1 + (s + 1)) * (2 * D.R.k + (s + 1 + (s + 1)) - 1) =
          2 * (2 * (s * D.R.k) + 2 * (s * s) + 3 * s + 2 * D.R.k + 1) := by
        have h5 : 2 * D.R.k + (s + 1 + (s + 1)) - 1 = 2 * D.R.k + 2 * s + 1 := by omega
        rw [h5]
        ring
      rw [h4]
      omega
    rw [e1, e2, (index_exponent_identities D.R.k s A hA3).2, e3, hA2]
    omega
  have hg : ∀ i, 2 ≤ D.host.g i := fun i => (D.host.g_prime i).two_le
  have hgR : ∀ i, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    have := hg i
    exact_mod_cast (show 0 < D.host.g i by omega)
  have hN : ∀ i, 0 < piN D.R.k (D.host.g i) := fun i => piN_pos _ _ (hg i)
  have hr' : D.R.r = D.R.k + (D.R.m - 1) := by
    show D.R.k + D.R.m - 1 = _
    omega
  rw [hPi, hSig, hE, hr']
  simp only [Fin.prod_univ_two]
  rw [piN_split, piN_split, Finset.prod_pow, Finset.prod_pow,
    div_eq_iff (mul_pos (pow_pos (mul_pos (pow_pos (hgR 0) _) (hN 0)) _)
      (pow_pos (mul_pos (pow_pos (hgR 1) _) (hN 1)) _)).ne']
  ring

/- English proof (translation)
The claim follows from `indices_four_three_of_indices_four_two D (local_index_formulas_and_bounds D)`.
-/
theorem index_product_formulas_and_ratio (D : D7) : IndexProductFormulasAndRatio D := indices_four_three_of_indices_four_two D (local_index_formulas_and_bounds D)

/- English proof (translation)
The claim follows from `log_word_scale_closed_form D h2b h2v (index_product_formulas_and_ratio D)`.
-/
theorem identity_five_one_of_aux2b_of_aux2v (D : D7) (h2b : MassRatio₂ D) (h2v : VolumeEqMass₂ D) : LemmaFiveOneIdentity D :=
  log_word_scale_closed_form D h2b h2v (index_product_formulas_and_ratio D)

end Formalism.MainNotions.StandardLattice
