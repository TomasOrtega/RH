import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResChiSandwichUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResChiSandwich

open MvPolynomial MeasureTheory Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds
open scoped ComplexOrder Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

/- English proof (translation)
Establish `hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x)` using `ae_iff.mpr hcar`. Unfold `bNormSq`. Combine the equalities or inequalities in the displayed calculation. Use `integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_` and prove the remaining obligations. Conclude with `mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))`.

Use `filter_upwards [hae] with z hz using h z hz`. Use `_ = B := by simp`.
-/
theorem bNormSq_le_of_pts_of {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0) {n r : ℕ}
    (s : Fin r → (Ix κ → ℂ) → ℂ) (c : Fin r → ℂ) {B : ℝ}
    (h : ∀ z ∈ pts (coordIdeal ℤ x), ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ≤ B) :
    bNormSq μ s (wgt m n) c ≤ B := by
  have hae : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := ae_iff.mpr hcar
  unfold bNormSq
  calc ∫ z, ‖∑ j, c j * s j z‖ ^ 2 * wgt m n z ∂μ ≤ ∫ _z, B ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => ?_) (integrable_const B) ?_
        · exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (pow_nonneg (m.nonneg z) _))
        · filter_upwards [hae] with z hz using h z hz
    _ = B := by simp

/- English proof (translation)
Take `⟨S, -, hS⟩` from `form_le_pnorm hfr k f hf`. Use `⟨S, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hmz : m.ρ z = pnorm e z` using `hFS z hz`. Rewrite using `[hmz]`. Conclude with `hS z hz`.
-/
theorem form_le_rho {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {e : Fin (D + 1) → Ix κ}
    (hfr : IsProjFrame x e) (hFS : IsPullFS x e m) (k : ℕ) (f : MvPolynomial (Ix κ) ℂ) (hf : f.IsHomogeneous k) :
    ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z f‖ ≤ S * m.ρ z ^ k := by
  obtain ⟨S, -, hS⟩ := form_le_pnorm hfr k f hf
  refine ⟨S, fun z hz => ?_⟩
  have hmz : m.ρ z = pnorm e z := hFS z hz
  rw [hmz]
  exact hS z hz

/- English proof (translation)
Take `⟨kε, ε, hε, hli⟩` from `exists_indep_sections x e hfr.isRatProjFrame`. Establish `hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous kε ∧ aeval x Hl = ε l` using `fun l => by`. Take `⟨p, hp, hpe⟩` from `Submodule.mem_map.mp (hε l)`. Conclude with `⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩`. Use `choose H hHh hHe using hεH`.

Establish `hliH : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l)`. Rewrite using `[show (fun l => aeval x (H l)) = ε from funext hHe]`. Conclude with `hli`. Establish `hCl : ∀ l, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * m.ρ z ^ kε` using `fun l => form_le_rho hfr hFS kε _ ((hHh l).map _)`. Use `choose Cl hCl using hCl`.

Use `set Cε := ∑ l, |Cl l| with hCεdef`. Establish `hCε0 : 0 ≤ Cε` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε` using `fun l z hz => (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l))) (pow_nonneg (m.nonneg z) _))`. Take `⟨k₀, hk₀⟩` from `exists_sec_eq_mul x e hfr`. Take `⟨tb, htb⟩` from `exists_isSecBasis x k₀`.

Use `choose Tf hTfh hTfb using htb.1`. Establish `hCt : ∀ i, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ S * m.ρ z ^ k₀` using `fun i => form_le_rho hfr hFS k₀ _ ((hTfh i).map _)`. Use `choose Cti hCti using hCt`. Use `set Ct := ∑ i, |Cti i| with hCtdef`. Establish `hCt : ∀ i, ∀ z ∈ pts (coordIdeal ℤ x), ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ Ct * m.ρ z ^ k₀` using `fun i z hz => (hCti i z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |Cti i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))) (pow_nonneg (m.nonneg z) _))`.

Establish `hCt0 : 0 ≤ Ct` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Take `⟨k', hk'⟩` from `finrank_sec_le x e hfr`. Use `set T : ℝ := max 1 (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) with hTdef`. Establish `hT1 : 1 ≤ T` using `le_max_left _ _`. Use `set lam : ℝ := max 1 Ct with hlamdef`.

Establish `hlam1 : 1 ≤ lam` using `le_max_left _ _`. Establish `hloglam : 0 ≤ Real.log lam` using `Real.log_nonneg hlam1`. Use `⟨max kε k₀, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2), fun n hn r b hb => ?_⟩` and prove the remaining obligations. Take `rfl` from `hb.card_eq`. Establish `hn1 : 1 ≤ n` using `by omega`.

Establish `hnk : n - kε + kε = n` using `Nat.sub_add_cancel (by omega)`. Establish `hnk₀ : n - k₀ + k₀ = n` using `Nat.sub_add_cancel (by omega)`. Take `⟨crd, hcrd1, hcrd2⟩` from `exists_crd hb`. Establish `hQh : ∀ p : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card), (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)).IsHomogeneous n` using `fun p => by`. Use `prodForm_isHomogeneous e (adtEnum_sum D (n - kε) (finProdFinEquiv.symm p).2) (hHh (finProdFinEquiv.symm p).1)` as an intermediate fact.

Rewrite `this` using `[hnk]`. Then use the resulting hypothesis. Establish `hQm : ∀ p, aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)) ∈ sec ℤ x n` using `fun p => Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQh p), rfl⟩`. Use `set M : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card)) ℤ := Matrix.of fun j p => crd ⟨_, hQm p⟩ j with hMdef`. Establish `hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1))` using `fun p => hcrd1 ⟨_, hQm p⟩`. Establish `hinj` using `injective_map_of_int_ker M (alphaMat_ker hfr H hliH M hM)`.

Establish `hr` using `le_of_injective_mulVec _ hinj`. Establish `hG'` using `monoDiag_posDef D (n - kε) (projDeg x e)`. Establish `hG` using `hpd n _ b hb`. Use `set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef`. Establish `hn1' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn1`.

Establish `hTn : 1 ≤ T * (n : ℝ) ^ D` using `one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1')`. Establish `hA : 0 < A` using `Real.sqrt_pos.mpr (by linarith)`. Establish `hA2 : A ^ 2 = T * (n : ℝ) ^ D` using `Real.sq_sqrt (by linarith)`. Establish `hnorm : (((A : ℂ) ^ 2) • monoDiag D (n - kε) (projDeg x e) - (M.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) * M.map (Int.cast : ℤ → ℂ)).PosSemidef`. Use `psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A) (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_` and prove the remaining obligations.

Rewrite using `[quad_conj, ← bNormSq_eq_re μ _ _ (hint n _ b hb), Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, quad_monoDiag]`. Establish `hq0 : 0 ≤ ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2` using `Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun i _ => mul_nonneg (monoNormSq_pos _).le (sq_nonneg _)`. Use `bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_` and prove the remaining obligations. Rewrite using `[sum_mulVec_secFun hb M _ hQh hM c z hz]`. Establish `h1` using `pt_lower hFS H hCε0 hCε c hz`.

Rewrite `h1` using `[hnk]`. Use `h1.trans ?_` and prove the remaining obligations. Establish `hswap : ∑ l : Fin (projDeg x e), ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 * monoNormSq (adtEnum D (n - kε) i) = ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2` using `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _`. Rewrite using `[hswap, hA2]`. Use `mul_le_mul_of_nonneg_right ?_ hq0` and prove the remaining obligations.

Establish `hB1 : (((n - kε + D).choose D : ℕ) : ℝ) ≤ (((n + 0 + D).choose D : ℕ) : ℝ)`. Conclude with `Nat.choose_le_choose D (by omega)` after adjusting the coercions. Establish `hB2` using `choose_bound 0 D hn1`. Combine the equalities or inequalities in the displayed calculation. Establish `hQ'h : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)), (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)).IsHomogeneous n` using `fun s => by`.

Use `prodForm_isHomogeneous e (adtEnum_sum D (n - k₀) s.1) (hTfh s.2)` as an intermediate fact. Rewrite `this` using `[hnk₀]`. Then use the resulting hypothesis. Establish `hwm : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)), aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)) ∈ sec ℤ x n` using `fun s => Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQ'h s), rfl⟩`. Establish `hspan` using `crd_span hcrd2 hb _ hwm (sec_le_span_prod (hk₀ n (by omega)) htb Tf hTfb)`. Take `⟨f, hfdet⟩` from `exists_cols_det_ne_zero _ hspan`.

Use `set Nm : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (finrank ℤ (sec ℤ x n))) ℤ := Matrix.of fun p q => crd ⟨_, hwm (f q)⟩ p with hNm`. Establish `hsmall : ∀ i, (((Nm.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) * Nm.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2`. Introduce `i`. Rewrite using `[diag_conj_eq, ← bNormSq_eq_re μ _ _ (hint n _ b hb)]`. Use `bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_` and prove the remaining obligations.

Establish `hv : Nm.map (Int.cast : ℤ → ℂ) *ᵥ Pi.single i 1 = fun p => ((crd ⟨_, hwm (f i)⟩ p : ℤ) : ℂ)`. Use function extensionality and compare the values at `p`. Simplify using `[hNm, Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite using `[hv, sum_secFun_eq' hb _ (hQ'h (f i)) _ (hcrd1 ⟨_, hwm (f i)⟩) z hz]`. Establish `h1` using `pt_small hFS (adtEnum_sum D (n - k₀) (f i).1) (Tf (f i).2) (hCt (f i).2) hz`.

Rewrite `h1` using `[hnk₀]`. Conclude with `h1.trans (pow_le_pow_left₀ hCt0 (le_max_right _ _) 2)`. Establish `key` using `neg_log_det_le hr hG' hG M hinj _ hfdet hA (by linarith) hnorm hsmall`. Rewrite `key` using `[neg_log_det_monoDiag]`. Establish `hmono : Monotone (chiP D)` using `monotone_nat_of_le_succ fun n => by`.

Use `chiP_succ_sub_nonneg D n` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm` using `mul_le_mul_of_nonneg_left (hmono (show n - max kε k₀ ≤ n - kε by omega)) (Nat.cast_nonneg (projDeg x e) : (0 : ℝ) ≤ projDeg x e)`. Take `⟨hL0, hL⟩` from `log_sqrt_bound D hT1 hn1`. Establish `hll` using `log_le_div_mul hloglam hn1`.

Use `set R' := projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card`. Use `set r := finrank ℤ (sec ℤ x n)`. Establish `hrR : (R' : ℝ) ≤ r` using `by exact_mod_cast hr`. Establish `hR0 : (0 : ℝ) ≤ R'` using `Nat.cast_nonneg _`. Establish `hrb : (r : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D`.

Establish `h1 : (r : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ)`. Conclude with `hk' n` after adjusting the coercions. Rewrite using `[mul_assoc]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn1) (Nat.cast_nonneg _))`. Establish `hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D` using `by positivity`.

Establish `hlogn : 0 ≤ Real.log ((n : ℝ) + 1)` using `Real.log_nonneg (by linarith)`. Establish `h3 : (R' : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1))` using `(mul_le_mul_of_nonneg_right (hrR.trans hrb) hL0).trans (mul_le_mul_of_nonneg_left hL hX)`. Establish `h4 : ((r : ℝ) - R') * Real.log lam ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D * (Real.log lam / Real.log 2 * Real.log (n + 1))` using `(mul_le_mul_of_nonneg_right (by linarith) hloglam).trans (mul_le_mul_of_nonneg_left hll hX)`. Establish `h5 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2) * (n : ℝ) ^ D * Real.log (n + 1) = (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D * ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1 …` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    {e : Fin (D + 1) → Ix κ} (hfr : IsProjFrame x e) (hFS : IsPullFS x e m)
    [IsProbabilityMeasure μ] (hcar : μ (pts (coordIdeal ℤ x))ᶜ = 0)
    (hint : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b → ∀ i j,
      Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ)
    (hpd : ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef) :
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n → ∀ (r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n b →
      (projDeg x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤
        -(1 / 2) * Real.log (bGram μ (fun j => secFun (b j)) (wgt m n)).det.re := by
  classical
  obtain ⟨kε, ε, hε, hli⟩ := exists_indep_sections x e hfr.isRatProjFrame
  have hεH : ∀ l, ∃ Hl : MvPolynomial (Ix κ) ℤ, Hl.IsHomogeneous kε ∧ aeval x Hl = ε l := fun l => by
    obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp (hε l)
    exact ⟨p, (mem_homogeneousSubmodule _ _).mp hp, hpe⟩
  choose H hHh hHe using hεH
  have hliH : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l) := by
    rw [show (fun l => aeval x (H l)) = ε from funext hHe]; exact hli
  have hCl : ∀ l, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ S * m.ρ z ^ kε :=
    fun l => form_le_rho hfr hFS kε _ ((hHh l).map _)
  choose Cl hCl using hCl
  set Cε := ∑ l, |Cl l| with hCεdef
  have hCε0 : 0 ≤ Cε := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hCε : ∀ l, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (H l))‖ ≤ Cε * m.ρ z ^ kε := fun l z hz =>
    (hCl l z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cl i|) (fun i _ => abs_nonneg _) (Finset.mem_univ l)))
      (pow_nonneg (m.nonneg z) _))
  obtain ⟨k₀, hk₀⟩ := exists_sec_eq_mul x e hfr
  obtain ⟨tb, htb⟩ := exists_isSecBasis x k₀
  choose Tf hTfh hTfb using htb.1
  have hCt : ∀ i, ∃ S : ℝ, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ S * m.ρ z ^ k₀ :=
    fun i => form_le_rho hfr hFS k₀ _ ((hTfh i).map _)
  choose Cti hCti using hCt
  set Ct := ∑ i, |Cti i| with hCtdef
  have hCt : ∀ i, ∀ z ∈ pts (coordIdeal ℤ x),
      ‖eval z (map (Int.castRingHom ℂ) (Tf i))‖ ≤ Ct * m.ρ z ^ k₀ := fun i z hz =>
    (hCti i z hz).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Cti i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)))
      (pow_nonneg (m.nonneg z) _))
  have hCt0 : 0 ≤ Ct := Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨k', hk'⟩ := finrank_sec_le x e hfr
  set T : ℝ := max 1 (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  set lam : ℝ := max 1 Ct with hlamdef
  have hlam1 : 1 ≤ lam := le_max_left _ _
  have hloglam : 0 ≤ Real.log lam := Real.log_nonneg hlam1
  refine ⟨max kε k₀, (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
    ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2), fun n hn r b hb => ?_⟩
  obtain rfl := hb.card_eq
  have hn1 : 1 ≤ n := by omega
  have hnk : n - kε + kε = n := Nat.sub_add_cancel (by omega)
  have hnk₀ : n - k₀ + k₀ = n := Nat.sub_add_cancel (by omega)
  obtain ⟨crd, hcrd1, hcrd2⟩ := exists_crd hb

  have hQh : ∀ p : Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card),
      (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)).IsHomogeneous n :=
    fun p => by
      have := prodForm_isHomogeneous e (adtEnum_sum D (n - kε) (finProdFinEquiv.symm p).2)
        (hHh (finProdFinEquiv.symm p).1)
      rwa [hnk] at this
  have hQm : ∀ p, aeval x (prodForm e (adtEnum D (n - kε) (finProdFinEquiv.symm p).2)
      (H (finProdFinEquiv.symm p).1)) ∈ sec ℤ x n := fun p =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQh p), rfl⟩
  set M : Matrix (Fin (finrank ℤ (sec ℤ x n)))
      (Fin (projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card)) ℤ :=
    Matrix.of fun j p => crd ⟨_, hQm p⟩ j with hMdef
  have hM : ∀ p, ∑ j, (M j p : Ω) * aeval x (b j) = aeval x (prodForm e
      (adtEnum D (n - kε) (finProdFinEquiv.symm p).2) (H (finProdFinEquiv.symm p).1)) :=
    fun p => hcrd1 ⟨_, hQm p⟩
  have hinj := injective_map_of_int_ker M (alphaMat_ker hfr H hliH M hM)
  have hr := le_of_injective_mulVec _ hinj
  have hG' := monoDiag_posDef D (n - kε) (projDeg x e)
  have hG := hpd n _ b hb
  set A := Real.sqrt (T * (n : ℝ) ^ D) with hAdef
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hTn : 1 ≤ T * (n : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hn1')
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  have hA2 : A ^ 2 = T * (n : ℝ) ^ D := Real.sq_sqrt (by linarith)
  have hnorm : (((A : ℂ) ^ 2) • monoDiag D (n - kε) (projDeg x e) -
      (M.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
        M.map (Int.cast : ℤ → ℂ)).PosSemidef := by
    refine psd_sub_of_quad_le (isHermitian_sq_smul hG'.isHermitian A)
      (Matrix.isHermitian_conjTranspose_mul_mul _ hG.isHermitian) fun c => ?_
    rw [quad_conj, ← bNormSq_eq_re μ _ _ (hint n _ b hb), Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, quad_monoDiag]
    have hq0 : 0 ≤ ∑ l : Fin (projDeg x e), ∑ i, monoNormSq (adtEnum D (n - kε) i) *
        ‖c (finProdFinEquiv (l, i))‖ ^ 2 := Finset.sum_nonneg fun l _ =>
      Finset.sum_nonneg fun i _ => mul_nonneg (monoNormSq_pos _).le (sq_nonneg _)
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    rw [sum_mulVec_secFun hb M _ hQh hM c z hz]
    have h1 := pt_lower hFS H hCε0 hCε c hz
    rw [hnk] at h1
    refine h1.trans ?_
    have hswap : ∑ l : Fin (projDeg x e), ∑ i, ‖c (finProdFinEquiv (l, i))‖ ^ 2 *
        monoNormSq (adtEnum D (n - kε) i) = ∑ l : Fin (projDeg x e), ∑ i,
        monoNormSq (adtEnum D (n - kε) i) * ‖c (finProdFinEquiv (l, i))‖ ^ 2 :=
      Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hswap, hA2]
    refine mul_le_mul_of_nonneg_right ?_ hq0
    have hB1 : (((n - kε + D).choose D : ℕ) : ℝ) ≤ (((n + 0 + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_le_choose D (by omega)
    have hB2 := choose_bound 0 D hn1
    calc Cε ^ 2 * (projDeg x e : ℝ) * (((n - kε + D).choose D : ℕ) : ℝ)
        ≤ Cε ^ 2 * (projDeg x e : ℝ) * (((1 + 0 + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D) :=
          mul_le_mul_of_nonneg_left (hB1.trans hB2) (by positivity)
      _ = (Cε ^ 2 * (projDeg x e : ℝ) * ((1 + 0 + D : ℕ) : ℝ) ^ D) * (n : ℝ) ^ D := by ring
      _ ≤ T * (n : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

  have hQ'h : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)).IsHomogeneous n := fun s => by
    have := prodForm_isHomogeneous e (adtEnum_sum D (n - k₀) s.1) (hTfh s.2)
    rwa [hnk₀] at this
  have hwm : ∀ s : Fin (Finset.Nat.antidiagonalTuple (D + 1) (n - k₀)).card × Fin (finrank ℤ (sec ℤ x k₀)),
      aeval x (prodForm e (adtEnum D (n - k₀) s.1) (Tf s.2)) ∈ sec ℤ x n := fun s =>
    Submodule.mem_map.mpr ⟨_, (mem_homogeneousSubmodule _ _).mpr (hQ'h s), rfl⟩
  have hspan := crd_span hcrd2 hb _ hwm (sec_le_span_prod (hk₀ n (by omega)) htb Tf hTfb)
  obtain ⟨f, hfdet⟩ := exists_cols_det_ne_zero _ hspan
  set Nm : Matrix (Fin (finrank ℤ (sec ℤ x n))) (Fin (finrank ℤ (sec ℤ x n))) ℤ :=
    Matrix.of fun p q => crd ⟨_, hwm (f q)⟩ p with hNm
  have hsmall : ∀ i, (((Nm.map (Int.cast : ℤ → ℂ))ᴴ * bGram μ (fun j => secFun (b j)) (wgt m n) *
      Nm.map (Int.cast : ℤ → ℂ)) i i).re ≤ lam ^ 2 := by
    intro i
    rw [diag_conj_eq, ← bNormSq_eq_re μ _ _ (hint n _ b hb)]
    refine bNormSq_le_of_pts_of hcar _ _ fun z hz => ?_
    have hv : Nm.map (Int.cast : ℤ → ℂ) *ᵥ Pi.single i 1 =
        fun p => ((crd ⟨_, hwm (f i)⟩ p : ℤ) : ℂ) := by
      funext p
      simp [hNm, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, sum_secFun_eq' hb _ (hQ'h (f i)) _ (hcrd1 ⟨_, hwm (f i)⟩) z hz]
    have h1 := pt_small hFS (adtEnum_sum D (n - k₀) (f i).1) (Tf (f i).2) (hCt (f i).2) hz
    rw [hnk₀] at h1
    exact h1.trans (pow_le_pow_left₀ hCt0 (le_max_right _ _) 2)
  have key := neg_log_det_le hr hG' hG M hinj _ hfdet hA (by linarith) hnorm hsmall
  rw [neg_log_det_monoDiag] at key

  have hmono : Monotone (chiP D) := monotone_nat_of_le_succ fun n => by
    have := chiP_succ_sub_nonneg D n; linarith
  have hm := mul_le_mul_of_nonneg_left (hmono (show n - max kε k₀ ≤ n - kε by omega))
    (Nat.cast_nonneg (projDeg x e) : (0 : ℝ) ≤ projDeg x e)
  obtain ⟨hL0, hL⟩ := log_sqrt_bound D hT1 hn1
  have hll := log_le_div_mul hloglam hn1
  set R' := projDeg x e * (Finset.Nat.antidiagonalTuple (D + 1) (n - kε)).card
  set r := finrank ℤ (sec ℤ x n)
  have hrR : (R' : ℝ) ≤ r := by exact_mod_cast hr
  have hR0 : (0 : ℝ) ≤ R' := Nat.cast_nonneg _
  have hrb : (r : ℝ) ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by
    have h1 : (r : ℝ) ≤ (projDeg x e : ℝ) * (((n + k' + D).choose D : ℕ) : ℝ) := by
      exact_mod_cast hk' n
    rw [mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_left (choose_bound k' D hn1) (Nat.cast_nonneg _))
  have hX : 0 ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D := by positivity
  have hlogn : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h3 : (R' : ℝ) * Real.log A ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (hrR.trans hrb) hL0).trans (mul_le_mul_of_nonneg_left hL hX)
  have h4 : ((r : ℝ) - R') * Real.log lam ≤ (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      (n : ℝ) ^ D * (Real.log lam / Real.log 2 * Real.log (n + 1)) :=
    (mul_le_mul_of_nonneg_right (by linarith) hloglam).trans (mul_le_mul_of_nonneg_left hll hX)
  have h5 : (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) + Real.log lam / Real.log 2) * (n : ℝ) ^ D *
        Real.log (n + 1) = (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      ((1 / 2) * (Real.log T / Real.log 2 + D) * Real.log (n + 1)) +
      (projDeg x e : ℝ) * ((1 + k' + D : ℕ) : ℝ) ^ D * (n : ℝ) ^ D *
      (Real.log lam / Real.log 2 * Real.log (n + 1)) := by ring
  linarith

end

end ResChiSandwich

end GroundTheory.Heights₂.Heights.HilbertSamuel
