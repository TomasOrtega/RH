import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExponentialGluing.ExpNegGlueHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2Gluing.IntegralLeToReal
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.UnipotentVanishing.InfAtUnipInvEqZero

noncomputable section

open NumberField MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E.E3

namespace GlobalTheory.CompanionTheory.LocExponent

/- English proof (translation)
Establish `h` using `(isLittleO_pow_exp_pos_mul_atTop M (show 0 < 2 * ε by positivity)).tendsto_div_nhds_zero`. Establish `h2` using `h.const_mul ((1 + 2 * B) ^ M)`. Rewrite `h2` using `[mul_zero]`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 1] with t ht`.

Establish `h0 : 0 ≤ 1 + B * (1 + t)` using `by nlinarith`. Check the signs of the components of the expression. Use `filter_upwards [eventually_ge_atTop 1] with t ht`. Establish `h1 : 1 + B * (1 + t) ≤ (1 + 2 * B) * t` using `by nlinarith`. Establish `h0 : 0 ≤ 1 + B * (1 + t)` using `by nlinarith`.

Establish `hp` using `pow_le_pow_left₀ h0 h1 M`. Rewrite using `[Real.exp_neg, mul_comm (Real.exp (2 * ε * t))⁻¹, ← div_eq_mul_inv, ← mul_div_assoc]`. Conclude with `div_le_div_of_nonneg_right (by rwa [mul_pow] at hp) (Real.exp_pos _).le`.
-/
theorem tendsto_exp_mul_poly (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (M : ℕ) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * ε * t)) * (1 + B * (1 + t)) ^ M) atTop (𝓝 0) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop M (show 0 < 2 * ε by positivity)).tendsto_div_nhds_zero
  have h2 := h.const_mul ((1 + 2 * B) ^ M)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    positivity
  · filter_upwards [eventually_ge_atTop 1] with t ht
    have h1 : 1 + B * (1 + t) ≤ (1 + 2 * B) * t := by nlinarith
    have h0 : 0 ≤ 1 + B * (1 + t) := by nlinarith
    have hp := pow_le_pow_left₀ h0 h1 M
    rw [Real.exp_neg, mul_comm (Real.exp (2 * ε * t))⁻¹, ← div_eq_mul_inv, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by rwa [mul_pow] at hp) (Real.exp_pos _).le

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hF0 (funext h)`. Take `⟨Q, hQc, hQn⟩` from `exists_compact_mem_nhds g₀`.

Establish `hFc` using `hdecF.1`. Use `set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI`. Establish `hIpos : 0 < I`. Establish `hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ` using `(hFc.norm.pow 2).continuousOn.integrableOn_compact hQc`. Rewrite using `[hI, setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]`.

Establish `hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q)` using `(hFc.norm.pow 2).isOpen_support.inter isOpen_interior`. Establish `hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty` using `⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩`. Conclude with `lt_of_lt_of_le (hopen.measure_pos μ hne) (measure_mono (Set.inter_subset_inter_right _ interior_subset))`. Establish `hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ = Real.exp (2 * (c.re - ρ) * t) * I`. Introduce `t`.

Establish `hre : (c * (t : ℂ)).re = c.re * t` using `by simp`. Establish `hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2`. Introduce `g`. Rewrite using `[hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]`. Repeatedly rewrite using `[hpt]`.

Rewrite using `[integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `hdecF.2 Q hQc`. Rewrite `hlim` using `[tendsto_congr hval]`.

Assume the negation of the conclusion as `hge`. Use `push Not at hge`. Establish `hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I` using `by filter_upwards [eventually_ge_atTop 0] with t ht`. Establish `h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t)` using `Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])`. Use the polynomial consequences of the given equalities and inequalities.

Use `ge_of_tendsto hlim hev` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_lt_of_dec {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)
    {F : G → ℂ} (hdecF : PositivityTheory.Rg.Rs.JExpNegGlue.Dec μ ρ a F) (hF0 : F ≠ 0) {c : ℂ}
    (hFeq : ∀ (t : ℝ) g, F (a t * g) = Complex.exp (c * t) * F g) : c.re < ρ := by
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, F g₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (funext h)
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds g₀
  have hFc := hdecF.1
  set I := ∫ g in Q, ‖F g‖ ^ 2 ∂μ with hI
  have hIpos : 0 < I := by
    have hint : IntegrableOn (fun g => ‖F g‖ ^ 2) Q μ := (hFc.norm.pow 2).continuousOn.integrableOn_compact hQc
    rw [hI, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun g => by show (0 : ℝ) ≤ ‖F g‖ ^ 2; positivity) hint]
    have hopen : IsOpen (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q) :=
      (hFc.norm.pow 2).isOpen_support.inter isOpen_interior
    have hne : (Function.support (fun g => ‖F g‖ ^ 2) ∩ interior Q).Nonempty :=
      ⟨g₀, by simp [Function.mem_support, hg₀], mem_interior_iff_mem_nhds.2 hQn⟩
    exact lt_of_lt_of_le (hopen.measure_pos μ hne)
      (measure_mono (Set.inter_subset_inter_right _ interior_subset))
  have hval : ∀ t : ℝ, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖F (a t * g)‖ ^ 2 ∂μ =
      Real.exp (2 * (c.re - ρ) * t) * I := by
    intro t
    have hre : (c * (t : ℂ)).re = c.re * t := by simp
    have hpt : ∀ g, ‖F (a t * g)‖ ^ 2 = Real.exp (c.re * t) ^ 2 * ‖F g‖ ^ 2 := by
      intro g
      rw [hFeq, norm_mul, Complex.norm_exp, mul_pow, hre]
    simp_rw [hpt]
    rw [integral_const_mul, ← mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
    congr 2; ring
  have hlim := hdecF.2 Q hQc
  rw [tendsto_congr hval] at hlim
  by_contra hge
  push Not at hge
  have hev : ∀ᶠ t in atTop, I ≤ Real.exp (2 * (c.re - ρ) * t) * I := by
    filter_upwards [eventually_ge_atTop 0] with t ht
    have h1 : 1 ≤ Real.exp (2 * (c.re - ρ) * t) :=
      Real.one_le_exp (by nlinarith [mul_nonneg (sub_nonneg.2 hge) ht])
    nlinarith
  have := ge_of_tendsto hlim hev
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

omit [IsCMField E] in

/- English proof (translation)
Introduce `x`. Establish `hle : (ratGL E N).range ≤ An.lat E N` using `le_sup_left`. Use `le_trans ?_ (h x)` and prove the remaining obligations. Establish `hinj : Set.InjOn (Subgroup.inclusion hle) {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S}` using `(Subgroup.inclusion_injective hle).injOn`. Rewrite using `[← hinj.encard_image]`.

Use `Set.encard_le_encard ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Conclude with `hγ`.
-/
theorem mult_of_lat {S : Set (GA E N)} {n : ℕ}
    (h : ∀ x, {γ : An.lat E N | (γ : GA E N) * x ∈ S}.encard ≤ n) : Mult S n := by
  intro x
  have hle : (ratGL E N).range ≤ An.lat E N := le_sup_left
  refine le_trans ?_ (h x)
  have hinj : Set.InjOn (Subgroup.inclusion hle) {γ : (ratGL E N).range | (γ : GA E N) * x ∈ S} :=
    (Subgroup.inclusion_injective hle).injOn
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  exact hγ

omit [IsCMField E] in
/- English proof (translation)
Unfold `An.rho`. Establish `: (r : ℝ) ≤ N` using `by exact_mod_cast hrN.le`. Conclude with `mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)`.
-/
theorem rho_nonneg {r : ℕ} (hrN : r < N) : 0 ≤ An.rho E N r := by
  unfold An.rho
  have : (r : ℝ) ≤ N := by exact_mod_cast hrN.le
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 this)) two_pos.le)

/- English proof (translation)
Take `⟨D, hD, hD0⟩` from `GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)`. Take `⟨C₁, hC₁⟩` from `l2glue.count_le count_holds hr hrN hD hQ`. Take `⟨C, M, hCM⟩` from `hLoc μ hμ`. Take `⟨B, hB, hsz⟩` from `hSize E N (GroundTheory.Automorphic.AutomorphicForm.unipGL '' D) Q (hD.image GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL) hQ`. Establish `hρ : 0 ≤ An.rho E N r` using `rho_nonneg hrN`.

Use `⟨max C 0 * (max C₁ 0 + 1), B, M, by positivity, hB, fun t ht => ?_⟩` and prove the remaining obligations. Use `set e := Real.exp (2 * An.rho E N r * t) with he`. Use `set n : ℕ := ⌈C₁ * e⌉₊ with hn`. Use `set R : ℝ := B * (1 + t) with hR`. Establish `hR0 : 0 ≤ R` using `by positivity`.

Establish `hS` using `l2glue.isCompact_sset r t hD hQ`. Establish `hmult : Mult (l2glue.sset E N r t D Q) n` using `mult_of_lat (hC₁ t ht)`. Establish `hlog : ∀ g ∈ l2glue.sset E N r t D Q, logSize g ≤ R`. Introduce and unpack `_ ⟨⟨X, q⟩, ⟨hX, hq⟩, rfl⟩`. Establish `hx` using `hsz _ ⟨X, hX, rfl⟩ q hq (fun i : Fin N => if (i : ℕ) < r then t else 0)`.

Use `hx.trans (mul_le_mul_of_nonneg_left ?_ hB)` and prove the remaining obligations. Establish `: ‖fun i : Fin N => if (i : ℕ) < r then t else 0‖ ≤ t`. Use `(pi_norm_le_iff_of_nonneg ht).2 fun i => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[Real.norm_of_nonneg ht]`.

Simplify using `using ht`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `hCM _ hS n R hR0 hmult hlog`. Establish `h2` using `l2glue.swap μ φ hφ r t hD hD0 hQ`. Establish `h1` using `l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR E N r t * g))`.

Establish `hP : 0 ≤ (1 + R) ^ M` using `by positivity`. Establish `he1 : 1 ≤ e` using `Real.one_le_exp (by positivity)`. Establish `hnle : (n : ℝ) ≤ (max C₁ 0 + 1) * e`. Establish `h6 : (n : ℝ) ≤ ⌈max C₁ 0 * e⌉₊`. Conclude with `Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))` after adjusting the coercions.

Establish `h7` using `(Nat.ceil_lt_add_one (show 0 ≤ max C₁ 0 * e by positivity)).le`. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : ENNReal.ofReal (C * n * (1 + R) ^ M) ≤ ENNReal.ofReal (max C 0 * n * (1 + R) ^ M)`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hP)` and prove the remaining obligations. Establish `h5 : (∫⁻ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ₑ ^ 2 ∂μ).toReal ≤ max C 0 * n * (1 + R) ^ M`.

Use `ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans (h3.trans h4))` as an intermediate fact. Rewrite `this` using `[ENNReal.toReal_ofReal (by positivity)]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integral_ctn_le (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {Q : Set (GA E N)} (hQ : IsCompact Q) :
    ∃ (K B : ℝ) (M : ℕ), 0 ≤ K ∧ 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ ≤
        K * (Real.exp (2 * An.rho E N r * t) * (1 + B * (1 + t)) ^ M) := by
  obtain ⟨D, hD, hD0⟩ := GroundTheory.Automorphic.AutomorphicForm.exists_isCompact_superset_unipFundamentalDomain
    (K := E) (n := N) (r := r)
  obtain ⟨C₁, hC₁⟩ := l2glue.count_le count_holds hr hrN hD hQ
  obtain ⟨C, M, hCM⟩ := hLoc μ hμ
  obtain ⟨B, hB, hsz⟩ := hSize E N (GroundTheory.Automorphic.AutomorphicForm.unipGL '' D) Q
    (hD.image GroundTheory.Automorphic.AutomorphicForm.continuous_unipGL) hQ
  have hρ : 0 ≤ An.rho E N r := rho_nonneg hrN
  refine ⟨max C 0 * (max C₁ 0 + 1), B, M, by positivity, hB, fun t ht => ?_⟩
  set e := Real.exp (2 * An.rho E N r * t) with he
  set n : ℕ := ⌈C₁ * e⌉₊ with hn
  set R : ℝ := B * (1 + t) with hR
  have hR0 : 0 ≤ R := by positivity
  have hS := l2glue.isCompact_sset r t hD hQ
  have hmult : Mult (l2glue.sset E N r t D Q) n := mult_of_lat (hC₁ t ht)
  have hlog : ∀ g ∈ l2glue.sset E N r t D Q, logSize g ≤ R := by
    rintro _ ⟨⟨X, q⟩, ⟨hX, hq⟩, rfl⟩
    have hx := hsz _ ⟨X, hX, rfl⟩ q hq (fun i : Fin N => if (i : ℕ) < r then t else 0)
    refine hx.trans (mul_le_mul_of_nonneg_left ?_ hB)
    have : ‖fun i : Fin N => if (i : ℕ) < r then t else 0‖ ≤ t := by
      refine (pi_norm_le_iff_of_nonneg ht).2 fun i => ?_
      split_ifs
      · rw [Real.norm_of_nonneg ht]
      · simpa using ht
    linarith
  have h3 := hCM _ hS n R hR0 hmult hlog
  have h2 := l2glue.swap μ φ hφ r t hD hD0 hQ
  have h1 := l2glue.integral_le_toReal (μ.restrict Q) (fun g => An.ctn r φ (An.aR E N r t * g))
  have hP : 0 ≤ (1 + R) ^ M := by positivity
  have he1 : 1 ≤ e := Real.one_le_exp (by positivity)
  have hnle : (n : ℝ) ≤ (max C₁ 0 + 1) * e := by
    have h6 : (n : ℝ) ≤ ⌈max C₁ 0 * e⌉₊ := by
      exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by linarith))
    have h7 := (Nat.ceil_lt_add_one (show 0 ≤ max C₁ 0 * e by positivity)).le
    nlinarith
  have h4 : ENNReal.ofReal (C * n * (1 + R) ^ M) ≤ ENNReal.ofReal (max C 0 * n * (1 + R) ^ M) := by
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hP)
  have h5 : (∫⁻ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ₑ ^ 2 ∂μ).toReal ≤ max C 0 * n * (1 + R) ^ M := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h2.trans (h3.trans h4))
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := h1
    _ ≤ _ := h5
    _ ≤ max C 0 * ((max C₁ 0 + 1) * e) * (1 + R) ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnle (by positivity)) hP
    _ = _ := by ring

/- English proof (translation)
Take `⟨K, B, M, hK, hB, hb⟩` from `integral_ctn_le hSize hφ hLoc hr hrN μ hQ`. Establish `hlim` using `(tendsto_exp_mul_poly B ε hB hε M).const_mul K`. Rewrite `hlim` using `[mul_zero]`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)) ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop 0] with t ht`.

Establish `h` using `mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-(2 * (An.rho E N r + ε) * t))).le`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hee : Real.exp (-(2 * (An.rho E N r + ε) * t)) * Real.exp (2 * An.rho E N r * t) = Real.exp (-(2 * ε * t))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hee]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tendsto_ctn (hSize : SizeT) {φ : GA E N → ℂ} (hφ : Continuous φ) (hLoc : Loc φ) {r : ℕ}
    (hr : 0 < r) (hrN : r < N) (μ : Measure (GA E N)) [hμ : μ.IsHaarMeasure] {ε : ℝ} (hε : 0 < ε)
    {Q : Set (GA E N)} (hQ : IsCompact Q) :
    Tendsto (fun t : ℝ => Real.exp (-(2 * (An.rho E N r + ε) * t)) *
      ∫ g in Q, ‖An.ctn r φ (An.aR E N r t * g)‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨K, B, M, hK, hB, hb⟩ := integral_ctn_le hSize hφ hLoc hr hrN μ hQ
  have hlim := (tendsto_exp_mul_poly B ε hB hε M).const_mul K
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have h := mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos (-(2 * (An.rho E N r + ε) * t))).le
  refine h.trans (le_of_eq ?_)
  have hee : Real.exp (-(2 * (An.rho E N r + ε) * t)) * Real.exp (2 * An.rho E N r * t) = Real.exp (-(2 * ε * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← hee]; ring

end GlobalTheory.CompanionTheory.LocExponent

namespace GlobalTheory.CompanionTheory.LocExponent

open PositivityTheory.Rg.Rs.JExpNegGlue in

/- English proof (translation)
Introduce `hSize E _ _ _ N φ hA hLoc r hr0 hrN c hc`. Take `⟨haR, -, -, hct⟩` from `dict_holds E N`. Establish `hctn` using `(hct φ hA r hr0 hrN).2`. Take `⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩` from `hc`. Take `⟨c₀, -, hF₀eq⟩` from `hctn F₀ hF₀`.

Substitute `hF₀eq` using the available equality. Establish `hφc : Continuous φ.1` using `GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level`. Set `μ : Measure (GA E N)` to `Measure.haar`. Establish `: μ.IsHaarMeasure` using `inferInstance`. Use `set a : ℝ → GA E N := aT E N r with ha`.

Establish `hcomm : ∀ s t, a s * a t = a t * a s` using `aT_comm E N r`. Establish `hlt : ∀ ε : ℝ, 0 < ε → c.re < An.rho E N r + ε`. Introduce `ε hε`. Establish `hdec_ctn : Dec μ (An.rho E N r + ε) a (An.ctn r φ.1)`. Use `⟨continuous_ctn r hφc, fun Q hQ => ?_⟩` and prove the remaining obligations.

Establish `h` using `tendsto_ctn hSize hφc hLoc hr0 hrN μ hε hQ`. Simplify using `only [ha, haR]`. Conclude with `h`. Establish `hdecF : Dec μ (An.rho E N r + ε) a F`. Use `Submodule.span_induction (p := fun H _ => Dec μ (An.rho E N r + ε) a H) ?_ (dec_zero μ _ a) (fun x y _ _ hx hy => dec_add μ _ a hx hy) (fun b x _ hx => dec_smul μ _ a b hx) hFspan` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, rfl⟩`. Use `dec_smul μ _ a c₀ (dec_translate μ _ a hcomm s hdec_ctn) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `re_lt_of_dec μ _ a hdecF hF0 hFeq`.

Establish `hle : c.re ≤ An.rho E N r` using `le_of_forall_pos_le_add fun ε hε => (hlt ε hε).le`. Establish `hd : (0 : ℝ) < Module.finrank ℚ E` using `Nat.cast_pos.2 Module.finrank_pos`. Rewrite `hle` using `[An.rho]`. Unfold `pE`. Establish `: c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2`.

Rewrite using `[div_le_iff₀ hd]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem locNonPosGlue_holds : LocNonPosGlue := by
  intro hSize E _ _ _ N φ hA hLoc r hr0 hrN c hc
  obtain ⟨haR, -, -, hct⟩ := dict_holds E N
  have hctn := (hct φ hA r hr0 hrN).2
  obtain ⟨F₀, hF₀, F, hFspan, hF0, hFeq⟩ := hc
  obtain ⟨c₀, -, hF₀eq⟩ := hctn F₀ hF₀
  subst hF₀eq
  have hφc : Continuous φ.1 := GlobalTheory.CompanionTheory.ConstTerm.continuous_of_isOpen_stab φ hA.level
  let μ : Measure (GA E N) := Measure.haar
  have : μ.IsHaarMeasure := inferInstance
  set a : ℝ → GA E N := aT E N r with ha
  have hcomm : ∀ s t, a s * a t = a t * a s := aT_comm E N r
  have hlt : ∀ ε : ℝ, 0 < ε → c.re < An.rho E N r + ε := by
    intro ε hε
    have hdec_ctn : Dec μ (An.rho E N r + ε) a (An.ctn r φ.1) := by
      refine ⟨continuous_ctn r hφc, fun Q hQ => ?_⟩
      have h := tendsto_ctn hSize hφc hLoc hr0 hrN μ hε hQ
      simp only [ha, haR]
      exact h
    have hdecF : Dec μ (An.rho E N r + ε) a F := by
      refine Submodule.span_induction (p := fun H _ => Dec μ (An.rho E N r + ε) a H) ?_ (dec_zero μ _ a)
        (fun x y _ _ hx hy => dec_add μ _ a hx hy) (fun b x _ hx => dec_smul μ _ a b hx) hFspan
      rintro _ ⟨s, rfl⟩
      convert dec_smul μ _ a c₀ (dec_translate μ _ a hcomm s hdec_ctn) using 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul]
    exact re_lt_of_dec μ _ a hdecF hF0 hFeq
  have hle : c.re ≤ An.rho E N r := le_of_forall_pos_le_add fun ε hε => (hlt ε hε).le
  have hd : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  rw [An.rho] at hle
  unfold pE
  have : c.re / (Module.finrank ℚ E : ℝ) ≤ (r : ℝ) * ((N : ℝ) - r) / 2 := by
    rw [div_le_iff₀ hd]; linarith
  linarith

end GlobalTheory.CompanionTheory.LocExponent

end
