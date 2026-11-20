import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ConjKappa
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaSummableAndDeterminesTestFn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledGaussianKernelDiagonalTranslationInvarianStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensityStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeSpanMembership
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical Pointwise

namespace GlobalTheory.Ker.Mean

section Abstract

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/- English proof (translation)
Set `b` to `Module.Basis.ofSpan hL`. Establish `hb : Set.range b ⊆ L` using `Module.Basis.ofSpan_subset hL`. Use `haveI := FiniteDimensional.fintypeBasisIndex b`. Establish `hS : μ (ZSpan.fundamentalDomain b) < ⊤` using `(ZSpan.fundamentalDomain_isBounded b).measure_lt_top`. Use `lt_of_le_of_lt ?_ hS` and prove the remaining obligations.

Rewrite using `[hF.measure_eq_tsum (ZSpan.fundamentalDomain b)]`. Use `le_trans (measure_mono ?_) (measure_iUnion_le _)` and prove the remaining obligations. Introduce `v hv`. Establish `h1 : (ZSpan.floor b v : V) ∈ L`. Establish `: Submodule.span ℤ (Set.range b) ≤ L.toIntSubmodule` using `Submodule.span_le.2 hb`.

Conclude with `this (ZSpan.floor b v).2`. Use `Set.mem_iUnion.2 ⟨⟨_, h1⟩, ⟨ZSpan.fract b v, ZSpan.fract_mem_fundamentalDomain b v, ?_⟩, hv⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ZSpan.floor b v : V) + ZSpan.fract b v = v`. Rewrite using `[ZSpan.fract_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem measure_lt_top_of_span (L : AddSubgroup V) [Countable L]
    (hL : ⊤ ≤ Submodule.span ℝ (L : Set V)) {F : Set V} (hF : IsAddFundamentalDomain L F μ) :
    μ F < ⊤ := by
  let b := Module.Basis.ofSpan hL
  have hb : Set.range b ⊆ L := Module.Basis.ofSpan_subset hL
  haveI := FiniteDimensional.fintypeBasisIndex b
  have hS : μ (ZSpan.fundamentalDomain b) < ⊤ :=
    (ZSpan.fundamentalDomain_isBounded b).measure_lt_top
  refine lt_of_le_of_lt ?_ hS
  rw [hF.measure_eq_tsum (ZSpan.fundamentalDomain b)]
  refine le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro v hv
  have h1 : (ZSpan.floor b v : V) ∈ L := by
    have : Submodule.span ℤ (Set.range b) ≤ L.toIntSubmodule := Submodule.span_le.2 hb
    exact this (ZSpan.floor b v).2
  refine Set.mem_iUnion.2 ⟨⟨_, h1⟩, ⟨ZSpan.fract b v, ZSpan.fract_mem_fundamentalDomain b v, ?_⟩, hv⟩
  change (ZSpan.floor b v : V) + ZSpan.fract b v = v
  rw [ZSpan.fract_apply]; abel

/- English proof (translation)
Establish `h1 : IsAddFundamentalDomain L (t +ᵥ F) μ` using `hF.vadd_of_comm t`. Establish `h2` using `hF.setIntegral_eq h1 (f := χ) (fun l x => by`. Express the relevant statement in the definitionally equal form `χ ((l : V) + x) = χ x`. Rewrite using `[hχ, hL _ l.2, one_mul])`. Establish `h3 : ∫ w in t +ᵥ F, χ w ∂μ = ∫ w in F, χ (t + w) ∂μ`.

Use `(measurePreserving_add_left μ t).setIntegral_image_emb (measurableEmbedding_addLeft t) χ F` as an intermediate fact. Conclude with `this`. Simplify using `only [hχ] at h3`. Rewrite `h3` using `[integral_const_mul, ← h2]`. Establish `: (χ t - 1) * ∫ w in F, χ w ∂μ = 0` using `by rw [sub_mul, ← h3]; ring`.

Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht)`.
-/
theorem integral_char_eq_zero (L : AddSubgroup V) [Countable L] {F : Set V}
    (hF : IsAddFundamentalDomain L F μ) (χ : V → ℂ) (hχ : ∀ v w, χ (v + w) = χ v * χ w)
    (hL : ∀ l ∈ L, χ l = 1) {t : V} (ht : χ t ≠ 1) : ∫ w in F, χ w ∂μ = 0 := by
  have h1 : IsAddFundamentalDomain L (t +ᵥ F) μ := hF.vadd_of_comm t
  have h2 := hF.setIntegral_eq h1 (f := χ) (fun l x => by
    change χ ((l : V) + x) = χ x
    rw [hχ, hL _ l.2, one_mul])
  have h3 : ∫ w in t +ᵥ F, χ w ∂μ = ∫ w in F, χ (t + w) ∂μ := by
    have := (measurePreserving_add_left μ t).setIntegral_image_emb
      (measurableEmbedding_addLeft t) χ F
    exact this
  simp only [hχ] at h3
  rw [integral_const_mul, ← h2] at h3
  have : (χ t - 1) * ∫ w in F, χ w ∂μ = 0 := by rw [sub_mul, ← h3]; ring
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht)

/- English proof (translation)
Establish `hfin` using `measure_lt_top_of_span L hL hF`. Establish `hpos : μ F ≠ 0` using `hF.measure_ne_zero (NeZero.ne μ)`. Use `haveI : IsFiniteMeasure (μ.restrict F) := isFiniteMeasure_restrict.2 hfin.ne`. Establish `hre : ((μ F).toReal : ℂ) ≠ 0`. Conclude with `ENNReal.toReal_ne_zero.2 ⟨hpos, hfin.ne⟩` after adjusting the coercions.

Rewrite using `[← integral_tsum_of_summable_integral_norm]`. Rewrite using `[tsum_eq_single i₀]`. Simplify using `only [h₀, mul_one, integral_const, Measure.real, Measure.restrict_apply_univ, real_smul]`. Clear the denominators using the available nonvanishing facts. Introduce `i hi`.

Distinguish the cases in `h : c i = 0`. Simplify using `[h]`. Take `⟨t, ht⟩` from `h₁ i hi`. Rewrite using `[integral_const_mul, integral_char_eq_zero L hF (χ i) (hχ i) (hχL i h) ht, mul_zero]`. Introduce `i`.

Conclude with `Integrable.of_bound (continuous_const.mul (hcont i)).aestronglyMeasurable ‖c i‖ (Filter.Eventually.of_forall fun w => by simp [hn])`. Simplify using `only [norm_mul, hn, mul_one, integral_const, smul_eq_mul]`. Conclude with `hc.mul_left _`.
-/
theorem mean_tsum {ι : Type} [Countable ι] (L : AddSubgroup V) [Countable L]
    (hL : ⊤ ≤ Submodule.span ℝ (L : Set V)) {F : Set V} (hF : IsAddFundamentalDomain L F μ)
    (c : ι → ℂ) (hc : Summable fun i => ‖c i‖) (χ : ι → V → ℂ) (hcont : ∀ i, Continuous (χ i))
    (hn : ∀ i v, ‖χ i v‖ = 1) (hχ : ∀ i v w, χ i (v + w) = χ i v * χ i w)
    (hχL : ∀ i, c i ≠ 0 → ∀ l ∈ L, χ i l = 1) (i₀ : ι) (h₀ : ∀ v, χ i₀ v = 1)
    (h₁ : ∀ i, i ≠ i₀ → ∃ t, χ i t ≠ 1) :
    ((μ F).toReal : ℂ)⁻¹ * ∫ w in F, ∑' i, c i * χ i w ∂μ = c i₀ := by
  have hfin := measure_lt_top_of_span L hL hF
  have hpos : μ F ≠ 0 := hF.measure_ne_zero (NeZero.ne μ)
  haveI : IsFiniteMeasure (μ.restrict F) := isFiniteMeasure_restrict.2 hfin.ne
  have hre : ((μ F).toReal : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨hpos, hfin.ne⟩
  rw [← integral_tsum_of_summable_integral_norm]
  · rw [tsum_eq_single i₀]
    · simp only [h₀, mul_one, integral_const, Measure.real, Measure.restrict_apply_univ,
        real_smul]
      field_simp
    · intro i hi
      by_cases h : c i = 0
      · simp [h]
      · obtain ⟨t, ht⟩ := h₁ i hi
        rw [integral_const_mul, integral_char_eq_zero L hF (χ i) (hχ i) (hχL i h) ht, mul_zero]
  · intro i
    exact Integrable.of_bound (continuous_const.mul (hcont i)).aestronglyMeasurable ‖c i‖
      (Filter.Eventually.of_forall fun w => by simp [hn])
  · simp only [norm_mul, hn, mul_one, integral_const, smul_eq_mul]
    exact hc.mul_left _

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (idx : Fin g ≃ X.Ψ × Fin r) {n : ℕ}

/- English proof (translation)
Establish `e : (aLin X x₁ x₂ τ)⁻¹ * aLin X x₁ x₂ τ = 1` using `nonsing_inv_mul _ h.isUnit`. Simplify using `only [dblz', DblPer.of_row]`. Rewrite using `[← smul_add, ← add_vecMul]`. Use `congr 2`. Use `conv_rhs => rw [← one_mulVec (w τ k), ← e, ← mulVec_mulVec, ← mulVec_add]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Simplify using `only [zR, Equiv.apply_symm_apply, Pi.add_apply]`. Distinguish the cases in `hc : (c : ℕ) < X.p0`. Simplify using `only [if_pos hc, hermC, map_sum, map_mul, conj_conj, DblPer.conj_Gm, mulVec, dotProduct, aLin, of_apply, Finset.sum_mul, FD.col, mat, Pi.add_apply]`.

Rewrite using `[Finset.sum_comm (f := fun i j => τ.1 (X.Gm i j) * conj (x₂ τ j c) * w τ k i), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [if_neg hc, mulVec, dotProduct, aLin, of_apply, Pi.add_apply]`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem dblz'_shift (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (h : (aLin X x₁ x₂ τ).det ≠ 0)
    (a b w : WR X n) (k : Fin n) :
    dblz' X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i)) τ k =
      dblz' X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) τ k +
        (τ.1 X.κ0 / 2) • (w τ k ᵥ* X.Gm.map τ.1) := by
  have e : (aLin X x₁ x₂ τ)⁻¹ * aLin X x₁ x₂ τ = 1 := nonsing_inv_mul _ h.isUnit
  simp only [dblz', DblPer.of_row]
  rw [← smul_add, ← add_vecMul]
  congr 2
  conv_rhs => rw [← one_mulVec (w τ k), ← e, ← mulVec_mulVec, ← mulVec_add]
  congr 1
  funext c
  simp only [zR, Equiv.apply_symm_apply, Pi.add_apply]
  by_cases hc : (c : ℕ) < X.p0
  · simp only [if_pos hc, hermC, map_sum, map_mul, conj_conj, DblPer.conj_Gm, mulVec, dotProduct,
      aLin, of_apply, Finset.sum_mul, FD.col, mat, Pi.add_apply]
    rw [Finset.sum_comm (f := fun i j => τ.1 (X.Gm i j) * conj (x₂ τ j c) * w τ k i),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [if_neg hc, mulVec, dotProduct, aLin, of_apply, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `e : (aAnti X x₁ x₂ τ)⁻¹ * aAnti X x₁ x₂ τ = 1` using `nonsing_inv_mul _ h.isUnit`. Simplify using `only [dblz, DblPer.of_row]`. Rewrite using `[← smul_add, ← mulVec_add]`. Use `congr 2`. Use `conv_rhs => rw [← one_mulVec (star (w τ k)), ← e, ← mulVec_mulVec, ← mulVec_add]`.

Use `congr 1`. Use function extensionality and compare the values at `c`. Simplify using `only [zR, Equiv.apply_symm_apply, Pi.add_apply]`. Distinguish the cases in `hc : (c : ℕ) < X.p0`. Simplify using `only [if_pos hc, hermC, map_add, mulVec, dotProduct, aAnti, of_apply, Finset.sum_mul, FD.col, mat, Pi.add_apply, Pi.star_apply, RCLike.star_def]`.

Rewrite using `[Finset.sum_comm (f := fun i j => x₁ τ j c * τ.1 (X.Gm j i) * conj (w τ k i)), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`. Simplify using `only [if_neg hc, mulVec, dotProduct, aAnti, of_apply, Pi.add_apply, map_sum, map_mul, map_add, Pi.star_apply, RCLike.star_def]`.

Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem dblz_shift (x₁ x₂ : Frame X.Ψ r) (τ : X.Ψ) (h : (aAnti X x₁ x₂ τ).det ≠ 0)
    (a b w : WR X n) (k : Fin n) :
    dblz X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i)) τ k =
      dblz X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) τ k +
        (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ star (w τ k)) := by
  have e : (aAnti X x₁ x₂ τ)⁻¹ * aAnti X x₁ x₂ τ = 1 := nonsing_inv_mul _ h.isUnit
  simp only [dblz, DblPer.of_row]
  rw [← smul_add, ← mulVec_add]
  congr 2
  conv_rhs => rw [← one_mulVec (star (w τ k)), ← e, ← mulVec_mulVec, ← mulVec_add]
  congr 1
  funext c
  simp only [zR, Equiv.apply_symm_apply, Pi.add_apply]
  by_cases hc : (c : ℕ) < X.p0
  · simp only [if_pos hc, hermC, map_add, mulVec, dotProduct,
      aAnti, of_apply, Finset.sum_mul, FD.col, mat, Pi.add_apply, Pi.star_apply, RCLike.star_def]
    rw [Finset.sum_comm (f := fun i j => x₁ τ j c * τ.1 (X.Gm j i) * conj (w τ k i)),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [if_neg hc, mulVec, dotProduct, aAnti, of_apply, Pi.add_apply, map_sum, map_mul,
      map_add, Pi.star_apply, RCLike.star_def]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Unfold `expo EFR`. Use `push_cast`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[dblz_shift X idx x₁ x₂ τ (h' τ), dblz'_shift X idx x₁ x₂ τ (h τ), dotProduct_add, add_dotProduct, Complex.re_eq_add_conj]`. Establish `e1 : (fun a => τ.1 (x k a)) ⬝ᵥ (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ star (w τ k)) = τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k)`. Simplify using `only [hermC, embR, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_neg, map_div₀, map_ofNat, map_apply, Pi.star_apply, RCLike.star_def]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Establish `e2 : ((τ.1 X.κ0 / 2) • (w τ k ᵥ* X.Gm.map τ.1)) ⬝ᵥ (fun a => conj (τ.1 (x k a))) = conj (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k))`. Simplify using `only [hermC, embR, vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, map_neg, map_div₀, map_ofNat, map_apply, map_sum, map_mul, conj_conj, DblPer.conj_Gm, DblPer.conj_kappa]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expo_shift (x₁ x₂ : Frame X.Ψ r) (h : ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0)
    (h' : ∀ τ, (aAnti X x₁ x₂ τ).det ≠ 0) (Z : CM X.Ψ r r) (a b w : WR X n)
    (x : Matrix (Fin n) (Fin r) E) :
    expo X.Ψ x Z
      (dblz X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i)))
      (dblz' X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) =
    expo X.Ψ x Z (dblz X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)))
      (dblz' X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))) +
      (EFR X (embR X x) w : ℝ) := by
  unfold expo EFR
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dblz_shift X idx x₁ x₂ τ (h' τ), dblz'_shift X idx x₁ x₂ τ (h τ), dotProduct_add,
    add_dotProduct, Complex.re_eq_add_conj]
  have e1 : (fun a => τ.1 (x k a)) ⬝ᵥ (-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ star (w τ k)) =
      τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k) := by
    simp only [hermC, embR, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      map_neg, map_div₀, map_ofNat, map_apply, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have e2 : ((τ.1 X.κ0 / 2) • (w τ k ᵥ* X.Gm.map τ.1)) ⬝ᵥ (fun a => conj (τ.1 (x k a))) =
      conj (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k)) := by
    simp only [hermC, embR, vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      Finset.sum_mul, map_neg, map_div₀, map_ofNat, map_apply, map_sum, map_mul, conj_conj,
      DblPer.conj_Gm, DblPer.conj_kappa]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [e1, e2]
  ring

/- English proof (translation)
Simplify using `only [EFR, hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_re]`.
-/
theorem EFR_add_right (u v w : WR X n) : EFR X u (v + w) = EFR X u v + EFR X u w := by
  simp only [EFR, hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_re]

/- English proof (translation)
Simplify using `only [EFR, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: hermC τ.1 X.Gm (u τ k) ((t • v) τ k) = t * hermC τ.1 X.Gm (u τ k) (v τ k)`. Simplify using `only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[this, mul_left_comm _ (t : ℂ), re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EFR_smul_right (t : ℝ) (u v : WR X n) : EFR X u (t • v) = t * EFR X u v := by
  simp only [EFR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have : hermC τ.1 X.Gm (u τ k) ((t • v) τ k) = t * hermC τ.1 X.Gm (u τ k) (v τ k) := by
    simp only [hermC, Pi.smul_apply, real_smul, map_mul, conj_ofReal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this, mul_left_comm _ (t : ℂ), re_ofReal_mul]
  ring

/- English proof (translation)
Unfold `EFR hermC`. Use `fun_prop`.
-/
theorem continuous_EFR (u : WR X n) : Continuous (EFR X u) := by
  unfold EFR hermC
  fun_prop

/- English proof (translation)
Set `w : WR X n` to `fun τ k => τ.1 (-(X.κ0 / 2)) • (embR X x τ k ᵥ* X.Gm.map τ.1)`. Use `⟨w, fun h => hx ?_⟩` and prove the remaining obligations. Establish `e : ∀ τ k, (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k)).re = ∑ b, normSq (w τ k b)`. Introduce `τ k`. Establish `: τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k) = ∑ b, w τ k b * conj (w τ k b)`.

Rewrite using `[hermC, Finset.sum_comm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, ← mul_assoc]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Simplify using `only [mul_conj, re_sum, ofReal_re]`. Establish `nn : ∀ τ k, 0 ≤ ∑ b, normSq (w τ k b)` using `fun τ k => Finset.sum_nonneg fun _ _ => normSq_nonneg _`. Simplify using `only [EFR, e] at h`. Choose the witnesses or unpack the hypotheses as in `⟨τ⟩ : Nonempty X.Ψ := by`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `⟨⟨σ, hσ⟩⟩`. Conclude with `⟨⟨_, not_not.1 fun h' => hσ ((X.cmType σ).2 h')⟩⟩`. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg fun τ _ => Finset.sum_nonneg fun k _ => mul_nonneg zero_le_two (nn τ k)).1 h τ (Finset.mem_univ _)`. Use extensionality with `k a`.

Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg zero_le_two (nn τ k)).1 h1 k (Finset.mem_univ _)`. Establish `h3 : w τ k = 0`. Use function extensionality and compare the values at `b`. Conclude with `normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => normSq_nonneg _).1 ((mul_eq_zero.1 h2).resolve_left two_ne_zero) b (Finset.mem_univ _))`. Establish `hk : τ.1 (-(X.κ0 / 2)) ≠ 0` using `(map_ne_zero τ.1).2 (neg_ne_zero.2 (div_ne_zero (DblPer.kappa_ne X) two_ne_zero))`.

Establish `h4` using `eq_zero_of_vecMul_eq_zero (DblPer.det_Gm X τ.1) ((smul_eq_zero.1 h3).resolve_left hk)`. Conclude with `(map_eq_zero τ.1).1 (congrFun h4 a)`.
-/
theorem exists_EFR_ne (x : Matrix (Fin n) (Fin r) E) (hx : x ≠ 0) :
    ∃ w, EFR X (embR X x) w ≠ 0 := by
  let w : WR X n := fun τ k => τ.1 (-(X.κ0 / 2)) • (embR X x τ k ᵥ* X.Gm.map τ.1)
  refine ⟨w, fun h => hx ?_⟩
  have e : ∀ τ k, (τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k)).re =
      ∑ b, normSq (w τ k b) := by
    intro τ k
    have : τ.1 (-(X.κ0 / 2)) * hermC τ.1 X.Gm (embR X x τ k) (w τ k) =
        ∑ b, w τ k b * conj (w τ k b) := by
      rw [hermC, Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Finset.sum_mul, ← mul_assoc]
      rfl
    rw [this]
    simp only [mul_conj, re_sum, ofReal_re]
  have nn : ∀ τ k, 0 ≤ ∑ b, normSq (w τ k b) :=
    fun τ k => Finset.sum_nonneg fun _ _ => normSq_nonneg _
  simp only [EFR, e] at h
  obtain ⟨τ⟩ : Nonempty X.Ψ := by
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hσ : σ ∈ X.Ψ
    · exact ⟨⟨σ, hσ⟩⟩
    · exact ⟨⟨_, not_not.1 fun h' => hσ ((X.cmType σ).2 h')⟩⟩
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg zero_le_two (nn τ k)).1 h τ (Finset.mem_univ _)
  ext k a
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg zero_le_two (nn τ k)).1 h1 k (Finset.mem_univ _)
  have h3 : w τ k = 0 := by
    funext b
    exact normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => normSq_nonneg _).1
      ((mul_eq_zero.1 h2).resolve_left two_ne_zero) b (Finset.mem_univ _))
  have hk : τ.1 (-(X.κ0 / 2)) ≠ 0 :=
    (map_ne_zero τ.1).2 (neg_ne_zero.2 (div_ne_zero (DblPer.kappa_ne X) two_ne_zero))
  have h4 := eq_zero_of_vecMul_eq_zero (DblPer.det_Gm X τ.1)
    ((smul_eq_zero.1 h3).resolve_left hk)
  exact (map_eq_zero τ.1).1 (congrFun h4 a)

/- English proof (translation)
Use function extensionality and compare the values at `τ k a`. Simplify using `[embR]`.
-/
theorem embR_nsmul (m : ℕ) (y : Matrix (Fin n) (Fin r) E) :
    embR X ((m : E) • y) = m • embR X y := by
  funext τ k a
  simp [embR]

instance countable_latR (N : ℕ) : Countable (latR X n N) := by
  let f : Matrix (Fin n) (Fin r) E →+ WR X n :=
    AddMonoidHom.mk' (embR X) fun y y' => by funext τ k a; simp [embR]
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have h : latR X n N ≤ f.range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨y, -, rfl⟩
    exact ⟨(N : E) • y, embR_nsmul X N y⟩
  have hc : Countable (Matrix (Fin n) (Fin r) E) := inferInstanceAs (Countable (Fin n → Fin r → E))
  exact ((Set.countable_range f).mono h).to_subtype

/- English proof (translation)
Use `choose f hf hm using fun i => LatticeSpanMembership.exists_nat_smul_mem (X := X) (v i)`. Use `⟨∏ i, f i, Finset.prod_pos fun i _ => hf i, fun i => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem f (Finset.mem_univ i)`. Rewrite using `[hc, mul_comm, Nat.cast_mul, mul_smul]`. Conclude with `Base.nat_smul_mem _ _ (hm i)`.
-/
theorem exists_common {ι : Type} [Fintype ι] (v : ι → Fin r → E) :
    ∃ M : ℕ, 0 < M ∧ ∀ i, (M : E) • v i ∈ X.Λ := by
  choose f hf hm using fun i => LatticeSpanMembership.exists_nat_smul_mem (X := X) (v i)
  refine ⟨∏ i, f i, Finset.prod_pos fun i _ => hf i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  rw [hc, mul_comm, Nat.cast_mul, mul_smul]
  exact Base.nat_smul_mem _ _ (hm i)

/- English proof (translation)
Introduce `v _`. Use `(Submodule.closed_of_finiteDimensional _).closure_subset_iff.2 ?_ (hd v)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Take `⟨M, hM, hy⟩` from `exists_common X fun k => y k`. Establish `h1 : N • embR X ((M : E) • y) ∈ latR X n N` using `AddSubgroup.subset_closure ⟨_, hy, rfl⟩`.

Establish `h2` using `Submodule.smul_mem _ ((N : ℝ) * M)⁻¹ (Submodule.subset_span (R := ℝ) h1)`. Rewrite `h2` using `[embR_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (by positivity), one_smul]`. Conclude with `h2`.
-/
theorem span_latR (hd : DenseRange (embR X (n := n))) {N : ℕ} (hN : 0 < N) :
    ⊤ ≤ Submodule.span ℝ (latR X n N : Set (WR X n)) := by
  intro v _
  refine (Submodule.closed_of_finiteDimensional _).closure_subset_iff.2 ?_ (hd v)
  rintro _ ⟨y, rfl⟩
  obtain ⟨M, hM, hy⟩ := exists_common X fun k => y k
  have h1 : N • embR X ((M : E) • y) ∈ latR X n N := AddSubgroup.subset_closure ⟨_, hy, rfl⟩
  have h2 := Submodule.smul_mem _ ((N : ℝ) * M)⁻¹ (Submodule.subset_span (R := ℝ) h1)
  rw [embR_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul,
    mul_assoc, inv_mul_cancel₀ (by positivity), one_smul] at h2
  exact h2

/- English proof (translation)
Take `⟨M, hM, h⟩` from `exists_common X fun a : Fin r => Pi.single a (1 : E)`. Use `⟨M, hM, fun v hv => ?_⟩` and prove the remaining obligations. Establish `: (M : E) • v = ∑ a, (⟨v a, hv a⟩ : 𝓞 E) • ((M : E) • (Pi.single a 1 : Fin r → E))`. Use extensionality with `b`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single b]`.

Express the relevant statement in the definitionally equal form `(M : E) * v b = v b * ((M : E) * (Pi.single b (1 : E) : Fin r → E) b)`. Simplify using `[mul_comm]`. Introduce `a _ h`. Express the relevant statement in the definitionally equal form `v a * ((M : E) * (Pi.single a (1 : E) : Fin r → E) b) = 0`. Simplify using `[Ne.symm h]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (h a)`.
-/
theorem exists_int_mem : ∃ M : ℕ, 0 < M ∧ ∀ v : Fin r → E, (∀ a, IsIntegral ℤ (v a)) →
    (M : E) • v ∈ X.Λ := by
  obtain ⟨M, hM, h⟩ := exists_common X fun a : Fin r => Pi.single a (1 : E)
  refine ⟨M, hM, fun v hv => ?_⟩
  have : (M : E) • v = ∑ a, (⟨v a, hv a⟩ : 𝓞 E) • ((M : E) • (Pi.single a 1 : Fin r → E)) := by
    ext b
    rw [Finset.sum_apply, Finset.sum_eq_single b]
    · change (M : E) * v b = v b * ((M : E) * (Pi.single b (1 : E) : Fin r → E) b)
      simp [mul_comm]
    · intro a _ h
      change v a * ((M : E) * (Pi.single a (1 : E) : Fin r → E) b) = 0
      simp [Ne.symm h]
    · simp
  rw [this]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (h a)

/- English proof (translation)
Simplify using `only [EFR, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: hermC τ.1 X.Gm ((m • u) τ k) (v τ k) = (m : ℝ) * hermC τ.1 X.Gm (u τ k) (v τ k)`. Simplify using `only [hermC, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum, ofReal_natCast]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite using `[this, mul_left_comm _ ((m : ℝ) : ℂ), re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EFR_nsmul_left (m : ℕ) (u v : WR X n) : EFR X (m • u) v = m * EFR X u v := by
  simp only [EFR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
  have : hermC τ.1 X.Gm ((m • u) τ k) (v τ k) = (m : ℝ) * hermC τ.1 X.Gm (u τ k) (v τ k) := by
    simp only [hermC, Pi.smul_apply, nsmul_eq_mul, Finset.mul_sum, ofReal_natCast]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this, mul_left_comm _ ((m : ℝ) : ℂ), re_ofReal_mul]
  ring

/- English proof (translation)
Introduce `E _ _ _ r X g q0 hr bas idx n hs hn x₁ hx₁ x₂ hx₂ φ₁ φ₂ h₁ h₂`. Take `⟨hsb, hdbl, -⟩` from `GlobalTheory.SW.DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂`. Take `⟨hty, hZ, hdet⟩` from `GlobalTheory.SW.dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂`. Take `⟨-, -, hEF, hdense, -⟩` from `GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ hx₁`. Establish `hsum` using `(GlobalTheory.SW.thH_summable_and_inj E X.Ψ hty n r _ hsb _ hZ).1`.

Take `⟨R, hR, hsupp, -⟩` from `hsb`. Take `⟨M, hM, hMΛ⟩` from `exists_int_mem X`. Use `⟨M * R, Nat.mul_pos hM hR, ?_⟩` and prove the remaining obligations. Introduce and unpack `N hN ⟨d, rfl⟩ Fd hF a b`. Use `set ψ := dbl X bas idx φ₁ φ₂`.

Use `set K := gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) with hK`. Set `c : Matrix (Fin n) (Fin r) E → ℂ` to `fun x => ψ x * cexp (2 * π * I * expo X.Ψ x (dblZ X x₁ x₂) (dblz X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))) (dblz' X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))))`. Set `χ : Matrix (Fin n) (Fin r) E → WR X n → ℂ` to `fun x w => cexp (2 * π * I * (EFR X (embR X x) w : ℝ))`. Establish `hint : ∀ w, cexp (π * I * (EFR X w (a - b) : ℝ)) * (thR X bas idx φ₁ x₁ (w + a) * conj (thR X bas idx φ₂ x₂ (w + b))) = K * ∑' x, c x * χ x w`. Introduce `w`.

Establish `e1` using `hdbl x₁ hx₁ x₂ hx₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))`. Simplify using `only [conj_conj] at e1`. Establish `e2` using `GlobalTheory.T.doubledGaussianKernel_diagonal_translation_invariant E r X g q0 hr bas idx n hs hn x₁ hx₁ x₂ hx₂ a b w`. Establish `e3 : thH X.Ψ ψ (dblZ X x₁ x₂) (dblz X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) (dblz' X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = ∑' x, c x * χ x w`. Use `tsum_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[expo_shift X idx x₁ x₂ (fun τ => (hdet τ).1) (fun τ => (hdet τ).2.1), mul_add, Complex.exp_add, ← mul_assoc]`. Rewrite using `[hK, ← e2, ← e3]`. Simplify using `only [thR, map_mul]`. Rewrite using `[mul_mul_mul_comm (gaussR _ _ _ _ _), e1]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hint]`. Use `haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)`. Use `haveI : Countable (Matrix (Fin n) (Fin r) E) := inferInstanceAs (Countable (Fin n → Fin r → E))`. Establish `hadd : ∀ x v w, χ x (v + w) = χ x v * χ x w` using `fun x v w => by`. Simplify using `only [χ]`.

Rewrite using `[EFR_add_right, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hzero : ∀ x, χ x 0 = 1` using `fun x => by`.

Use `EFR_smul_right X 0 (embR X x) 0` as an intermediate fact. Simplify using `only [zero_smul, zero_mul] at this`. Simplify using `[χ, this]`. Use `haveI : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Use `haveI : (volume : Measure (Fin n → Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`.

Use `haveI : (volume : Measure (WR X n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _`. Establish `key` using `mean_tsum (μ := volume) (latR X n (M * R * d)) (span_latR X hdense hN) hF c (hsum _ _) χ (fun x => by`. Use `continuous_EFR X (embR X x)` as an intermediate fact. Simplify using `only [χ]`. Use the proof step `fun_prop)`.

Use the proof step `(fun x v => by`. Simplify using `only [χ]`. Rewrite using `[show 2 * π * I * ((EFR X (embR X x) v : ℝ) : ℂ) = ((2 * π * EFR X (embR X x) v : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I])`. Use `hadd ?_ 0 (fun v => by`. Use `EFR_nsmul_left X 0 (embR X 0) v` as an intermediate fact.

Rewrite `this` using `[← embR_nsmul]`. Simplify using `only [smul_zero, Nat.cast_zero, zero_mul] at this`. Simplify using `[χ, this]) ?_`. Rewrite using `[integral_const_mul, mul_left_comm, key, mul_comm]`. Use `congr 1`.

Simplify using `[c, expo, dotProduct]`. Introduce `x hx l hl`. Establish `hx'` using `hsupp x (left_ne_zero_of_mul hx)`. Proceed by induction on `hl using AddSubgroup.closure_induction with`. Consider the case `mem l hl`.

Take `⟨y, hy, rfl⟩` from `hl`. Establish `hm : ∀ k, (((M * R : ℕ) : E) • x) k ∈ X.Λ` using `fun k => by`. Use `hMΛ (((R : E) • x) k) (hx' k)` as an intermediate fact. Rewrite using `[Nat.cast_mul, mul_smul]`. Conclude with `this`.

Establish `hi : ∀ k, ∃ m : ℤ, EF X ((((M * R : ℕ) : E) • x) k) (y k) = m` using `fun k => by`. Use `hs (bas.symm ⟨_, hm k⟩) (bas.symm ⟨_, hy k⟩)` as an intermediate fact. Simplify using `only [LinearEquiv.apply_symm_apply] at this`. Conclude with `⟨_, this.trans (Int.cast_neg _).symm⟩`. Use `choose m hm' using hi`.

Establish `e` using `hEF (((M * R : ℕ) : E) • x) y`. Simplify using `only [hm'] at e`. Rewrite `e` using `[embR_nsmul, EFR_nsmul_left]`. Establish `e' : EFR X (embR X x) ((M * R * d) • embR X y) = ((d * ∑ k, m k : ℤ) : ℝ)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℝ, EFR_smul_right, Nat.cast_mul, mul_comm _ (d : ℝ), mul_assoc, e]`.

Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [χ]`. Rewrite using `[e', ← Complex.exp_int_mul_two_pi_mul_I (d * ∑ k, m k)]`. Use `congr 1`.

Rewrite using `[ofReal_intCast]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => exact hzero x`. Consider the case `add l l' _ _ h h' => rw [hadd, h, h', one_mul]`. Consider the case `neg l _ h`.

Use `hadd x l (-l)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, hzero, h, one_mul]`. Conclude with `this.symm`. Introduce `x hx`. Take `⟨w, hw⟩` from `exists_EFR_ne X x hx`.

Use `⟨(2 * EFR X (embR X x) w)⁻¹ • w, ?_⟩` and prove the remaining obligations. Simplify using `only [χ]`. Rewrite using `[EFR_smul_right, show (2 * EFR X (embR X x) w)⁻¹ * EFR X (embR X x) w = 1 / 2 by field_simp, show 2 * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]`. Evaluate the numerical expressions.
-/
theorem mean_thR_mul_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ Fd : Set (WR X n), IsAddFundamentalDomain (latR X n N) Fd volume → ∀ a b : WR X n, ((volume Fd).toReal : ℂ)⁻¹ * ∫ w in Fd, cexp (π * I * (EFR X w (a - b) : ℝ)) * (thR X bas idx φ₁ x₁ (w + a) * conj (thR X bas idx φ₂ x₂ (w + b))) = dbl X bas idx φ₁ φ₂ 0 * (gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x₁ hx₁ x₂ hx₂ φ₁ φ₂ h₁ h₂
  obtain ⟨hsb, hdbl, -⟩ := GlobalTheory.SW.DblEx.dbl_spec E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂
  obtain ⟨hty, hZ, hdet⟩ := GlobalTheory.SW.dblZ_mem_Hn E r X x₁ hx₁ x₂ hx₂
  obtain ⟨-, -, hEF, hdense, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ hx₁
  have hsum := (GlobalTheory.SW.thH_summable_and_inj E X.Ψ hty n r _ hsb _ hZ).1
  obtain ⟨R, hR, hsupp, -⟩ := hsb
  obtain ⟨M, hM, hMΛ⟩ := exists_int_mem X
  refine ⟨M * R, Nat.mul_pos hM hR, ?_⟩
  rintro N hN ⟨d, rfl⟩ Fd hF a b
  set ψ := dbl X bas idx φ₁ φ₂
  set K := gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) *
    kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) with hK
  let c : Matrix (Fin n) (Fin r) E → ℂ := fun x => ψ x * cexp (2 * π * I * expo X.Ψ x (dblZ X x₁ x₂)
    (dblz X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)))
    (dblz' X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i))))
  let χ : Matrix (Fin n) (Fin r) E → WR X n → ℂ := fun x w =>
    cexp (2 * π * I * (EFR X (embR X x) w : ℝ))
  have hint : ∀ w, cexp (π * I * (EFR X w (a - b) : ℝ)) *
      (thR X bas idx φ₁ x₁ (w + a) * conj (thR X bas idx φ₂ x₂ (w + b))) =
      K * ∑' x, c x * χ x w := by
    intro w
    have e1 := hdbl x₁ hx₁ x₂ hx₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))
    simp only [conj_conj] at e1
    have e2 := GlobalTheory.T.doubledGaussianKernel_diagonal_translation_invariant E r X g q0 hr bas idx n hs hn x₁ hx₁ x₂ hx₂ a b w
    have e3 : thH X.Ψ ψ (dblZ X x₁ x₂)
        (dblz X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i)))
        (dblz' X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) =
        ∑' x, c x * χ x w := by
      refine tsum_congr fun x => ?_
      rw [expo_shift X idx x₁ x₂ (fun τ => (hdet τ).1) (fun τ => (hdet τ).2.1), mul_add,
        Complex.exp_add, ← mul_assoc]
    rw [hK, ← e2, ← e3]
    simp only [thR, map_mul]
    rw [mul_mul_mul_comm (gaussR _ _ _ _ _), e1]
    ring
  simp only [hint]
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin n) (Fin r) E) := inferInstanceAs (Countable (Fin n → Fin r → E))
  have hadd : ∀ x v w, χ x (v + w) = χ x v * χ x w := fun x v w => by
    simp only [χ]
    rw [EFR_add_right, ← Complex.exp_add]; congr 1; push_cast; ring
  have hzero : ∀ x, χ x 0 = 1 := fun x => by
    have := EFR_smul_right X 0 (embR X x) 0
    simp only [zero_smul, zero_mul] at this
    simp [χ, this]
  haveI : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Fin r → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (WR X n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := mean_tsum (μ := volume) (latR X n (M * R * d)) (span_latR X hdense hN) hF c (hsum _ _) χ
    (fun x => by
      have := continuous_EFR X (embR X x)
      simp only [χ]
      fun_prop)
    (fun x v => by
      simp only [χ]
      rw [show 2 * π * I * ((EFR X (embR X x) v : ℝ) : ℂ) =
        ((2 * π * EFR X (embR X x) v : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I])
    hadd ?_ 0 (fun v => by
      have := EFR_nsmul_left X 0 (embR X 0) v
      rw [← embR_nsmul] at this
      simp only [smul_zero, Nat.cast_zero, zero_mul] at this
      simp [χ, this]) ?_
  · rw [integral_const_mul, mul_left_comm, key, mul_comm]
    congr 1
    simp [c, expo, dotProduct]
  · intro x hx l hl
    have hx' := hsupp x (left_ne_zero_of_mul hx)
    induction hl using AddSubgroup.closure_induction with
    | mem l hl =>
      obtain ⟨y, hy, rfl⟩ := hl
      have hm : ∀ k, (((M * R : ℕ) : E) • x) k ∈ X.Λ := fun k => by
        have := hMΛ (((R : E) • x) k) (hx' k)
        rw [Nat.cast_mul, mul_smul]
        exact this
      have hi : ∀ k, ∃ m : ℤ, EF X ((((M * R : ℕ) : E) • x) k) (y k) = m := fun k => by
        have := hs (bas.symm ⟨_, hm k⟩) (bas.symm ⟨_, hy k⟩)
        simp only [LinearEquiv.apply_symm_apply] at this
        exact ⟨_, this.trans (Int.cast_neg _).symm⟩
      choose m hm' using hi
      have e := hEF (((M * R : ℕ) : E) • x) y
      simp only [hm'] at e
      rw [embR_nsmul, EFR_nsmul_left] at e
      have e' : EFR X (embR X x) ((M * R * d) • embR X y) = ((d * ∑ k, m k : ℤ) : ℝ) := by
        rw [← Nat.cast_smul_eq_nsmul ℝ, EFR_smul_right, Nat.cast_mul, mul_comm _ (d : ℝ), mul_assoc, e]
        push_cast; rfl
      simp only [χ]
      rw [e', ← Complex.exp_int_mul_two_pi_mul_I (d * ∑ k, m k)]
      congr 1
      rw [ofReal_intCast]; ring
    | zero => exact hzero x
    | add l l' _ _ h h' => rw [hadd, h, h', one_mul]
    | neg l _ h =>
      have := hadd x l (-l)
      rw [add_neg_cancel, hzero, h, one_mul] at this
      exact this.symm
  · intro x hx
    obtain ⟨w, hw⟩ := exists_EFR_ne X x hx
    refine ⟨(2 * EFR X (embR X x) w)⁻¹ • w, ?_⟩
    simp only [χ]
    rw [EFR_smul_right, show (2 * EFR X (embR X x) w)⁻¹ * EFR X (embR X x) w = 1 / 2 by field_simp,
      show 2 * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]
    norm_num

end GlobalTheory.Ker.Mean
