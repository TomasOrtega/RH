import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.RightBilinearApply
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ExistsDecayBoundTwo
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SigmaFinitePosRealMeasure
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.FiniteSupportOfHyp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_vecMul_le' (v : Vr F) (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    ‖v ᵥ* M‖ ≤ ‖v‖ * ∑ i, ∑ j, ‖M i j‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  calc ‖(v ᵥ* M) j‖ = ‖∑ i, v i * M i j‖ := by simp only [Matrix.vecMul, dotProduct]
    _ ≤ ∑ i, ‖v i * M i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v‖ * ‖M i j‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (norm_nonneg _))
    _ = ‖v‖ * ∑ i, ‖M i j‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖v‖ * ∑ i, ∑ j, ‖M i j‖ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖M i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
        (norm_nonneg _)

/- English proof (translation)
Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_mulVec_le' (M : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) (v : Vr F) :
    ‖M *ᵥ v‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ v) i‖ = ‖∑ j, M i j * v j‖ := by simp only [Matrix.mulVec, dotProduct]
    _ ≤ ∑ j, ‖M i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖v‖ := Finset.sum_le_sum fun j _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))
        (norm_nonneg _)

/- English proof (translation)
Establish `h1 : 1 + p ≤ (K + 1) * (1 + w)` using `by nlinarith`. Establish `hpos : 0 < (1 + p) ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]`. Use `_ ≤ (K + 1) ^ k * ((1 + p) ^ k)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hpos (pow_le_pow_left₀ (by positivity) h1 k)) (by positivity)`.
-/
theorem inv_pow_le_of_le {p w K : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) (hK : 0 ≤ K) (h : p ≤ K * w) (k : ℕ) :
    ((1 + w) ^ k)⁻¹ ≤ (K + 1) ^ k * ((1 + p) ^ k)⁻¹ := by
  have h1 : 1 + p ≤ (K + 1) * (1 + w) := by nlinarith
  have hpos : 0 < (1 + p) ^ k := by positivity
  calc ((1 + w) ^ k)⁻¹ = (K + 1) ^ k * (((K + 1) * (1 + w)) ^ k)⁻¹ := by
        rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ (K + 1) ^ k * ((1 + p) ^ k)⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ hpos (pow_le_pow_left₀ (by positivity) h1 k)) (by positivity)

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [rowv, Mrow, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.vecMul, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem rowv_eq (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    rowv g a ξ = fun j => (a : Ad F) * (rowA ξ ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F))) j := by
  funext j
  simp only [rowv, Mrow, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul, Matrix.vecMul, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [colv, Mcol, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem colv_eq (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    colv g a ξ = fun j => ((a⁻¹ : Ideles F) : Ad F) *
      (((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) j := by
  funext j
  simp only [colv, Mcol, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_diagonal, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [vInf, rowv_eq, Matrix.vecMul, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem vInf_rowv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    vInf (rowv g a ξ) = (fun i => UpperTheory.V.TR.pInf F ((a : Ad F) * algebraMap F (Ad F) (ξ i))) ᵥ*
      (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) := by
  funext j
  simp only [vInf, rowv_eq, Matrix.vecMul, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [vInf, colv_eq, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]`. Use `Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations.
-/
theorem vInf_colv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) :
    vInf (colv g a ξ) = ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) *ᵥ
      (fun i => UpperTheory.V.TR.pInf F (((a⁻¹ : Ideles F) : Ad F) * algebraMap F (Ad F) (ξ i))) := by
  funext j
  simp only [vInf, colv_eq, Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rowA]
  refine Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_pInf_mul_inv (g : GA F 2) :
    (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) *
      ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_pInf_inv_mul (g : GA F 2) :
    ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) *
      (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[coe_moduleSection]`. Both sides reduce to the same expression.
-/
theorem pFin_moduleSection (t : {r : ℝ // 0 < r}) :
    pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
  rw [coe_moduleSection]
  rfl

/- English proof (translation)
Establish `h : pFin F (((moduleSection (w0 F) t)⁻¹ : Ideles F) : Ad F) * pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1`. Rewrite using `[← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Rewrite `h` using `[pFin_moduleSection, mul_one]`. Then use the resulting hypothesis.
-/
theorem pFin_moduleSection_inv (t : {r : ℝ // 0 < r}) :
    pFin F ((((moduleSection (w0 F) t)⁻¹ : Ideles F)) : Ad F) = 1 := by
  have h : pFin F (((moduleSection (w0 F) t)⁻¹ : Ideles F) : Ad F) *
      pFin F ((moduleSection (w0 F) t : Ideles F) : Ad F) = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  rwa [pFin_moduleSection, mul_one] at h

/- English proof (translation)
Unfold `finRow`. Use `split_ifs with h1 h2 h2`. Both sides reduce to the same expression. Conclude with `absurd (by simpa only [h] using h1) h2`. Conclude with `absurd (by simpa only [← h] using h2) h1`.

Both sides reduce to the same expression.
-/
theorem finite_row_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {y y' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (y i) = pFin F (y' i)) : finRow c y = finRow c y' := by
  unfold finRow
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by simpa only [h] using h1) h2
  · exact absurd (by simpa only [← h] using h2) h1
  · rfl

/- English proof (translation)
Unfold `finCol`. Use `split_ifs with h1 h2 h2`. Rewrite using `[h 1]`. Conclude with `absurd (by simpa only [h] using h1) h2`. Conclude with `absurd (by simpa only [← h] using h2) h1`.

Both sides reduce to the same expression.
-/
theorem finite_column_congr {c : HeightOneSpectrum (𝓞 F) → ℕ} {y y' : Fin 2 → Ad F}
    (h : ∀ i, pFin F (y i) = pFin F (y' i)) : finCol c y = finCol c y' := by
  unfold finCol
  split_ifs with h1 h2 h2
  · rw [h 1]
  · exact absurd (by simpa only [h] using h1) h2
  · exact absurd (by simpa only [← h] using h2) h1
  · rfl

/- English proof (translation)
Use `finite_row_congr fun i => ?_` and prove the remaining obligations. Simplify using `only [rowv_eq, av, Units.val_mul, map_mul, pFin_moduleSection, one_mul]`.
-/
theorem finRow_av (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (ξ : Fin 2 → F) :
    finRow c (rowv g (av p) ξ) = finRow c (rowv g (p.2 : Ideles F) ξ) := by
  refine finite_row_congr fun i => ?_
  simp only [rowv_eq, av, Units.val_mul, map_mul, pFin_moduleSection, one_mul]

/- English proof (translation)
Use `finite_column_congr fun i => ?_` and prove the remaining obligations. Simplify using `only [colv_eq, av, mul_inv_rev, Units.val_mul, map_mul, pFin_moduleSection_inv, mul_one]`.
-/
theorem finCol_av (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (p : Pp F) (ξ : Fin 2 → F) :
    finCol c (colv g (av p) ξ) = finCol c (colv g (p.2 : Ideles F) ξ) := by
  refine finite_column_congr fun i => ?_
  simp only [colv_eq, av, mul_inv_rev, Units.val_mul, map_mul, pFin_moduleSection_inv, mul_one]

/- English proof (translation)
Unfold `finRow`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem norm_finRow_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ‖finRow c y‖ ≤ 1 := by
  unfold finRow
  split_ifs <;> simp

/- English proof (translation)
Unfold `finCol`. Use `split_ifs`. Conclude with `(Circle.norm_coe _).le`. Simplify using the standard rewrite rules.
-/
theorem norm_finCol_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ‖finCol c y‖ ≤ 1 := by
  unfold finCol
  split_ifs
  · exact (Circle.norm_coe _).le
  · simp

/- English proof (translation)
Use `set E := normOneFundamentalDomain F with hEdef`. Use `set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef`. Establish `hC : IsCompact C` using `(isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val`. Take `⟨d, hd0, hd⟩` from `exists_den_row c g hC`. Take `⟨k, U, hU, hdec⟩` from `exists_decay_bound_two F hC d hd0 2`.

Use `set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'`. Use `set K := ∑ i, ∑ j, ‖G' i j‖ with hKdef`. Establish `hK : 0 ≤ K` using `by positivity`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) := ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩`.

Use `set bnd : Pp F × Xi F → ℝ := fun q => (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2)⁻¹ * (q.1.1 : ℝ)) * 1) * |U q.2.1|) with hbnddef`. Establish `hbnd : Integrable bnd (μS F {t | 1 ≤ (t : ℝ)})`. Establish `h1 : Integrable (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ 2)⁻¹ * (t : ℝ)) (posRealMeasure.restrict {t | 1 ≤ (t : ℝ)})` using `integrableOn_ge_one le_rfl`. Establish `h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E)` using `integrable_const _`. Establish `h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count`.

Rewrite using `[integrable_count_iff]`. Establish `hi : Function.Injective (fun x : Xi F => x.1)` using `fun x y h => Subtype.ext h`. Simplify `hU.abs.comp_injective hi` using `[Function.comp_def]`. Conclude with `((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)`. Use `hbnd.mono' ?_ ?_` and prove the remaining obligations.

Conclude with `(hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable`. Establish `hae : ∀ᵐ q ∂(μS F {t | 1 ≤ (t : ℝ)}), 1 ≤ (q.1.1 : ℝ) ∧ q.1.2 ∈ E`. Establish `ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}), 1 ≤ (t : ℝ)` using `ae_restrict_mem measurableSet_ge_one`. Establish `hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E` using `ae_restrict_mem (measurableSet_normOneFundamentalDomain F)`. Establish `h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}).prod ((normOneMeasure F).restrict E)), 1 ≤ (p.1 : ℝ) ∧ p.2 ∈ E` using `by filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha, Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩`.

Conclude with `Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1`. Use `filter_upwards [hae] with q hq`. Take `⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩` from `q`. Take `⟨ht, hu⟩` from `hq`. Simplify using `only at ht hu`.

Establish `hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩)` using `by simp only [hbnddef]; positivity`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Distinguish the cases in `hf : finRow c (rowv g (av (t, u)) ξ) = 0`. Establish `: kap1 χ c g ((t, u), ⟨ξ, hξ⟩) = 0` using `by simp only [kap1]; rw [hf, zero_mul, zero_mul]`. Rewrite using `[this, norm_zero, zero_mul]`.

Conclude with `hbpos`. Establish `huC : (u : Ideles F) ∈ C` using `⟨u, subset_closure hu, rfl⟩`. Establish `hcond : ∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (u : Ideles F) * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧ Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (u : …`. Rewrite `hf` using `[finRow_av]`. Unfold `finRow at hf`.

Use `split_ifs at hf with hc`. Conclude with `hc`. Conclude with `absurd rfl hf`. Establish `hden` using `hd _ huC ξ hcond`. Establish `hdecay` using `hdec _ huC t ht ξ hξ hden`.

Use `set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t * (u : Ideles F) : Ideles F) : Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef`. Establish `hw1 : w1 g ((t, u), ⟨ξ, hξ⟩) = P ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F)`. Simplify using `only [w1]`. Rewrite using `[vInf_rowv]`. Both sides reduce to the same expression.

Establish `hPw : ‖P‖ ≤ K * ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖`. Establish `e : P = w1 g ((t, u), ⟨ξ, hξ⟩) ᵥ* G'`. Rewrite using `[hw1, Matrix.vecMul_vecMul, hG', map_pInf_mul_inv, Matrix.vecMul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hkap : ‖kap1 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ)`.

Simplify using `only [kap1, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real, Real.norm_of_nonneg t.2.le]`. Conclude with `mul_le_of_le_one_left t.2.le (norm_finRow_le c _)`. Establish `hw'` using `inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k`. Establish `hUabs : U ξ ≤ |U ξ|` using `le_abs_self _`. Establish `ht0 : (0 : ℝ) < t` using `t.2`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem hint1 {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) (g : GA F 2)
    (hκ : AEStronglyMeasurable (kap1 χ c g) (μS F {t | 1 ≤ (t : ℝ)}))
    (hw : AEStronglyMeasurable (w1 g) (μS F {t | 1 ≤ (t : ℝ)})) :
    ∃ k : ℕ, Integrable (fun q => ‖kap1 χ c g q‖ * ((1 + ‖w1 g q‖) ^ k)⁻¹) (μS F {t | 1 ≤ (t : ℝ)}) := by
  classical
  set E := normOneFundamentalDomain F with hEdef
  set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val
  obtain ⟨d, hd0, hd⟩ := exists_den_row c g hC
  obtain ⟨k, U, hU, hdec⟩ := exists_decay_bound_two F hC d hd0 2
  set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'
  set K := ∑ i, ∑ j, ‖G' i j‖ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨k, ?_⟩
  haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩
  set bnd : Pp F × Xi F → ℝ := fun q =>
    (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2)⁻¹ * (q.1.1 : ℝ)) * 1) * |U q.2.1|) with hbnddef
  have hbnd : Integrable bnd (μS F {t | 1 ≤ (t : ℝ)}) := by
    have h1 : Integrable (fun t : {r : ℝ // 0 < r} => ((t : ℝ) ^ 2)⁻¹ * (t : ℝ))
        (posRealMeasure.restrict {t | 1 ≤ (t : ℝ)}) := integrableOn_ge_one le_rfl
    have h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E) :=
      integrable_const _
    have h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count := by
      rw [integrable_count_iff]
      have hi : Function.Injective (fun x : Xi F => x.1) := fun x y h => Subtype.ext h
      simpa [Function.comp_def] using hU.abs.comp_injective hi
    exact ((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)
  refine hbnd.mono' ?_ ?_
  · exact (hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable
  have hae : ∀ᵐ q ∂(μS F {t | 1 ≤ (t : ℝ)}), 1 ≤ (q.1.1 : ℝ) ∧ q.1.2 ∈ E := by
    have ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}), 1 ≤ (t : ℝ) :=
      ae_restrict_mem measurableSet_ge_one
    have hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain F)
    have h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | 1 ≤ (t : ℝ)}).prod
        ((normOneMeasure F).restrict E)), 1 ≤ (p.1 : ℝ) ∧ p.2 ∈ E := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha,
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1
  filter_upwards [hae] with q hq
  obtain ⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩ := q
  obtain ⟨ht, hu⟩ := hq
  simp only at ht hu
  have hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; positivity
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hf : finRow c (rowv g (av (t, u)) ξ) = 0
  · have : kap1 χ c g ((t, u), ⟨ξ, hξ⟩) = 0 := by simp only [kap1]; rw [hf, zero_mul, zero_mul]
    rw [this, norm_zero, zero_mul]
    exact hbpos
  have huC : (u : Ideles F) ∈ C := ⟨u, subset_closure hu, rfl⟩
  have hcond : ∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      (u : Ideles F) * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) (u : Ideles F) * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) := by
    rw [finRow_av] at hf
    unfold finRow at hf
    split_ifs at hf with hc
    · exact hc
    · exact absurd rfl hf
  have hden := hd _ huC ξ hcond
  have hdecay := hdec _ huC t ht ξ hξ hden
  set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t * (u : Ideles F) : Ideles F) : Ad F) *
    algebraMap F (Ad F) (ξ i)) with hPdef
  have hw1 : w1 g ((t, u), ⟨ξ, hξ⟩) = P ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) := by
    simp only [w1]
    rw [vInf_rowv]
    rfl
  have hPw : ‖P‖ ≤ K * ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ := by
    have e : P = w1 g ((t, u), ⟨ξ, hξ⟩) ᵥ* G' := by
      rw [hw1, Matrix.vecMul_vecMul, hG', map_pInf_mul_inv, Matrix.vecMul_one]
    calc ‖P‖ = ‖w1 g ((t, u), ⟨ξ, hξ⟩) ᵥ* G'‖ := by rw [← e]
      _ ≤ ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ * K := norm_vecMul_le' _ _
      _ = K * ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖ := mul_comm _ _
  have hkap : ‖kap1 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ) := by
    simp only [kap1, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg t.2.le]
    exact mul_le_of_le_one_left t.2.le (norm_finRow_le c _)
  have hw' := inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k
  have hUabs : U ξ ≤ |U ξ| := le_abs_self _
  have ht0 : (0 : ℝ) < t := t.2
  calc ‖kap1 χ c g ((t, u), ⟨ξ, hξ⟩)‖ * ((1 + ‖w1 g ((t, u), ⟨ξ, hξ⟩)‖) ^ k)⁻¹
      ≤ (t : ℝ) * ((K + 1) ^ k * (((t : ℝ) ^ 2)⁻¹ * U ξ)) :=
        mul_le_mul hkap (hw'.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))) (by positivity) ht0.le
    _ ≤ (t : ℝ) * ((K + 1) ^ k * (((t : ℝ) ^ 2)⁻¹ * |U ξ|)) := by gcongr
    _ = bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; ring

/- English proof (translation)
Use `set E := normOneFundamentalDomain F with hEdef`. Use `set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef`. Establish `hC : IsCompact C` using `(isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val`. Use `set C2 : Set (Ideles F) := (fun u : normOneSubgroup F => ((u : Ideles F))⁻¹) '' closure E with hC2def`. Establish `hC2 : IsCompact C2` using `(isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val.inv`.

Take `⟨d, hd0, hd⟩` from `exists_den_col c (finite_support_of_hyp H) g hC`. Take `⟨k, U, hU, hdec⟩` from `exists_decay_bound_two F hC2 d hd0 2`. Use `set G := (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG`. Use `set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'`. Use `set K := ∑ i, ∑ j, ‖G i j‖ with hKdef`.

Establish `hK : 0 ≤ K` using `by positivity`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) := ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩`. Use `set bnd : Pp F × Xi F → ℝ := fun q => (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2) * (q.1.1 : ℝ)⁻¹) * 1) * |U q.2.1|) with hbnddef`. Establish `hbnd : Integrable bnd (μS F {t | (t : ℝ) < 1})`.

Establish `h1 : Integrable (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ 2 * (t : ℝ)⁻¹) (posRealMeasure.restrict {t | (t : ℝ) < 1})` using `integrableOn_lt_one le_rfl`. Establish `h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E)` using `integrable_const _`. Establish `h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count`. Rewrite using `[integrable_count_iff]`. Establish `hi : Function.Injective (fun x : Xi F => x.1)` using `fun x y h => Subtype.ext h`.

Simplify `hU.abs.comp_injective hi` using `[Function.comp_def]`. Conclude with `((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)`. Use `hbnd.mono' ?_ ?_` and prove the remaining obligations. Conclude with `(hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable`. Establish `hae : ∀ᵐ q ∂(μS F {t | (t : ℝ) < 1}), (q.1.1 : ℝ) < 1 ∧ q.1.2 ∈ E`.

Establish `ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}), (t : ℝ) < 1` using `ae_restrict_mem measurableSet_lt_one`. Establish `hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E` using `ae_restrict_mem (measurableSet_normOneFundamentalDomain F)`. Establish `h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}).prod ((normOneMeasure F).restrict E)), (p.1 : ℝ) < 1 ∧ p.2 ∈ E` using `by filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha, Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩`. Conclude with `Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1`. Use `filter_upwards [hae] with q hq`.

Take `⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩` from `q`. Take `⟨ht, hu⟩` from `hq`. Simplify using `only at ht hu`. Establish `hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩)`. Simplify using `only [hbnddef]`.

Conclude with `mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg t.2.le _) (inv_nonneg.2 t.2.le)) zero_le_one) (abs_nonneg _))`. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Distinguish the cases in `hf : finCol c (colv g (av (t, u)) ξ) = 0`. Establish `: kap2 χ c g ((t, u), ⟨ξ, hξ⟩) = 0` using `by simp only [kap2]; rw [hf, zero_mul, zero_mul]`. Rewrite using `[this, norm_zero, zero_mul]`.

Conclude with `hbpos`. Establish `huC : (u : Ideles F) ∈ C` using `⟨u, subset_closure hu, rfl⟩`. Establish `hu2 : ((u : Ideles F))⁻¹ ∈ C2` using `⟨u, subset_closure hu, rfl⟩`. Establish `hden` using `hd _ huC ξ (by`. Rewrite `hf` using `[finCol_av]`.

Unfold `finCol at hf`. Use `split_ifs at hf with hc`. Conclude with `hc`. Conclude with `absurd rfl hf)`. Establish `ht0 : (0 : ℝ) < t` using `t.2`.

Establish `hT : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹` using `Positive.coe_inv t`. Establish `hT1 : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)`. Rewrite using `[hT]`. Conclude with `(one_le_inv₀ ht0).2 ht.le`. Establish `hdecay` using `hdec _ hu2 t⁻¹ hT1 ξ hξ hden`.

Establish `hav : moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ = (av (t, u))⁻¹`. Simplify using `only [av, map_inv, mul_inv]`. Use `set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ : Ideles F) : Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef`. Establish `hw2 : w2 g ((t, u), ⟨ξ, hξ⟩) = G' *ᵥ P`. Simplify using `only [w2]`.

Rewrite using `[vInf_colv, hPdef, hav]`. Establish `hPw : ‖P‖ ≤ K * ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖`. Establish `e : P = G *ᵥ w2 g ((t, u), ⟨ξ, hξ⟩)`. Rewrite using `[hw2, Matrix.mulVec_mulVec, hG, hG', map_pInf_mul_inv, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hkap : ‖kap2 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ)⁻¹`. Simplify using `only [kap2, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real, Real.norm_of_nonneg t.2.le]`. Conclude with `mul_le_of_le_one_left (inv_nonneg.2 t.2.le) (norm_finCol_le c _)`. Establish `hw'` using `inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k`. Establish `hUabs : U ξ ≤ |U ξ|` using `le_abs_self _`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem hint2 {χ : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp χ c) (g : GA F 2)
    (hκ : AEStronglyMeasurable (kap2 χ c g) (μS F {t | (t : ℝ) < 1}))
    (hw : AEStronglyMeasurable (w2 g) (μS F {t | (t : ℝ) < 1})) :
    ∃ k : ℕ, Integrable (fun q => ‖kap2 χ c g q‖ * ((1 + ‖w2 g q‖) ^ k)⁻¹) (μS F {t | (t : ℝ) < 1}) := by
  classical
  set E := normOneFundamentalDomain F with hEdef
  set C : Set (Ideles F) := (fun u : normOneSubgroup F => (u : Ideles F)) '' closure E with hCdef
  have hC : IsCompact C := (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val
  set C2 : Set (Ideles F) := (fun u : normOneSubgroup F => ((u : Ideles F))⁻¹) '' closure E with hC2def
  have hC2 : IsCompact C2 :=
    (isCompact_closure_normOneFundamentalDomain (K := F)).image continuous_subtype_val.inv
  obtain ⟨d, hd0, hd⟩ := exists_den_col c (finite_support_of_hyp H) g hC
  obtain ⟨k, U, hU, hdec⟩ := exists_decay_bound_two F hC2 d hd0 2
  set G := (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG
  set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'
  set K := ∑ i, ∑ j, ‖G i j‖ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨k, ?_⟩
  haveI : IsFiniteMeasure ((normOneMeasure F).restrict E) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact normOneMeasure_normOneFundamentalDomain_lt_top F⟩
  set bnd : Pp F × Xi F → ℝ := fun q =>
    (K + 1) ^ k * (((((q.1.1 : ℝ) ^ 2) * (q.1.1 : ℝ)⁻¹) * 1) * |U q.2.1|) with hbnddef
  have hbnd : Integrable bnd (μS F {t | (t : ℝ) < 1}) := by
    have h1 : Integrable (fun t : {r : ℝ // 0 < r} => (t : ℝ) ^ 2 * (t : ℝ)⁻¹)
        (posRealMeasure.restrict {t | (t : ℝ) < 1}) := integrableOn_lt_one le_rfl
    have h2 : Integrable (fun _ : normOneSubgroup F => (1 : ℝ)) ((normOneMeasure F).restrict E) :=
      integrable_const _
    have h3 : Integrable (fun ξ : Xi F => |U ξ.1|) Measure.count := by
      rw [integrable_count_iff]
      have hi : Function.Injective (fun x : Xi F => x.1) := fun x y h => Subtype.ext h
      simpa [Function.comp_def] using hU.abs.comp_injective hi
    exact ((h1.mul_prod h2).mul_prod h3).const_mul ((K + 1) ^ k)
  refine hbnd.mono' ?_ ?_
  · exact (hκ.aemeasurable.norm.mul ((hw.aemeasurable.norm.const_add 1).pow_const k).inv).aestronglyMeasurable
  have hae : ∀ᵐ q ∂(μS F {t | (t : ℝ) < 1}), (q.1.1 : ℝ) < 1 ∧ q.1.2 ∈ E := by
    have ha : ∀ᵐ t : {r : ℝ // 0 < r} ∂(posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}),
        (t : ℝ) < 1 := ae_restrict_mem measurableSet_lt_one
    have hb : ∀ᵐ u ∂((normOneMeasure F).restrict E), u ∈ E :=
      ae_restrict_mem (measurableSet_normOneFundamentalDomain F)
    have h1 : ∀ᵐ p ∂((posRealMeasure.restrict {t : {r : ℝ // 0 < r} | (t : ℝ) < 1}).prod
        ((normOneMeasure F).restrict E)), (p.1 : ℝ) < 1 ∧ p.2 ∈ E := by
      filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually ha,
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb] with p h1 h2 using ⟨h1, h2⟩
    exact Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually h1
  filter_upwards [hae] with q hq
  obtain ⟨⟨t, u⟩, ⟨ξ, hξ⟩⟩ := q
  obtain ⟨ht, hu⟩ := hq
  simp only at ht hu
  have hbpos : 0 ≤ bnd ((t, u), ⟨ξ, hξ⟩) := by
    simp only [hbnddef]
    exact mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg t.2.le _) (inv_nonneg.2 t.2.le)) zero_le_one) (abs_nonneg _))
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hf : finCol c (colv g (av (t, u)) ξ) = 0
  · have : kap2 χ c g ((t, u), ⟨ξ, hξ⟩) = 0 := by simp only [kap2]; rw [hf, zero_mul, zero_mul]
    rw [this, norm_zero, zero_mul]
    exact hbpos
  have huC : (u : Ideles F) ∈ C := ⟨u, subset_closure hu, rfl⟩
  have hu2 : ((u : Ideles F))⁻¹ ∈ C2 := ⟨u, subset_closure hu, rfl⟩
  have hden := hd _ huC ξ (by
    rw [finCol_av] at hf
    unfold finCol at hf
    split_ifs at hf with hc
    · exact hc
    · exact absurd rfl hf)
  have ht0 : (0 : ℝ) < t := t.2
  have hT : ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) = (t : ℝ)⁻¹ := Positive.coe_inv t
  have hT1 : 1 ≤ ((t⁻¹ : {r : ℝ // 0 < r}) : ℝ) := by
    rw [hT]; exact (one_le_inv₀ ht0).2 ht.le
  have hdecay := hdec _ hu2 t⁻¹ hT1 ξ hξ hden
  have hav : moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ = (av (t, u))⁻¹ := by
    simp only [av, map_inv, mul_inv]
  set P : Vr F := fun i => UpperTheory.V.TR.pInf F (((moduleSection (w0 F) t⁻¹ * ((u : Ideles F))⁻¹ : Ideles F) :
    Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef
  have hw2 : w2 g ((t, u), ⟨ξ, hξ⟩) = G' *ᵥ P := by
    simp only [w2]
    rw [vInf_colv, hPdef, hav]
  have hPw : ‖P‖ ≤ K * ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖ := by
    have e : P = G *ᵥ w2 g ((t, u), ⟨ξ, hξ⟩) := by
      rw [hw2, Matrix.mulVec_mulVec, hG, hG', map_pInf_mul_inv, Matrix.one_mulVec]
    calc ‖P‖ = ‖G *ᵥ w2 g ((t, u), ⟨ξ, hξ⟩)‖ := by rw [← e]
      _ ≤ K * ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖ := norm_mulVec_le' _ _
  have hkap : ‖kap2 χ c g ((t, u), ⟨ξ, hξ⟩)‖ ≤ (t : ℝ)⁻¹ := by
    simp only [kap2, norm_mul, norm_inv, norm_hchar_of_finOrder H.fin, inv_one, mul_one, Complex.norm_real,
      Real.norm_of_nonneg t.2.le]
    exact mul_le_of_le_one_left (inv_nonneg.2 t.2.le) (norm_finCol_le c _)
  have hw' := inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k
  have hUabs : U ξ ≤ |U ξ| := le_abs_self _
  calc ‖kap2 χ c g ((t, u), ⟨ξ, hξ⟩)‖ * ((1 + ‖w2 g ((t, u), ⟨ξ, hξ⟩)‖) ^ k)⁻¹
      ≤ (t : ℝ)⁻¹ * ((K + 1) ^ k * (((((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)) ^ 2)⁻¹ * U ξ)) :=
        mul_le_mul hkap (hw'.trans (mul_le_mul_of_nonneg_left hdecay (by positivity))) (by positivity)
          (inv_nonneg.2 ht0.le)
    _ ≤ (t : ℝ)⁻¹ * ((K + 1) ^ k * (((((t⁻¹ : {r : ℝ // 0 < r}) : ℝ)) ^ 2)⁻¹ * |U ξ|)) := by gcongr
    _ = bnd ((t, u), ⟨ξ, hξ⟩) := by simp only [hbnddef]; rw [hT]; field_simp

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
