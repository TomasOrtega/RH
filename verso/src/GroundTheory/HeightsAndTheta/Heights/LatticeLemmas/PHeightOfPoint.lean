import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ComplexAt TensorProduct

noncomputable section

namespace HeightOfPointAlt

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hr`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans (max_le (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))`.
-/
theorem adicAbv_sum_le (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/- English proof (translation)
Establish `hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite` using `FinitePlace.hasFiniteMulSupport hc`. Use `(hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_preimage, Function.mem_mulSupport, FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]`. Conclude with `hv`.
-/
theorem finite_adicAbv_ne_one {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  refine (hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  exact hv

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

omit [NumberField F] in

/- English proof (translation)
Set `b : 𝓞 K` to `⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩`. Establish `hb : intToField F K a = algebraMap (𝓞 K) K b` using `rfl`. Rewrite using `[hb]`. Conclude with `v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b`.
-/
theorem adicAbv_intToField_le_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by
  let b : 𝓞 K := ⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩
  have hb : intToField F K a = algebraMap (𝓞 K) K b := rfl
  rw [hb]
  exact v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b

variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]

def archLinear (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[ℂ] ComplexAt (τ.comp (algebraMap F K)) where
  toFun := archFunctional τ yv
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z e =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply]
      simp only [archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
      exact smul_mul_assoc c z _
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

/- English proof (translation)
Use `set σ := τ.comp (algebraMap F K)`. Set `φ : FibreSpace h σ →ₗ[ℂ] ℂ` to `(ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ (FibreSpace.equiv h σ).symm.toLinearMap`. Establish `hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))` using `fun _ => rfl`. Set `φc` to `LinearMap.toContinuousLinearMap φ`. Establish `hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} => ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖)`.

Use `⟨‖φc‖, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨ξ, rfl⟩`. Use `show ‖φ ξ‖ ≤ _`. Combine the equalities or inequalities in the displayed calculation. Use `set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)`.

Establish `hξ₀ : φ ξ₀ = τ (yv x)`. Rewrite using `[hφ]`. Simplify using `only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]`. Both sides reduce to the same expression. Establish `hne : ξ₀ ≠ 0`.

Introduce `h0`. Rewrite `hξ₀` using `[h0, map_zero]`. Conclude with `(map_ne_zero τ).mpr hx hξ₀.symm`. Use `set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀`. Establish `hξ₁ : ‖ξ₁‖ ≤ 1` using `le_of_eq (norm_smul_inv_norm hne)`.

Establish `hφ₁ : φ ξ₁ ≠ 0`. Rewrite using `[map_smul, hξ₀, smul_eq_mul]`. Use `mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)` and prove the remaining obligations. Conclude with `(norm_ne_zero_iff.mpr hne)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hφ]`. Conclude with `le_ciSup hbdd ⟨ξ₁, hξ₁⟩`.
-/
theorem archDualNorm_pos (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by
  set σ := τ.comp (algebraMap F K)
  let φ : FibreSpace h σ →ₗ[ℂ] ℂ := (ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ
    (FibreSpace.equiv h σ).symm.toLinearMap
  have hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ)) :=
    fun _ => rfl
  let φc := LinearMap.toContinuousLinearMap φ
  have hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} =>
      ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖) := by
    refine ⟨‖φc‖, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    show ‖φ ξ‖ ≤ _
    calc ‖φ ξ‖ = ‖φc ξ‖ := rfl
      _ ≤ ‖φc‖ * ‖(ξ : FibreSpace h σ)‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * 1 := mul_le_mul_of_nonneg_left ξ.2 (norm_nonneg φc)
      _ = ‖φc‖ := mul_one _
  set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)
  have hξ₀ : φ ξ₀ = τ (yv x) := by
    rw [hφ]
    simp only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, one_mul]
    rfl
  have hne : ξ₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ₀
    exact (map_ne_zero τ).mpr hx hξ₀.symm
  set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀
  have hξ₁ : ‖ξ₁‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hne)
  have hφ₁ : φ ξ₁ ≠ 0 := by
    rw [map_smul, hξ₀, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)
    exact_mod_cast (norm_ne_zero_iff.mpr hne)
  calc (0 : ℝ) < ‖φ ξ₁‖ := norm_pos_iff.mpr hφ₁
    _ ≤ archDualNorm h τ yv := by
      rw [hφ]
      exact le_ciSup hbdd ⟨ξ₁, hξ₁⟩

end HeightOfPointAlt

open HeightOfPointAlt

/- English proof (translation)
Introduce `F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv`. Establish `hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x` using `fun x => (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)`. Establish `hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k)`. Introduce `c`. Simplify using `only [map_sum, map_smulₛₗ, smul_eq_mul]`.

Use `set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v => ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef`. Establish `hM0 : ∀ v, 0 ≤ M v` using `fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _`. Establish `hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v` using `fun v k => by show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))`. Conclude with `le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))) (Finite.bddAbove_range _) k`. Establish `hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v`.

Introduce `v x`. Take `⟨c, rfl⟩` from `hspan x`. Rewrite using `[hyvx]`. Use `adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hdual : ∀ v, dualNormAt v yv = M v`. Introduce `v`. Establish `hbdd : BddAbove (Set.range fun x : W => NumberField.HeightOneSpectrum.adicAbv K v (yv x))`. Use `⟨M v, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hle v x`. Unfold `dualNormAt`. Use `le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_` and prove the remaining obligations. Conclude with `Real.iSup_le (fun k => le_ciSup hbdd (w k)) (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)`.

Establish `hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v`. Introduce `v`. Rewrite using `[gaussNorm_eq_gaussNormOf]`. Use `le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_` and prove the remaining obligations. Rewrite using `[coeff_sum]`.

Use `adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_C_mul, map_mul, coeff_X]`. Use `split_ifs`. Rewrite using `[map_one, mul_one]`. Conclude with `hleM v k`.

Rewrite using `[map_zero, mul_zero]`. Conclude with `hM0 v`. Use `Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)` and prove the remaining obligations. Establish `hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) = yv (w k)`. Rewrite using `[coeff_sum, Finset.sum_eq_single k]`.

Rewrite using `[coeff_C_mul, coeff_X, if_pos rfl, mul_one]`. Introduce `j _ hj`. Rewrite using `[coeff_C_mul, coeff_X, if_neg, mul_zero]`. Introduce `hjk`. Conclude with `hj (Finsupp.single_left_injective one_ne_zero hjk)`.

Introduce `hk`. Conclude with `absurd (Finset.mem_univ k) hk`. Rewrite using `[← hc]`. Conclude with `le_gaussNormOf _ _ _`. Choose the witnesses or unpack the hypotheses as in `⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, ne_eq, not_not] at hcon`. Apply `hyv` to reduce the goal to its premises. Use extensionality with `x`. Take `⟨c, rfl⟩` from `hspan x`.

Rewrite using `[hyvx]`. Simplify using `[hcon]`. Establish `hMpos : ∀ v, 0 < M v` using `fun v => lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)`. Establish `hMfin : (Function.support fun v => Real.log (M v)).Finite`. Use `(Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0}) fun k hk => finite_adicAbv_ne_one hk).subset ?_` and prove the remaining obligations.

Introduce `v hv`. Assume the negation of the conclusion as `hnot`. Simplify using `only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot`. Apply `hv` to reduce the goal to its premises. Establish `h1 : M v = 1`.

Use `le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_` and prove the remaining obligations. Distinguish the cases in `hk : yv (w k) = 0`. Rewrite using `[hk, map_zero]`. Conclude with `zero_le_one`. Conclude with `(hnot k hk).le`.

Rewrite using `[← hnot k₀ hk₀]`. Conclude with `hleM v k₀`. Simplify using `only [h1, Real.log_one]`. Use `⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite`.

Use `(finite_adicAbv_ne_one hx).subset ?_` and prove the remaining obligations. Introduce `v hv h1`. Apply `hv` to reduce the goal to its premises. Simplify using `only [h1, Real.log_one]`. Establish `e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) = Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v)`.

Introduce `v`. Rewrite using `[hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']`. Establish `e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) = Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv)`. Introduce `τ`. Conclude with `Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx)) (archDualNorm_pos h τ yv x hx).ne'`.

Establish `e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) = ∑ᶠ v, Real.log (M v)` using `finsum_congr fun v => by rw [hdual]`. Unfold `heightWith`. Simplify using `only [e1, e2]`. Rewrite using `[finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx, sum_log_norm_embeddings hx, e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem heightOfPoint : HeightOfPoint.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv
  have hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)
  have hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k) := by
    intro c
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef
  have hM0 : ∀ v, 0 ≤ M v := fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _
  have hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v := fun v k =>
    by
    show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))
    exact le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)))
      (Finite.bddAbove_range _) k
  have hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v := by
    intro v x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) :=
          mul_le_mul_of_nonneg_right (adicAbv_intToField_le_one v (c k)) (AbsoluteValue.nonneg _ _)
      _ ≤ M v := by rw [one_mul]; exact hleM v k
  have hdual : ∀ v, dualNormAt v yv = M v := by
    intro v
    have hbdd : BddAbove (Set.range fun x : W =>
        NumberField.HeightOneSpectrum.adicAbv K v (yv x)) := by
      refine ⟨M v, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle v x
    unfold dualNormAt
    refine le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_
    exact Real.iSup_le (fun k => le_ciSup hbdd (w k))
      (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)
  have hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v := by
    intro v
    rw [gaussNorm_eq_gaussNormOf]
    refine le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_
    · rw [coeff_sum]
      refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
      rw [coeff_C_mul, map_mul, coeff_X]
      split_ifs
      · rw [map_one, mul_one]; exact hleM v k
      · rw [map_zero, mul_zero]; exact hM0 v
    · refine Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)
      have hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) =
          yv (w k) := by
        rw [coeff_sum, Finset.sum_eq_single k]
        · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
          intro hjk
          exact hj (Finsupp.single_left_injective one_ne_zero hjk)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [← hc]
      exact le_gaussNormOf _ _ _

  obtain ⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hyv
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    simp [hcon]
  have hMpos : ∀ v, 0 < M v := fun v =>
    lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)
  have hMfin : (Function.support fun v => Real.log (M v)).Finite := by
    refine (Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0})
      fun k hk => finite_adicAbv_ne_one hk).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    have h1 : M v = 1 := by
      refine le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_
      · by_cases hk : yv (w k) = 0
        · rw [hk, map_zero]; exact zero_le_one
        · exact (hnot k hk).le
      · rw [← hnot k₀ hk₀]; exact hleM v k₀
    simp only [h1, Real.log_one]
  refine ⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩
  have hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite := by
    refine (finite_adicAbv_ne_one hx).subset ?_
    intro v hv h1
    apply hv
    simp only [h1, Real.log_one]
  have e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v) := by
    intro v
    rw [hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']
  have e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) =
      Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv) := by
    intro τ
    exact Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx))
      (archDualNorm_pos h τ yv x hx).ne'
  have e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) =
      ∑ᶠ v, Real.log (M v) := finsum_congr fun v => by rw [hdual]
  unfold heightWith
  simp only [e1, e2]
  rw [finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx,
    sum_log_norm_embeddings hx, e3]
  ring

/- English proof (translation)
The claim follows from `heightOfPoint`.
-/
theorem HeightOfPoint.proof (_h1 : GaussNormBasic.Statement) : HeightOfPoint.Statement :=
  heightOfPoint

end

end GroundTheory.Heights₂.Heights
