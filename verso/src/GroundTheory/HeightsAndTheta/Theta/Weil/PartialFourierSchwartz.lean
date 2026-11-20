import Mathlib

namespace GroundTheory.Heights₂.Theta

open MeasureTheory SchwartzMap Real Complex Filter Topology
open scoped FourierTransform ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] {ι : Type} [Fintype ι]

section Slice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Establish `h : (fun v' : (EuclideanSpace ℝ ι) ↦ f (x, v')) = (fun q ↦ f (q + (x, 0))) ∘ (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι))`. Use function extensionality and compare the values at `v'`. Simplify using the standard rewrite rules. Establish `hc : ContDiff ℝ ∞ (fun q ↦ f (q + (x, 0)))` using `hf.comp (contDiff_id.add contDiff_const)`. Rewrite using `[h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]`.

Use `(ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_` and prove the remaining obligations. Establish `h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)‖ ≤ 1` using `Finset.prod_le_one (fun _ _ ↦ by positivity) fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ V₁ (EuclideanSpace ℝ ι)`. Establish `h2 : (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)) v + (x, 0) = (x, v)` using `by simp`. Rewrite using `[h2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_iteratedFDeriv_slice_le {f : V₁ × (EuclideanSpace ℝ ι) → E} (hf : ContDiff ℝ ∞ f) (x : V₁) (v : (EuclideanSpace ℝ ι))
    (n : ℕ) : ‖iteratedFDeriv ℝ n (fun v' ↦ f (x, v')) v‖ ≤ ‖iteratedFDeriv ℝ n f (x, v)‖ := by
  have h : (fun v' : (EuclideanSpace ℝ ι) ↦ f (x, v')) =
      (fun q ↦ f (q + (x, 0))) ∘ (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)) := by
    funext v'
    simp
  have hc : ContDiff ℝ ∞ (fun q ↦ f (q + (x, 0))) := hf.comp (contDiff_id.add contDiff_const)
  rw [h, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ ↦ by positivity) fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ V₁ (EuclideanSpace ℝ ι)
  have h2 : (ContinuousLinearMap.inr ℝ V₁ (EuclideanSpace ℝ ι)) v + (x, 0) = (x, v) := by simp
  rw [h2]
  calc _ ≤ ‖iteratedFDeriv ℝ n f (x, v)‖ * 1 := by gcongr
    _ = _ := mul_one _

def schwartzSlice (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) : 𝓢((EuclideanSpace ℝ ι), E) where
  toFun v := F (x, v)
  smooth' := (F.smooth ⊤).comp (contDiff_const.prodMk contDiff_id)
  decay' k n := by
    obtain ⟨C, -, hC⟩ := F.decay k n
    refine ⟨C, fun v ↦ ?_⟩
    calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun v' ↦ F (x, v')) v‖
        ≤ ‖(x, v)‖ ^ k * ‖iteratedFDeriv ℝ n F (x, v)‖ := by
          gcongr
          · exact norm_snd_le (x, v)
          · exact norm_iteratedFDeriv_slice_le (F.smooth ⊤) x v n
      _ ≤ C := hC _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem schwartzSlice_apply (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) (v : (EuclideanSpace ℝ ι)) :
    schwartzSlice F x v = F (x, v) := rfl

/- English proof (translation)
Use `SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun v ↦ ?_` and prove the remaining obligations. Establish `hsm : ContDiffAt ℝ n (schwartzSlice F x) v` using `((schwartzSlice F x).smooth ⊤).contDiffAt.of_le (by exact_mod_cast le_top)`. Establish `hcoe : (((‖x‖ ^ j) • schwartzSlice F x : 𝓢((EuclideanSpace ℝ ι), E)) : (EuclideanSpace ℝ ι) → E) = (‖x‖ ^ j) • (schwartzSlice F x : (EuclideanSpace ℝ ι) → E)` using `rfl`. Rewrite using `[hcoe, iteratedFDeriv_const_smul_apply hsm, norm_smul, Real.norm_of_nonneg (by positivity)]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `norm_snd_le (x, v)`. Conclude with `norm_fst_le (x, v)`. Conclude with `norm_iteratedFDeriv_slice_le (F.smooth ⊤) x v n`. Use `_ = ‖(x, v)‖ ^ (j + k) * ‖iteratedFDeriv ℝ n F (x, v)‖ := by ring`. Use `_ ≤ _ := F.le_seminorm ℝ (j + k) n (x, v)`.
-/
theorem seminorm_smul_schwartzSlice_le (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) (j k n : ℕ) :
    SchwartzMap.seminorm ℝ k n ((‖x‖ ^ j) • schwartzSlice F x) ≤
      SchwartzMap.seminorm ℝ (j + k) n F := by
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun v ↦ ?_
  have hsm : ContDiffAt ℝ n (schwartzSlice F x) v :=
    ((schwartzSlice F x).smooth ⊤).contDiffAt.of_le (by exact_mod_cast le_top)
  have hcoe : (((‖x‖ ^ j) • schwartzSlice F x : 𝓢((EuclideanSpace ℝ ι), E)) : (EuclideanSpace ℝ ι) → E) =
      (‖x‖ ^ j) • (schwartzSlice F x : (EuclideanSpace ℝ ι) → E) := rfl
  rw [hcoe, iteratedFDeriv_const_smul_apply hsm, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  calc ‖v‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (schwartzSlice F x) v‖)
      ≤ ‖(x, v)‖ ^ k * (‖(x, v)‖ ^ j * ‖iteratedFDeriv ℝ n F (x, v)‖) := by
        gcongr
        · exact norm_snd_le (x, v)
        · exact norm_fst_le (x, v)
        · exact norm_iteratedFDeriv_slice_le (F.smooth ⊤) x v n
    _ = ‖(x, v)‖ ^ (j + k) * ‖iteratedFDeriv ℝ n F (x, v)‖ := by ring
    _ ≤ _ := F.le_seminorm ℝ (j + k) n (x, v)

/- English proof (translation)
Use `set r : ℕ := Module.finrank ℝ (EuclideanSpace ℝ ι) + 1`. Use `set C : ℝ := 2 ^ r * ((Finset.Iic (r, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G`. Use `⟨fun v ↦ C * (1 + ‖v‖) ^ (-(r : ℝ)), (integrable_one_add_norm (by simp [r])).const_mul C, fun x v ↦ ?_⟩` and prove the remaining obligations. Establish `h` using `G.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (r, 0)) (k := r) (n := 0) le_rfl le_rfl (x, v)`. Rewrite `h` using `[norm_iteratedFDeriv_zero]`.

Establish `h1 : (1 + ‖v‖) ^ r ≤ (1 + ‖(x, v)‖) ^ r` using `by gcongr`. Conclude with `norm_snd_le (x, v)`. Establish `hpos : 0 < (1 + ‖v‖) ^ r` using `by positivity`. Use `show ‖G (x, v)‖ ≤ C * (1 + ‖v‖) ^ (-(r : ℝ))`. Rewrite using `[Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_comm]`. Use `gcongr`. Use `_ ≤ C := h`.
-/
theorem exists_integrable_bound_snd (G : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) :
    ∃ b : (EuclideanSpace ℝ ι) → ℝ, Integrable b ∧ ∀ x v, ‖G (x, v)‖ ≤ b v := by
  set r : ℕ := Module.finrank ℝ (EuclideanSpace ℝ ι) + 1
  set C : ℝ := 2 ^ r * ((Finset.Iic (r, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨fun v ↦ C * (1 + ‖v‖) ^ (-(r : ℝ)),
    (integrable_one_add_norm (by simp [r])).const_mul C, fun x v ↦ ?_⟩
  have h := G.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (r, 0)) (k := r) (n := 0) le_rfl le_rfl
    (x, v)
  rw [norm_iteratedFDeriv_zero] at h
  have h1 : (1 + ‖v‖) ^ r ≤ (1 + ‖(x, v)‖) ^ r := by
    gcongr
    exact norm_snd_le (x, v)
  have hpos : 0 < (1 + ‖v‖) ^ r := by positivity
  show ‖G (x, v)‖ ≤ C * (1 + ‖v‖) ^ (-(r : ℝ))
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖G (x, v)‖ * (1 + ‖v‖) ^ r ≤ (1 + ‖(x, v)‖) ^ r * ‖G (x, v)‖ := by
        rw [mul_comm]
        gcongr
    _ ≤ C := h

end Slice

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) (p : V₁ × (EuclideanSpace ℝ ι)) : E :=
  𝓕 (fun v ↦ F (p.1, v)) p.2

/- English proof (translation)
Rewrite using `[partialFourierSnd, Real.fourier_eq]`.
-/
theorem partialFourierSnd_apply (F : V₁ × (EuclideanSpace ℝ ι) → E) (x : V₁) (w : (EuclideanSpace ℝ ι)) :
    partialFourierSnd F (x, w) = ∫ v, 𝐞 (-inner ℝ v w) • F (x, v) := by
  rw [partialFourierSnd, Real.fourier_eq]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Conclude with `partialFourierSnd_apply F p.1 p.2`.
-/
theorem partialFourierSnd_eq (F : V₁ × (EuclideanSpace ℝ ι) → E) :
    partialFourierSnd F = fun p ↦ ∫ v, ((𝐞 (-inner ℝ v p.2) : ℂ)) • F (p.1, v) := by
  funext p
  exact partialFourierSnd_apply F p.1 p.2

/- English proof (translation)
Set `T : 𝓢((EuclideanSpace ℝ ι), E) →L[ℝ] 𝓢((EuclideanSpace ℝ ι), E)` to `SchwartzMap.fourierTransformCLM ℝ`. Set `q : Seminorm ℝ 𝓢((EuclideanSpace ℝ ι), E)` to `(SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap`. Establish `hq : Continuous q` using `((schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E).continuous_seminorm (k, 0)).comp T.continuous`. Take `⟨s, C₀, -, hC₀⟩` from `Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E) q hq`. Use `set M : ℝ := ∑ i ∈ s, SchwartzMap.seminorm ℝ (j + i.1) i.2 F`.

Use `⟨C₀ * M, fun x w ↦ ?_⟩` and prove the remaining obligations. Use `set g : 𝓢((EuclideanSpace ℝ ι), E) := (‖x‖ ^ j) • schwartzSlice F x`. Establish `hTg : T g w = (‖x‖ ^ j) • partialFourierSnd F (x, w)`. Simplify using `only [g, map_smul, smul_apply]`. Both sides reduce to the same expression.

Establish `h2 : ‖w‖ ^ k * ‖T g w‖ ≤ q g` using `(T g).norm_pow_mul_le_seminorm ℝ k w`. Establish `h3 : q g ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g`. Use `hC₀ g` as an intermediate fact. Simplify `this` using `[NNReal.smul_def]`. Establish `h4 : (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g ≤ M`.

Use `Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _) fun i hi ↦ ?_` and prove the remaining obligations. Use `(seminorm_smul_schwartzSlice_le F x j i.1 i.2).trans ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i : ℕ × ℕ ↦ SchwartzMap.seminorm ℝ (j + i.1) i.2 F) (fun _ _ ↦ apply_nonneg _ _) hi`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hTg, norm_smul, Real.norm_of_nonneg (by positivity)]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ q g := h2`. Use `_ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g := h3`. Use `_ ≤ C₀ * M := by gcongr`.
-/
theorem exists_bound_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (j k : ℕ) :
    ∃ C, ∀ x w, ‖x‖ ^ j * (‖w‖ ^ k * ‖partialFourierSnd F (x, w)‖) ≤ C := by
  let T : 𝓢((EuclideanSpace ℝ ι), E) →L[ℝ] 𝓢((EuclideanSpace ℝ ι), E) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢((EuclideanSpace ℝ ι), E) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E).continuous_seminorm (k, 0)).comp T.continuous
  obtain ⟨s, C₀, -, hC₀⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (EuclideanSpace ℝ ι) E) q hq
  set M : ℝ := ∑ i ∈ s, SchwartzMap.seminorm ℝ (j + i.1) i.2 F
  refine ⟨C₀ * M, fun x w ↦ ?_⟩
  set g : 𝓢((EuclideanSpace ℝ ι), E) := (‖x‖ ^ j) • schwartzSlice F x
  have hTg : T g w = (‖x‖ ^ j) • partialFourierSnd F (x, w) := by
    simp only [g, map_smul, smul_apply]
    rfl
  have h2 : ‖w‖ ^ k * ‖T g w‖ ≤ q g := (T g).norm_pow_mul_le_seminorm ℝ k w
  have h3 : q g ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g := by
    have := hC₀ g
    simpa [NNReal.smul_def] using this
  have h4 : (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g ≤ M := by
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _)
      fun i hi ↦ ?_
    refine (seminorm_smul_schwartzSlice_le F x j i.1 i.2).trans ?_
    exact Finset.single_le_sum (f := fun i : ℕ × ℕ ↦ SchwartzMap.seminorm ℝ (j + i.1) i.2 F)
      (fun _ _ ↦ apply_nonneg _ _) hi
  calc ‖x‖ ^ j * (‖w‖ ^ k * ‖partialFourierSnd F (x, w)‖) = ‖w‖ ^ k * ‖T g w‖ := by
        rw [hTg, norm_smul, Real.norm_of_nonneg (by positivity)]
        ring
    _ ≤ q g := h2
    _ ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ ι) E)) g := h3
    _ ≤ C₀ * M := by gcongr

variable (V₁ ι) in

abbrev fstIncl : V₁ × (EuclideanSpace ℝ ι) →L[ℝ] V₁ × (EuclideanSpace ℝ ι) :=
  (ContinuousLinearMap.inl ℝ V₁ (EuclideanSpace ℝ ι)).comp (ContinuousLinearMap.fst ℝ V₁ (EuclideanSpace ℝ ι))

variable (V₁ ι) in

def sndInnerCLM : V₁ × (EuclideanSpace ℝ ι) →L[ℝ] (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (V₁ × (EuclideanSpace ℝ ι)) (EuclideanSpace ℝ ι) ℝ).flip (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι)))

/- English proof (translation)
Simplify using `[sndInnerCLM]`.
-/
theorem sndInnerCLM_apply (p q : V₁ × (EuclideanSpace ℝ ι)) :
    sndInnerCLM V₁ ι p q = inner ℝ p.2 q.2 := by
  simp [sndInnerCLM]

def partialFourierDeriv (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) : 𝓢(V₁ × (EuclideanSpace ℝ ι), V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.compL ℝ (V₁ × (EuclideanSpace ℝ ι)) (V₁ × (EuclideanSpace ℝ ι)) E).flip
      (fstIncl V₁ ι)) (SchwartzMap.fderivCLM ℝ (V₁ × (EuclideanSpace ℝ ι)) E F) +
    (-(2 * π * I) : ℂ) • SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.smulRightL ℝ (V₁ × (EuclideanSpace ℝ ι)) E).flip
      (sndInnerCLM V₁ ι).hasTemperateGrowth F

/- English proof (translation)
Simplify using `[partialFourierDeriv, SchwartzMap.postcompCLM_apply, SchwartzMap.bilinLeftCLM_apply, sndInnerCLM_apply, fstIncl]`.
-/
theorem partialFourierDeriv_apply (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (p q : V₁ × (EuclideanSpace ℝ ι)) :
    partialFourierDeriv F p q =
      fderiv ℝ F p (q.1, 0) + (-(2 * π * I) : ℂ) • (inner ℝ p.2 q.2 • F p) := by
  simp [partialFourierDeriv, SchwartzMap.postcompCLM_apply, SchwartzMap.bilinLeftCLM_apply,
    sndInnerCLM_apply, fstIncl]

/- English proof (translation)
Establish `he : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : Circle) : ℂ)) (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))) q` using `(hasFDerivAt_fourierChar_neg_bilinear_right (innerSL ℝ) v q.2).comp q hasFDerivAt_snd`. Establish `hpair : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) (fstIncl V₁ ι) q`. Establish `h : (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) = fun q' ↦ fstIncl V₁ ι q' + ((0 : V₁), v)`. Use function extensionality and compare the values at `q'`. Simplify using the standard rewrite rules.

Rewrite using `[h]`. Conclude with `(fstIncl V₁ ι).hasFDerivAt.add_const _`. Establish `hF : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ F (q'.1, v)) ((fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι)) q` using `(F.differentiableAt.hasFDerivAt).comp q hpair`. Establish `hs : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v)) ((((𝐞 (-inner ℝ v q.2) : Circle) : ℂ)) • (fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι) + (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp (ContinuousLinearM …` using `he.smul hF`. Use `hs.congr_fderiv (ContinuousLinearMap.ext fun r ↦ ?_)` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.smul_apply, partialFourierDeriv_apply]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]`. Rewrite using `[← Complex.coe_smul, smul_add, smul_smul, smul_smul]`. Use `congr 1`. Put the polynomial expressions in normal form.

Both sides reduce to the same expression.
-/
theorem hasFDerivAt_partialFourierSnd_integrand (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (v : (EuclideanSpace ℝ ι)) (q : V₁ × (EuclideanSpace ℝ ι)) :
    HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
      (((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)) q := by
  have he : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : Circle) : ℂ))
      (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp
        (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))) q :=
    (hasFDerivAt_fourierChar_neg_bilinear_right (innerSL ℝ) v q.2).comp q hasFDerivAt_snd
  have hpair : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) (fstIncl V₁ ι) q := by
    have h : (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ (q'.1, v)) =
        fun q' ↦ fstIncl V₁ ι q' + ((0 : V₁), v) := by
      funext q'
      simp
    rw [h]
    exact (fstIncl V₁ ι).hasFDerivAt.add_const _
  have hF : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ F (q'.1, v))
      ((fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι)) q :=
    (F.differentiableAt.hasFDerivAt).comp q hpair
  have hs : HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
      ((((𝐞 (-inner ℝ v q.2) : Circle) : ℂ)) • (fderiv ℝ F (q.1, v)).comp (fstIncl V₁ ι) +
        (((-2 * π * I * 𝐞 (-(innerSL ℝ) v q.2)) • (ofRealCLM ∘L ((innerSL ℝ) v))).comp
          (ContinuousLinearMap.snd ℝ V₁ (EuclideanSpace ℝ ι))).smulRight (F (q.1, v))) q := he.smul hF
  refine hs.congr_fderiv (ContinuousLinearMap.ext fun r ↦ ?_)
  rw [ContinuousLinearMap.smul_apply, partialFourierDeriv_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ofRealCLM_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [← Complex.coe_smul, smul_add, smul_smul, smul_smul]
  congr 1
  ring_nf
  rfl

/- English proof (translation)
Take `⟨b, hb, hbF⟩` from `exists_integrable_bound_snd (partialFourierDeriv F)`. Take `⟨b₀, hb₀, hb₀F⟩` from `exists_integrable_bound_snd F`. Establish `hce : ∀ w : (EuclideanSpace ℝ ι), Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v w) : Circle) : ℂ)` using `fun w ↦ continuous_subtype_val.comp (continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)`. Establish `hcont : ∀ q : V₁ × (EuclideanSpace ℝ ι), Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v)` using `fun q ↦ (hce q.2).smul (F.continuous.comp (continuous_const.prodMk continuous_id))`. Establish `hcont' : Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)` using `(hce p.2).smul ((partialFourierDeriv F).continuous.comp (continuous_const.prodMk continuous_id))`.

Establish `hm : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v)) volume` using `Eventually.of_forall fun q ↦ (hcont q).aestronglyMeasurable`. Establish `hi : Integrable (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v p.2) : ℂ)) • F (p.1, v)) volume`. Use `hb₀.mono' (hcont p).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Circle.norm_coe, one_mul]`. Conclude with `hb₀F _ _`.

Establish `hm' : AEStronglyMeasurable (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) volume` using `hcont'.aestronglyMeasurable`. Establish `hbd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))), ‖((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)‖ ≤ b v`. Use `Eventually.of_forall fun v q _ ↦ ?_` and prove the remaining obligations. Rewrite using `[norm_smul, Circle.norm_coe, one_mul]`. Conclude with `hbF _ _`.

Establish `hd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))), HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v)) (((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)) q` using `Eventually.of_forall fun v q _ ↦ hasFDerivAt_partialFourierSnd_integrand F v q`. Establish `key : HasFDerivAt (fun q : V₁ × (EuclideanSpace ℝ ι) ↦ ∫ v, ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v)) (∫ v, ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) p` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := E) (H := V₁ × (EuclideanSpace ℝ ι)) Filter.univ_mem hm hi hm' hbd hb hd`. Rewrite using `[partialFourierSnd_eq (F : V₁ × (EuclideanSpace ℝ ι) → E)]`. Use `key using 1` and compare the differences between its conclusion and the goal. Conclude with `congrFun (partialFourierSnd_eq _) p`.
-/
theorem hasFDerivAt_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E))
    (p : V₁ × (EuclideanSpace ℝ ι)) :
    HasFDerivAt (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E))
      (partialFourierSnd (partialFourierDeriv F : V₁ × (EuclideanSpace ℝ ι) →
        (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E)) p) p := by
  obtain ⟨b, hb, hbF⟩ := exists_integrable_bound_snd (partialFourierDeriv F)
  obtain ⟨b₀, hb₀, hb₀F⟩ := exists_integrable_bound_snd F
  have hce : ∀ w : (EuclideanSpace ℝ ι),
      Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v w) : Circle) : ℂ) := fun w ↦
    continuous_subtype_val.comp (continuous_fourierChar.comp
      (continuous_id.inner continuous_const).neg)
  have hcont : ∀ q : V₁ × (EuclideanSpace ℝ ι),
      Continuous fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v) :=
    fun q ↦ (hce q.2).smul (F.continuous.comp (continuous_const.prodMk continuous_id))
  have hcont' : Continuous fun v : (EuclideanSpace ℝ ι) ↦
      ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v) :=
    (hce p.2).smul ((partialFourierDeriv F).continuous.comp
      (continuous_const.prodMk continuous_id))
  have hm : ∀ᶠ q in 𝓝 p, AEStronglyMeasurable
      (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v)) volume :=
    Eventually.of_forall fun q ↦ (hcont q).aestronglyMeasurable
  have hi : Integrable
      (fun v : (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v p.2) : ℂ)) • F (p.1, v)) volume := by
    refine hb₀.mono' (hcont p).aestronglyMeasurable (Eventually.of_forall fun v ↦ ?_)
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hb₀F _ _
  have hm' : AEStronglyMeasurable (fun v : (EuclideanSpace ℝ ι) ↦
      ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) volume :=
    hcont'.aestronglyMeasurable
  have hbd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))),
      ‖((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)‖ ≤ b v := by
    refine Eventually.of_forall fun v q _ ↦ ?_
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hbF _ _
  have hd : ∀ᵐ v ∂(volume : Measure (EuclideanSpace ℝ ι)), ∀ q ∈ (Set.univ : Set (V₁ × (EuclideanSpace ℝ ι))),
      HasFDerivAt (fun q' : V₁ × (EuclideanSpace ℝ ι) ↦ ((𝐞 (-inner ℝ v q'.2) : ℂ)) • F (q'.1, v))
        (((𝐞 (-inner ℝ v q.2) : ℂ)) • partialFourierDeriv F (q.1, v)) q :=
    Eventually.of_forall fun v q _ ↦ hasFDerivAt_partialFourierSnd_integrand F v q
  have key : HasFDerivAt (fun q : V₁ × (EuclideanSpace ℝ ι) ↦
      ∫ v, ((𝐞 (-inner ℝ v q.2) : ℂ)) • F (q.1, v))
      (∫ v, ((𝐞 (-inner ℝ v p.2) : ℂ)) • partialFourierDeriv F (p.1, v)) p :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (E := E)
      (H := V₁ × (EuclideanSpace ℝ ι)) Filter.univ_mem hm hi hm' hbd hb hd
  rw [partialFourierSnd_eq (F : V₁ × (EuclideanSpace ℝ ι) → E)]
  convert key using 1
  exact congrFun (partialFourierSnd_eq _) p

/- English proof (translation)
The claim follows from `funext fun p ↦ (hasFDerivAt_partialFourierSnd F p).fderiv`.
-/
theorem fderiv_partialFourierSnd (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) :
    fderiv ℝ (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) =
      partialFourierSnd (partialFourierDeriv F : V₁ × (EuclideanSpace ℝ ι) →
        (V₁ × (EuclideanSpace ℝ ι) →L[ℝ] E)) :=
  funext fun p ↦ (hasFDerivAt_partialFourierSnd F p).fderiv

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `E _ _ _ F`. Conclude with `contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p ↦ (hasFDerivAt_partialFourierSnd F p).continuousAt)`. Consider the case `succ n ih`.

Introduce `E _ _ _ F`. Establish `h : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1` using `by push_cast; rfl`. Rewrite using `[h, contDiff_succ_iff_fderiv]`. Use `⟨fun p ↦ (hasFDerivAt_partialFourierSnd F p).differentiableAt, fun h' ↦ ?_, ?_⟩` and prove the remaining obligations. Conclude with `absurd h' (by simp)`.

Rewrite using `[fderiv_partialFourierSnd]`. Conclude with `ih _ (partialFourierDeriv F)`.
-/
theorem contDiff_partialFourierSnd (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)),
      ContDiff ℝ n (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) := by
  induction n with
  | zero =>
    intro E _ _ _ F
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun p ↦
      (hasFDerivAt_partialFourierSnd F p).continuousAt)
  | succ n ih =>
    intro E _ _ _ F
    have h : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [h, contDiff_succ_iff_fderiv]
    refine ⟨fun p ↦ (hasFDerivAt_partialFourierSnd F p).differentiableAt, fun h' ↦ ?_, ?_⟩
    · exact absurd h' (by simp)
    · rw [fderiv_partialFourierSnd]
      exact ih _ (partialFourierDeriv F)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `E _ _ _ F k`. Take `⟨C₁, h₁⟩` from `exists_bound_partialFourierSnd F k 0`. Take `⟨C₂, h₂⟩` from `exists_bound_partialFourierSnd F 0 k`.

Use `⟨C₁ + C₂, fun p ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[norm_iteratedFDeriv_zero]`. Establish `h1` using `h₁ p.1 p.2`. Establish `h2` using `h₂ p.1 p.2`. Simplify using `only [pow_zero, one_mul, Prod.mk.eta] at h1 h2`.

Establish `hp : ‖p‖ ^ k ≤ ‖p.1‖ ^ k + ‖p.2‖ ^ k`. Rewrite using `[Prod.norm_def]`. Break down `le_total ‖p.1‖ ‖p.2‖ with h | h` into its components or cases. Rewrite using `[max_eq_right h]`. Combine the linear relations using `[pow_nonneg (norm_nonneg p.1) k]`.

Rewrite using `[max_eq_left h]`. Combine the linear relations using `[pow_nonneg (norm_nonneg p.2) k]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `succ n ih`. Introduce `E _ _ _ F k`.

Take `⟨C, hC⟩` from `ih _ (partialFourierDeriv F) k`. Use `⟨C, fun p ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← norm_iteratedFDeriv_fderiv, fderiv_partialFourierSnd]`. Conclude with `hC p`.
-/
theorem exists_bound_iteratedFDeriv_partialFourierSnd (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E))
      (k : ℕ), ∃ C, ∀ p : V₁ × (EuclideanSpace ℝ ι),
        ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)) p‖ ≤ C := by
  induction n with
  | zero =>
    intro E _ _ _ F k
    obtain ⟨C₁, h₁⟩ := exists_bound_partialFourierSnd F k 0
    obtain ⟨C₂, h₂⟩ := exists_bound_partialFourierSnd F 0 k
    refine ⟨C₁ + C₂, fun p ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero]
    have h1 := h₁ p.1 p.2
    have h2 := h₂ p.1 p.2
    simp only [pow_zero, one_mul, Prod.mk.eta] at h1 h2
    have hp : ‖p‖ ^ k ≤ ‖p.1‖ ^ k + ‖p.2‖ ^ k := by
      rw [Prod.norm_def]
      rcases le_total ‖p.1‖ ‖p.2‖ with h | h
      · rw [max_eq_right h]
        linarith [pow_nonneg (norm_nonneg p.1) k]
      · rw [max_eq_left h]
        linarith [pow_nonneg (norm_nonneg p.2) k]
    calc ‖p‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖
        ≤ (‖p.1‖ ^ k + ‖p.2‖ ^ k) * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ := by gcongr
      _ = ‖p.1‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ +
          ‖p.2‖ ^ k * ‖partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E) p‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add h1 h2
  | succ n ih =>
    intro E _ _ _ F k
    obtain ⟨C, hC⟩ := ih _ (partialFourierDeriv F) k
    refine ⟨C, fun p ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, fderiv_partialFourierSnd]
    exact hC p

def partialFourierSndSchwartz (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) : 𝓢(V₁ × (EuclideanSpace ℝ ι), E) where
  toFun := partialFourierSnd (F : V₁ × (EuclideanSpace ℝ ι) → E)
  smooth' := contDiff_infty.mpr fun n ↦ contDiff_partialFourierSnd n E F
  decay' k n := exists_bound_iteratedFDeriv_partialFourierSnd n E F k

/- English proof (translation)
The claim follows from `partialFourierSnd_apply _ _ _`.
-/
theorem partialFourierSndSchwartz_apply (F : 𝓢(V₁ × (EuclideanSpace ℝ ι), E)) (x : V₁) (w : (EuclideanSpace ℝ ι)) :
    partialFourierSndSchwartz F (x, w) = ∫ v, 𝐞 (-inner ℝ v w) • F (x, v) :=
  partialFourierSnd_apply _ _ _

end

end GroundTheory.Heights₂.Theta
