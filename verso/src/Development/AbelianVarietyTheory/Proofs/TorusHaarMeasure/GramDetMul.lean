import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.AbsNormEqProdCmTypeSq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndexRangeMulVecLinEqAbsNormDet
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.ValMul

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_mul, show Bᴴ * Nᴴ * (N * B) = Bᴴ * (Nᴴ * N) * B by simp only [Matrix.mul_assoc], Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`. Establish `h : star B.det * (Nᴴ * N).det * B.det = (Complex.normSq B.det : ℂ) * (Nᴴ * N).det`. Rewrite using `[Complex.normSq_eq_conj_mul_self, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Complex.re_ofReal_mul]`.
-/
private lemma det_gram_mul_right_re {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    [DecidableEq ι] (N : Matrix n ι ℂ) (B : Matrix ι ι ℂ) :
    ((N * B)ᴴ * (N * B)).det.re = Complex.normSq B.det * (Nᴴ * N).det.re := by
  rw [Matrix.conjTranspose_mul,
    show Bᴴ * Nᴴ * (N * B) = Bᴴ * (Nᴴ * N) * B by simp only [Matrix.mul_assoc],
    Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : star B.det * (Nᴴ * N).det * B.det = (Complex.normSq B.det : ℂ) * (Nᴴ * N).det := by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [h, Complex.re_ofReal_mul]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `r X x ι _ _ w hw hwΛ A hA`. Use `set w' : ι → Fin r → E := fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b with hw'`. Establish `hsmul : ∀ (c : 𝓞 E) (v : Fin r → E), c • v = (c : E) • v` using `fun c v => rfl`. Establish `hmat : ∀ τ : X.Ψ, (Matrix.of fun k a => τ.1 (w' a k)) = (Matrix.of fun k a => τ.1 (w a k)) * A.map (fun c => τ.1 (c : E))`. Introduce `τ`.

Use extensionality with `k a`. Simplify using `[Matrix.mul_apply, w', Finset.sum_apply, Algebra.smul_def, mul_comm]`. Establish `hnum : ∀ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))).det.re) = ‖τ.1 (A.det : E)‖ ^ 2 * (((_root_.ReciprocityTheory. …`. Introduce `τ`. Rewrite using `[hmat τ, ← Matrix.mul_assoc (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹, det_gram_mul_right_re]`.

Use `congr 1`. Establish `hd : (A.map fun c => τ.1 (c : E)).det = τ.1 (A.det : E)`. Use `RingHom.map_det (τ.1.comp (algebraMap (𝓞 E) E)) A` as an intermediate fact. Conclude with `this.symm`. Rewrite using `[hd, Complex.normSq_eq_norm_sq]`.

Establish `hspanE : Submodule.span E (Set.range w') = Submodule.span E (Set.range w)`. Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, rfl⟩`. Use `set B : Matrix ι ι E := A.map fun t => (t : E) with hB`. Establish `hBdet : IsUnit B.det`. Establish `h` using `RingHom.map_det (algebraMap (𝓞 E) E) A`.

Establish `h0 : ((A.det : 𝓞 E) : E) ≠ 0` using `by exact_mod_cast hA`. Use `isUnit_iff_ne_zero.mpr ?_` and prove the remaining obligations. Establish `hB' : B.det = ((A.det : 𝓞 E) : E)` using `h.symm`. Rewrite using `[hB']`. Conclude with `h0`.

Establish `hrec : ∑ a, B⁻¹ a c • w' a = w c`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [w', Finset.smul_sum, smul_smul, hB, Matrix.map_apply, mul_comm]`. Use `_ = ∑ b, (B * B⁻¹) b c • w b := by`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_smul]`. Use `_ = w c := by`. Rewrite using `[Matrix.mul_nonsing_inv B hBdet]`.

Simplify using `[Matrix.one_apply]`. Rewrite using `[← hrec]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Establish `hle1 : (Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup ≤ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup`. Rewrite using `[Submodule.toAddSubgroup_le]`.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.

Establish `hle2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤ X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup`. Introduce `v hv`. Establish `hv' : v ∈ Submodule.span (𝓞 E) (Set.range w)` using `hv`. Use `AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Use `Submodule.span_le.mpr ?_ hv'` and prove the remaining obligations.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hwΛ a`. Use `show v ∈ Submodule.span E (Set.range w)`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv'`. Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Establish `hidx : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℚ) = |Algebra.norm ℚ ((A.det : 𝓞 E) : E)|`. Set `ψ : (ι → 𝓞 E) →+ (Fin r → E)` to `{ toFun := fun c => ∑ b, ((c b : 𝓞 E) : E) • w b map_zero' := by simp map_add' := by`. Introduce `c d`.

Simplify using `[add_smul, Finset.sum_add_distrib] }`. Establish `hψ : ∀ c, ψ c = ∑ b, ((c b : 𝓞 E) : E) • w b` using `fun c => rfl`. Establish `hψinj : Function.Injective ψ`. Introduce `c d hcd`. Establish `h0 : ∑ b, (((c b : 𝓞 E) : E) - ((d b : 𝓞 E) : E)) • w b = 0`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← hψ, ← hψ]`. Conclude with `sub_eq_zero.mpr hcd`. Use function extensionality and compare the values at `b`. Use `Fintype.linearIndependent_iff.mp hw _ h0 b` as an intermediate fact.

Conclude with `RingOfIntegers.coe_injective (sub_eq_zero.mp this)`. Establish `hψmem : ∀ c, ψ c ∈ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup`. Introduce `c`. Use `show ψ c ∈ Submodule.span (𝓞 E) (Set.range w)`. Rewrite using `[hψ]`.

Use `Submodule.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← hsmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`. Set `φ : (ι → 𝓞 E) →+ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup` to `ψ.codRestrict _ hψmem`. Establish `hφsurj : Function.Surjective φ`.

Introduce and unpack `⟨v, hv⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv`. Use `⟨c, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ψ c = _`. Rewrite using `[hψ]`.

Conclude with `Finset.sum_congr rfl fun b _ => (hsmul (c b) (w b)).symm`. Establish `hlin : ∀ v : ι → 𝓞 E, ∑ a, v a • w' a = ψ (A.mulVec v)`. Introduce `v`. Rewrite using `[hψ]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [w', hsmul, Finset.smul_sum, smul_smul, mul_comm]`. Use `_ = ∑ b, ((A.mulVec v b : 𝓞 E) : E) • w b := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `push_cast`. Rewrite using `[Finset.sum_smul]`. Establish `hcomap : ((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.addSubgroupOf (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup).comap φ = (LinearMap.range A.mulVecLin).toAddSubgroup`. Use extensionality with `c`.

Rewrite using `[AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]`. Use `show ψ c ∈ Submodule.span (𝓞 E) (Set.range w') ↔ c ∈ LinearMap.range A.mulVecLin`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun, LinearMap.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`.

Conclude with `⟨v, hψinj (by rw [Matrix.mulVecLin_apply, ← hlin]; exact hv)⟩`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `⟨v, hlin v⟩`. Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφsurj, hcomap]`. Conclude with `_root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det ι A hA`.

Establish `hidxR : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℝ) = ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ)`. Conclude with `hidx` after adjusting the coercions. Establish `hN : ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) ≠ 0`. Establish `h0 : ((A.det : 𝓞 E) : E) ≠ 0`. Conclude with `hA` after adjusting the coercions.

Use `(Algebra.norm_ne_zero_iff (R := ℚ)).mpr h0` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib, ← _root_.GlobalTheory.abs_norm_eq_prod_cmType_sq r X, hspanE, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2, Nat.cast_mul, hidxR, mul_div_mul_left _ _ hN]`.
-/
theorem _root_.GlobalTheory.ValMul.value_mul_eq : ((∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ∀ A : Matrix ι ι (𝓞 E), A.det ≠ 0 → ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 ((fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b))).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X x ι _ _ w hw hwΛ A hA
  classical
  set w' : ι → Fin r → E := fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b with hw'
  have hsmul : ∀ (c : 𝓞 E) (v : Fin r → E), c • v = (c : E) • v := fun c v => rfl

  have hmat : ∀ τ : X.Ψ, (Matrix.of fun k a => τ.1 (w' a k)) =
      (Matrix.of fun k a => τ.1 (w a k)) * A.map (fun c => τ.1 (c : E)) := by
    intro τ
    ext k a
    simp [Matrix.mul_apply, w', Finset.sum_apply, Algebra.smul_def, mul_comm]
  have hnum : ∀ τ : X.Ψ, ((((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w' a k))).det.re) =
      ‖τ.1 (A.det : E)‖ ^ 2 * (((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))ᴴ *
      ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹ * Matrix.of fun k a => τ.1 (w a k))).det.re := by
    intro τ
    rw [hmat τ, ← Matrix.mul_assoc (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹, det_gram_mul_right_re]
    congr 1
    have hd : (A.map fun c => τ.1 (c : E)).det = τ.1 (A.det : E) := by
      have := RingHom.map_det (τ.1.comp (algebraMap (𝓞 E) E)) A
      exact this.symm
    rw [hd, Complex.normSq_eq_norm_sq]
  have hspanE : Submodule.span E (Set.range w') = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨c, rfl⟩
      set B : Matrix ι ι E := A.map fun t => (t : E) with hB
      have hBdet : IsUnit B.det := by
        have h := RingHom.map_det (algebraMap (𝓞 E) E) A
        have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hA
        refine isUnit_iff_ne_zero.mpr ?_
        have hB' : B.det = ((A.det : 𝓞 E) : E) := h.symm
        rw [hB']
        exact h0
      have hrec : ∑ a, B⁻¹ a c • w' a = w c := by
        calc ∑ a, B⁻¹ a c • w' a = ∑ a, ∑ b, (B b a * B⁻¹ a c) • w b := by
              refine Finset.sum_congr rfl fun a _ => ?_
              simp only [w', Finset.smul_sum, smul_smul, hB, Matrix.map_apply, mul_comm]
          _ = ∑ b, (B * B⁻¹) b c • w b := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Matrix.mul_apply, Finset.sum_smul]
          _ = w c := by
              rw [Matrix.mul_nonsing_inv B hBdet]
              simp [Matrix.one_apply]
      rw [← hrec]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have hle1 : (Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup ≤
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← hsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hle2 : (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
    intro v hv
    have hv' : v ∈ Submodule.span (𝓞 E) (Set.range w) := hv
    refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Submodule.span_le.mpr ?_ hv'
      rintro _ ⟨a, rfl⟩
      exact hwΛ a
    · show v ∈ Submodule.span E (Set.range w)
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv'
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hidx : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ ((A.det : 𝓞 E) : E)| := by
    let ψ : (ι → 𝓞 E) →+ (Fin r → E) :=
      { toFun := fun c => ∑ b, ((c b : 𝓞 E) : E) • w b
        map_zero' := by simp
        map_add' := by
          intro c d
          simp [add_smul, Finset.sum_add_distrib] }
    have hψ : ∀ c, ψ c = ∑ b, ((c b : 𝓞 E) : E) • w b := fun c => rfl
    have hψinj : Function.Injective ψ := by
      intro c d hcd
      have h0 : ∑ b, (((c b : 𝓞 E) : E) - ((d b : 𝓞 E) : E)) • w b = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hψ, ← hψ]
        exact sub_eq_zero.mpr hcd
      funext b
      have := Fintype.linearIndependent_iff.mp hw _ h0 b
      exact RingOfIntegers.coe_injective (sub_eq_zero.mp this)
    have hψmem : ∀ c, ψ c ∈ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup := by
      intro c
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w)
      rw [hψ]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [← hsmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    let φ : (ι → 𝓞 E) →+ (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup :=
      ψ.codRestrict _ hψmem
    have hφsurj : Function.Surjective φ := by
      rintro ⟨v, hv⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp hv
      refine ⟨c, Subtype.ext ?_⟩
      show ψ c = _
      rw [hψ]
      exact Finset.sum_congr rfl fun b _ => (hsmul (c b) (w b)).symm
    have hlin : ∀ v : ι → 𝓞 E, ∑ a, v a • w' a = ψ (A.mulVec v) := by
      intro v
      rw [hψ]
      calc ∑ a, v a • w' a = ∑ a, ∑ b, (((A b a : 𝓞 E) : E) * ((v a : 𝓞 E) : E)) • w b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp only [w', hsmul, Finset.smul_sum, smul_smul, mul_comm]
        _ = ∑ b, ((A.mulVec v b : 𝓞 E) : E) • w b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [Matrix.mulVec, dotProduct]
            push_cast
            rw [Finset.sum_smul]
    have hcomap : ((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup).comap φ =
        (LinearMap.range A.mulVecLin).toAddSubgroup := by
      ext c
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
      show ψ c ∈ Submodule.span (𝓞 E) (Set.range w') ↔ c ∈ LinearMap.range A.mulVecLin
      rw [Submodule.mem_span_range_iff_exists_fun, LinearMap.mem_range]
      constructor
      · rintro ⟨v, hv⟩
        exact ⟨v, hψinj (by rw [Matrix.mulVecLin_apply, ← hlin]; exact hv)⟩
      · rintro ⟨v, rfl⟩
        exact ⟨v, hlin v⟩
    rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφsurj, hcomap]
    exact _root_.GlobalTheory.index_range_mulVecLin_eq_abs_norm_det ι A hA
  have hidxR : (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex
      (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup : ℕ) : ℝ) =
      ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) := by
    exact_mod_cast hidx
  have hN : ((|Algebra.norm ℚ ((A.det : 𝓞 E) : E)| : ℚ) : ℝ) ≠ 0 := by
    have h0 : ((A.det : 𝓞 E) : E) ≠ 0 := by
      exact_mod_cast hA
    have := (Algebra.norm_ne_zero_iff (R := ℚ)).mpr h0
    positivity
  rw [Finset.prod_congr rfl (fun τ _ => hnum τ), Finset.prod_mul_distrib,
    ← _root_.GlobalTheory.abs_norm_eq_prod_cmType_sq r X, hspanE, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2,
    Nat.cast_mul, hidxR, mul_div_mul_left _ _ hN]

end GlobalTheory.ValMul
