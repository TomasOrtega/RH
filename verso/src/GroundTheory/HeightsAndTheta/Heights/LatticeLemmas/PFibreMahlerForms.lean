import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsFibreMahler
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PDiagonalChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField TensorProduct ComplexAt

noncomputable section

namespace FibreMahlerForms

section Dual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr' ξ]`. Simplify using `only [map_sum, map_smul, smul_eq_mul]`.
-/
theorem apply_eq_sum (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (ξ : V) :
    ℓ ξ = ∑ j, inner ℂ (b j) ξ * ℓ (b j) := by
  conv_lhs => rw [← b.sum_repr' ξ]
  simp only [map_sum, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[← b.sum_repr_symm]`. Simplify using `only [map_sum, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem apply_repr_symm (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ℓ (b.repr.symm (WithLp.toLp 2 v)) = ∑ j, ℓ (b j) * v j := by
  rw [← b.sum_repr_symm]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use `set v : V := ∑ j, star (ℓ (b j)) • b j`. Establish `hv : ∀ ξ, ℓ ξ = inner ℂ v ξ`. Introduce `ξ`. Rewrite using `[apply_eq_sum b ℓ ξ]`. Simplify using `only [v, sum_inner, inner_smul_left, Complex.star_def, Complex.conj_conj]`.

Conclude with `Finset.sum_congr rfl fun j _ ↦ mul_comm _ _`. Establish `hvv : ‖v‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2)`. Establish `h2 : ‖v‖ ^ 2 = ∑ j, ‖ℓ (b j)‖ ^ 2`. Rewrite using `[@norm_sq_eq_re_inner ℂ, ← hv]`. Simplify using `only [v, map_sum, map_smul, smul_eq_mul, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re]`.

Rewrite using `[← h2, Real.sqrt_sq (norm_nonneg _)]`. Rewrite using `[← hvv]`. Establish `hle : ∀ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ ≤ ‖v‖` using `fun ξ ↦ by`. Rewrite using `[hv]`. Combine the equalities or inequalities in the displayed calculation.

Establish `: Nonempty {ξ : V // ‖ξ‖ ≤ 1}` using `⟨⟨0, by simp⟩⟩`. Use `le_antisymm (ciSup_le hle) ?_` and prove the remaining obligations. Establish `hbdd : BddAbove (Set.range fun ξ : {ξ : V // ‖ξ‖ ≤ 1} ↦ ‖ℓ ξ‖)` using `⟨‖v‖, by`. Introduce and unpack `_ ⟨ξ, rfl⟩`. Conclude with `hle ξ⟩`.

Distinguish the cases in `h0 : v = 0`. Rewrite using `[h0, norm_zero]`. Conclude with `le_trans (norm_nonneg _) (le_ciSup hbdd ⟨0, by simp⟩)`. Establish `hn : (‖v‖ : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.mpr h0`. Use `le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨(‖v‖ : ℂ)⁻¹ • v, ?_⟩)` and prove the remaining obligations.

Establish `hn' : ‖v‖ ≠ 0` using `norm_ne_zero_iff.mpr h0`. Rewrite using `[hv, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_mul, norm_inv, norm_pow]`. Simplify using `only [Complex.norm_real, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]`.
-/
theorem iSup_norm_ball (b : OrthonormalBasis ι ℂ V) (ℓ : V →ₗ[ℂ] ℂ) :
    ⨆ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2) := by
  set v : V := ∑ j, star (ℓ (b j)) • b j
  have hv : ∀ ξ, ℓ ξ = inner ℂ v ξ := by
    intro ξ
    rw [apply_eq_sum b ℓ ξ]
    simp only [v, sum_inner, inner_smul_left, Complex.star_def, Complex.conj_conj]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hvv : ‖v‖ = √(∑ j, ‖ℓ (b j)‖ ^ 2) := by
    have h2 : ‖v‖ ^ 2 = ∑ j, ‖ℓ (b j)‖ ^ 2 := by
      rw [@norm_sq_eq_re_inner ℂ, ← hv]
      simp only [v, map_sum, map_smul, smul_eq_mul, Complex.star_def, Complex.conj_mul',
        ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re]
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [← hvv]
  have hle : ∀ ξ : {ξ : V // ‖ξ‖ ≤ 1}, ‖ℓ ξ‖ ≤ ‖v‖ := fun ξ ↦ by
    rw [hv]
    calc ‖inner ℂ v (ξ : V)‖ ≤ ‖v‖ * ‖(ξ : V)‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * 1 := by gcongr; exact ξ.2
      _ = ‖v‖ := mul_one _
  have : Nonempty {ξ : V // ‖ξ‖ ≤ 1} := ⟨⟨0, by simp⟩⟩
  refine le_antisymm (ciSup_le hle) ?_
  have hbdd : BddAbove (Set.range fun ξ : {ξ : V // ‖ξ‖ ≤ 1} ↦ ‖ℓ ξ‖) := ⟨‖v‖, by
    rintro _ ⟨ξ, rfl⟩; exact hle ξ⟩
  by_cases h0 : v = 0
  · rw [h0, norm_zero]
    exact le_trans (norm_nonneg _) (le_ciSup hbdd ⟨0, by simp⟩)
  · have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
    refine le_trans (le_of_eq ?_) (le_ciSup hbdd ⟨(‖v‖ : ℂ)⁻¹ • v, ?_⟩)
    · have hn' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      rw [hv, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), norm_mul, norm_inv, norm_pow]
      simp only [Complex.norm_real, RCLike.norm_ofReal, Real.norm_eq_abs, abs_norm]
      field_simp
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]

end Dual

section Mahler

variable {d : ℕ}

/- English proof (translation)
Take `⟨j0, hj0⟩` from `hc`. Use `set S := ∑ j, ‖c j‖ ^ 2 with hS`. Establish `hSpos : 0 < S` using `lt_of_lt_of_le (by positivity : 0 < ‖c j0‖ ^ 2) (Finset.single_le_sum (f := fun j ↦ ‖c j‖ ^ 2) (fun j _ ↦ by positivity) (Finset.mem_univ j0))`. Use `set ν := √S with hνdef`. Establish `hν : 0 < ν` using `Real.sqrt_pos.mpr hSpos`.

Establish `hν2 : ν ^ 2 = S` using `Real.sq_sqrt hSpos.le`. Establish `hνC : (ν : ℂ) ≠ 0` using `by exact_mod_cast hν.ne'`. Use `set p : Fin d → ℂ := fun j ↦ star (c j) / (ν : ℂ) with hpdef`. Establish `hsplit : (∑ j, C (c j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) = C (ν : ℂ) * ∑ j, C (star (p j)) * X ((0 : Fin 1), j)`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← C_mul]`. Use `congr 2`. Simplify using `only [p, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]`. Clear the denominators using the available nonvanishing facts.

Establish `hp : ∑ j, ‖p j‖ ^ 2 = 1`. Simplify using `only [p, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν, div_pow, ← Finset.sum_div, hν2]`. Conclude with `div_self hSpos.ne'`. Establish `hL : (∑ j, C (star (p j)) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (eval fun ij : Fin 1 × Fin d ↦ p ij.2) h0`. Simplify using `only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.conj_mul'] at h1`. Establish `h2 : ((∑ j, ‖p j‖ ^ 2 : ℝ) : ℂ) = 0` using `by push_cast; exact h1`. Rewrite `h2` using `[hp]`. Evaluate the numerical expressions using `at h2`.

Rewrite using `[hsplit, mahlerMul d 1 _ _ _ (C_ne_zero.mpr hνC) hL, mahler_C, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]`. Establish `hlin` using `sphereMeanLinear d p hp`. Establish `hfun : (fun u : Fin 1 × Fin d → ℂ ↦ Real.log ‖eval u (∑ j, C (star (p j)) * X ((0 : Fin 1), j))‖) = fun z ↦ Real.log ‖∑ j, z (0, j) * star (p j)‖`. Use function extensionality and compare the values at `u`. Simplify using `only [map_sum, map_mul, eval_C, eval_X, mul_comm]`.

Unfold `mahler`. Rewrite using `[hfun, hlin]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mahler_linear (c : Fin d → ℂ) (hc : ∃ j, c j ≠ 0) :
    mahler (HermNorm.std d) 1 (∑ j, C (c j) * X ((0 : Fin 1), j)) =
      Real.log √(∑ j, ‖c j‖ ^ 2) - (harmonic (d - 1) : ℝ) / 2 := by
  obtain ⟨j0, hj0⟩ := hc
  set S := ∑ j, ‖c j‖ ^ 2 with hS
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity : 0 < ‖c j0‖ ^ 2)
    (Finset.single_le_sum (f := fun j ↦ ‖c j‖ ^ 2) (fun j _ ↦ by positivity) (Finset.mem_univ j0))
  set ν := √S with hνdef
  have hν : 0 < ν := Real.sqrt_pos.mpr hSpos
  have hν2 : ν ^ 2 = S := Real.sq_sqrt hSpos.le
  have hνC : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  set p : Fin d → ℂ := fun j ↦ star (c j) / (ν : ℂ) with hpdef
  have hsplit : (∑ j, C (c j) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) =
      C (ν : ℂ) * ∑ j, C (star (p j)) * X ((0 : Fin 1), j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← mul_assoc, ← C_mul]
    congr 2
    simp only [p, star_div₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    field_simp
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    simp only [p, norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν, div_pow,
      ← Finset.sum_div, hν2]
    exact div_self hSpos.ne'
  have hL : (∑ j, C (star (p j)) * X ((0 : Fin 1), j) : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0 := by
    intro h0
    have h1 := congrArg (eval fun ij : Fin 1 × Fin d ↦ p ij.2) h0
    simp only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.conj_mul'] at h1
    have h2 : ((∑ j, ‖p j‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h1
    rw [hp] at h2
    norm_num at h2
  rw [hsplit, mahlerMul d 1 _ _ _ (C_ne_zero.mpr hνC) hL, mahler_C, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hν]
  have hlin := sphereMeanLinear d p hp
  have hfun : (fun u : Fin 1 × Fin d → ℂ ↦
      Real.log ‖eval u (∑ j, C (star (p j)) * X ((0 : Fin 1), j))‖) =
      fun z ↦ Real.log ‖∑ j, z (0, j) * star (p j)‖ := by
    funext u
    simp only [map_sum, map_mul, eval_C, eval_X, mul_comm]
  unfold mahler
  rw [hfun, hlin]
  ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp only [Finset.prod_empty, mul_one, mahler_C, Finset.sum_empty, add_zero]`. Consider the case `insert q s hq ih`. Establish `hne : (C a * ∏ q ∈ s, L q : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0` using `mul_ne_zero (C_ne_zero.mpr ha) (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q)`. Rewrite using `[Finset.prod_insert hq, mul_left_comm, mahlerMul d 1 _ _ _ (hL q) hne, ih, Finset.sum_insert hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mahler_C_mul_prod {ι : Type*} (s : Finset ι) (L : ι → MvPolynomial (Fin 1 × Fin d) ℂ)
    (hL : ∀ q, L q ≠ 0) (a : ℂ) (ha : a ≠ 0) :
    mahler (HermNorm.std d) 1 (C a * ∏ q ∈ s, L q) =
      Real.log ‖a‖ + ∑ q ∈ s, mahler (HermNorm.std d) 1 (L q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one, mahler_C, Finset.sum_empty, add_zero]
  | insert q s hq ih =>
    have hne : (C a * ∏ q ∈ s, L q : MvPolynomial (Fin 1 × Fin d) ℂ) ≠ 0 :=
      mul_ne_zero (C_ne_zero.mpr ha) (Finset.prod_ne_zero_iff.mpr fun q _ ↦ hL q)
    rw [Finset.prod_insert hq, mul_left_comm, mahlerMul d 1 _ _ _ (hL q) hne, ih,
      Finset.sum_insert hq]
    ring

end Mahler

section Fibre

variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_linearIndependent_fin (K := F) (E := W)`. Set `b` to `Module.Basis.mk (linearIndependent_fibreVec h σ hs) (LatticeLemmas.span_fibreVec_eq_top h σ hs (Fintype.card_fin _)).ge`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`.
-/
theorem finrank_fibreSpace (h : HermitianMetric F W) (σ : F →+* ℂ) :
    Module.finrank ℂ (FibreSpace h σ) = Module.finrank (𝓞 F) W := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := F) (E := W)
  let b := Module.Basis.mk (linearIndependent_fibreVec h σ hs)
    (LatticeLemmas.span_fibreVec_eq_top h σ hs (Fintype.card_fin _)).ge
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

/- English proof (translation)
Use `set T := Submodule.span ℂ (Set.range fun k ↦ fibreVec h σ (w k))`. Establish `hvec : ∀ e : W, fibreVec h σ e ∈ T`. Introduce `e`. Establish `he : e ∈ Submodule.span (𝓞 F) (Set.range w)` using `hw ▸ Submodule.mem_top`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp he`.

Rewrite using `[fibreVec_sum]`. Conclude with `Submodule.sum_mem _ fun k _ ↦ T.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)`. Introduce `ξ`. Establish `hξ : ξ ∈ T`. Take `⟨y, rfl⟩` from `(FibreSpace.equiv h σ).surjective ξ`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `T.zero_mem`. Consider the case `tmul z e`. Establish `: FibreSpace.equiv h σ (z ⊗ₜ e) = ((ofComplex σ).symm z) • fibreVec h σ e`.

Rewrite using `[fibreVec, ← map_smul, smul_tmul', complex_smul_def, mul_one, AlgEquiv.apply_symm_apply]`. Rewrite using `[this]`. Conclude with `T.smul_mem _ (hvec e)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `T.add_mem hx hy`.

Take `⟨x, hx⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp hξ`. Conclude with `⟨x, hx⟩`.
-/
theorem fibreGen_surjective (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (hw : Submodule.span (𝓞 F) (Set.range w) = ⊤) : Function.Surjective (fibreGen h σ w) := by
  set T := Submodule.span ℂ (Set.range fun k ↦ fibreVec h σ (w k))
  have hvec : ∀ e : W, fibreVec h σ e ∈ T := by
    intro e
    have he : e ∈ Submodule.span (𝓞 F) (Set.range w) := hw ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp he
    rw [fibreVec_sum]
    exact Submodule.sum_mem _ fun k _ ↦ T.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  intro ξ
  have hξ : ξ ∈ T := by
    obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective ξ
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact T.zero_mem
    | tmul z e =>
      have : FibreSpace.equiv h σ (z ⊗ₜ e) = ((ofComplex σ).symm z) • fibreVec h σ e := by
        rw [fibreVec, ← map_smul, smul_tmul', complex_smul_def, mul_one, AlgEquiv.apply_symm_apply]
      rw [this]
      exact T.smul_mem _ (hvec e)
    | add x y hx hy => rw [map_add]; exact T.add_mem hx hy
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hξ
  exact ⟨x, hx⟩

variable {K : Type} [Field K] [NumberField K] [Algebra F K]

def archLin (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) :
    FibreSpace h (τ.comp (algebraMap F K)) →ₗ[ℂ] ℂ where
  toFun ξ := (ofComplex _).symm (archFunctional τ yv ((FibreSpace.equiv h _).symm ξ))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    rw [map_smul]
    generalize (FibreSpace.equiv h _).symm x = y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, RingHom.id_apply]
    | tmul z e =>
      simp only [smul_tmul', archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply,
        complex_smul_def, map_mul, AlgEquiv.symm_apply_apply, RingHom.id_apply, smul_eq_mul,
        mul_assoc]
    | add x y hx hy =>
      simp only [smul_add, map_add, hx, hy, RingHom.id_apply, smul_eq_mul, mul_add]

/- English proof (translation)
Simplify using `only [archLin, LinearMap.coe_mk, AddHom.coe_mk, fibreVec, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul, AlgEquiv.symm_apply_apply]`.
-/
theorem archLin_fibreVec (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (e : W) :
    archLin h τ yv (fibreVec h (τ.comp (algebraMap F K)) e) = τ (yv e) := by
  simp only [archLin, LinearMap.coe_mk, AddHom.coe_mk, fibreVec, LinearEquiv.symm_apply_apply,
    archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul,
    AlgEquiv.symm_apply_apply]

/- English proof (translation)
Simplify using `only [fibreGen, map_sum, map_smul, archLin_fibreVec, smul_eq_mul, mul_comm]`.
-/
theorem archLin_fibreGen (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {n : ℕ}
    (w : Fin n → W) (x : Fin n → ℂ) :
    archLin h τ yv (fibreGen h (τ.comp (algebraMap F K)) w x) = ∑ k, τ (yv (w k)) * x k := by
  simp only [fibreGen, map_sum, map_smul, archLin_fibreVec, smul_eq_mul, mul_comm]

/- English proof (translation)
The claim follows from `iSup_norm_ball b (archLin h τ yv)`.
-/
theorem archDualNorm_eq (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) {ι : Type*}
    [Fintype ι] (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    archDualNorm h τ yv = √(∑ j, ‖archLin h τ yv (b j)‖ ^ 2) :=
  iSup_norm_ball b (archLin h τ yv)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e, yv e ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hy (LinearMap.ext hc)`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `h1` using `apply_eq_sum b (archLin h τ yv) (fibreVec h _ e)`. Rewrite `h1` using `[archLin_fibreVec]`. Simplify using `only [hc, mul_zero, Finset.sum_const_zero] at h1`. Conclude with `(map_ne_zero τ).mpr he h1`.
-/
theorem exists_archLin_ne_zero (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K)
    (hy : yv ≠ 0) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (FibreSpace h (τ.comp (algebraMap F K)))) :
    ∃ j, archLin h τ yv (b j) ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e, yv e ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hy (LinearMap.ext hc)
  by_contra hc
  push Not at hc
  have h1 := apply_eq_sum b (archLin h τ yv) (fibreVec h _ e)
  rw [archLin_fibreVec] at h1
  simp only [hc, mul_zero, Finset.sum_const_zero] at h1
  exact (map_ne_zero τ).mpr he h1

end Fibre

end FibreMahlerForms

open FibreMahlerForms in

/- English proof (translation)
Introduce `F _ _ W _ _ _ _ h n w hw K _ _ _ τ m yv hyv a ha`. Use `set σ := τ.comp (algebraMap F K) with hσ`. Set `b` to `stdOrthonormalBasis ℂ (FibreSpace h σ)`. Establish `hsurj` using `fibreGen_surjective h σ w hw`. Establish `hG : fibreMahler h σ w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) = mahler (HermNorm.std (Module.finrank ℂ (FibreSpace h σ))) 1 (C a * ∏ q, ∑ j, C (archLin h τ (yv q) (b j)) * X ((0 : Fin 1), j))`.

Unfold `fibreMahler fibreSphereMean mahler`. Use `congr 1`. Use function extensionality and compare the values at `u`. Use `set ξ := b.repr.symm (WithLp.toLp 2 fun j ↦ u (0, j))`. Establish `hx : fibreGen h σ w (Function.invFun (fibreGen h σ w) ξ) = ξ` using `Function.invFun_eq (hsurj ξ)`.

Simplify using `only [fibrePoly, map_mul, eval_C, map_prod, map_sum, eval_X]`. Use `congrArg (fun z ↦ Real.log ‖a * z‖) (Finset.prod_congr rfl fun q _ ↦ ?_)` and prove the remaining obligations. Establish `h1` using `archLin_fibreGen h τ (yv q) w (Function.invFun (fibreGen h σ w) ξ)`. Rewrite `h1` using `[hx]`. Rewrite using `[← h1, apply_repr_symm]`.

Rewrite using `[hG, mahler_C_mul_prod]`. Use `congr 1`. Use `Finset.sum_congr rfl fun q _ ↦ ?_` and prove the remaining obligations. Establish `hd : (harmonic (Module.finrank ℂ (FibreSpace h σ) - 1) : ℝ) = harmonic (Module.finrank (𝓞 F) W - 1)` using `by rw [finrank_fibreSpace]`. Rewrite using `[mahler_linear _ (exists_archLin_ne_zero h τ (yv q) (hyv q) b), archDualNorm_eq h τ (yv q) b, hd]`.

Introduce `q hq`. Take `⟨j, hj⟩` from `exists_archLin_ne_zero h τ (yv q) (hyv q) b`. Establish `h1` using `congrArg (eval fun ij : Fin 1 × Fin (Module.finrank ℂ (FibreSpace h σ)) ↦ star (archLin h τ (yv q) (b ij.2))) hq`. Simplify using `only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.mul_conj'] at h1`. Establish `h2 : ((∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 : ℝ) : ℂ) = 0` using `by push_cast; exact h1`.

Establish `h3 : ∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 = 0` using `by exact_mod_cast h2`. Rewrite `h3` using `[Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)]`. Conclude with `hj (by simpa using h3 j (Finset.mem_univ _))`. Conclude with `ha`.
-/
theorem FibreMahlerForms.proof : FibreMahlerForms.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ τ m yv hyv a ha
  set σ := τ.comp (algebraMap F K) with hσ
  let b := stdOrthonormalBasis ℂ (FibreSpace h σ)
  have hsurj := fibreGen_surjective h σ w hw
  have hG : fibreMahler h σ w (C a * ∏ q, ∑ k, C (τ (yv q (w k))) * X k) =
      mahler (HermNorm.std (Module.finrank ℂ (FibreSpace h σ))) 1
        (C a * ∏ q, ∑ j, C (archLin h τ (yv q) (b j)) * X ((0 : Fin 1), j)) := by
    unfold fibreMahler fibreSphereMean mahler
    congr 1
    funext u
    set ξ := b.repr.symm (WithLp.toLp 2 fun j ↦ u (0, j))
    have hx : fibreGen h σ w (Function.invFun (fibreGen h σ w) ξ) = ξ :=
      Function.invFun_eq (hsurj ξ)
    simp only [fibrePoly, map_mul, eval_C, map_prod, map_sum, eval_X]
    refine congrArg (fun z ↦ Real.log ‖a * z‖) (Finset.prod_congr rfl fun q _ ↦ ?_)
    have h1 := archLin_fibreGen h τ (yv q) w (Function.invFun (fibreGen h σ w) ξ)
    rw [hx] at h1
    rw [← h1, apply_repr_symm]
  rw [hG, mahler_C_mul_prod]
  · congr 1
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    have hd : (harmonic (Module.finrank ℂ (FibreSpace h σ) - 1) : ℝ) =
        harmonic (Module.finrank (𝓞 F) W - 1) := by rw [finrank_fibreSpace]
    rw [mahler_linear _ (exists_archLin_ne_zero h τ (yv q) (hyv q) b), archDualNorm_eq h τ (yv q) b, hd]
  · intro q hq
    obtain ⟨j, hj⟩ := exists_archLin_ne_zero h τ (yv q) (hyv q) b
    have h1 := congrArg (eval fun ij : Fin 1 × Fin (Module.finrank ℂ (FibreSpace h σ)) ↦
      star (archLin h τ (yv q) (b ij.2))) hq
    simp only [map_sum, map_mul, eval_C, eval_X, map_zero, Complex.star_def, Complex.mul_conj'] at h1
    have h2 : ((∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h1
    have h3 : ∑ j, ‖archLin h τ (yv q) (b j)‖ ^ 2 = 0 := by exact_mod_cast h2
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)] at h3
    exact hj (by simpa using h3 j (Finset.mem_univ _))
  · exact ha

end

end GroundTheory.Heights₂.Heights
