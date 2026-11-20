import Mathlib

namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

section Auxiliary

/- English proof (translation)
Break down `eq_or_ne a ∞ with rfl | ha` into its components or cases. Simplify using the standard rewrite rules. Break down `eq_or_ne b ∞ with rfl | hb` into its components or cases. Simplify using the standard rewrite rules. Use `lift a to NNReal using ha`.

Use `lift b to NNReal using hb`. Use `norm_cast`. Rewrite using `[← NNReal.coe_le_coe]`. Use `push_cast`. Use polynomial arithmetic with `[sq_nonneg ((a : ℝ) - b)]`.
-/
theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/- English proof (translation)
Break down `le_total a b with h | h` into its components or cases. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

end Auxiliary

section HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

/- English proof (translation)
Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]`. Conclude with `ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)`.
-/
theorem enorm_inner_le (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)

/- English proof (translation)
Rewrite using `[← ofReal_norm, ← ofReal_norm, norm_inner_symm]`.
-/
theorem enorm_inner_comm (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ = ‖⟪y, x⟫_𝕜‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]

/- English proof (translation)
Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]`. Conclude with `ENNReal.ofReal_le_ofReal (A.le_opNorm x)`.
-/
theorem enorm_apply_le (A : H →L[𝕜] K) (x : H) : ‖A x‖ₑ ≤ ‖A‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (A.le_opNorm x)

/- English proof (translation)
Establish `hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal` using `by norm_num`. Establish `h1` using `lp.norm_rpow_eq_tsum hp (b.repr x)`. Establish `h2` using `(lp.memℓp (b.repr x)).summable hp`. Simplify using `only [LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat, Real.rpow_two] at h1 h2`. Rewrite using `[← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2]`.

Use `congr 1`. Use extensionality with `i`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`.
-/
theorem enorm_sq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp (b.repr x)
  have h2 := (lp.memℓp (b.repr x)).summable hp
  simp only [LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat,
    Real.rpow_two] at h1 h2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2]
  congr 1
  ext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `i`. Conclude with `enorm_sq_eq_tsum c _`. Use `_ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm`.

Use `_ = ∑' j, ∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ₑ ^ 2 := by`. Use `congr 1`. Use extensionality with `j`. Use `congr 1`. Use extensionality with `i`.

Rewrite using `[← adjoint_inner_left, enorm_inner_comm]`. Use `_ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by`. Use `congr 1`. Use extensionality with `j`. Conclude with `(enorm_sq_eq_tsum b _).symm`.
-/
theorem tsum_enorm_sq_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (T : H →L[𝕜] K) :
    ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
  calc ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext i; exact enorm_sq_eq_tsum c _
    _ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext j; congr 1; ext i
        rw [← adjoint_inner_left, enorm_inner_comm]
    _ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
        congr 1; ext j; exact (enorm_sq_eq_tsum b _).symm

variable (𝕜 H) in

def stdHilbertBasis : HilbertBasis (exists_hilbertBasis 𝕜 H).choose 𝕜 H :=
  (exists_hilbertBasis 𝕜 H).choose_spec.choose

def hsNormSq (T : H →L[𝕜] K) : ℝ≥0∞ := ∑' i, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2

/- English proof (translation)
Rewrite using `[hsNormSq, tsum_enorm_sq_eq_adjoint _ (stdHilbertBasis 𝕜 K), tsum_enorm_sq_eq_adjoint b (stdHilbertBasis 𝕜 K)]`.
-/
theorem hsNormSq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    hsNormSq T = ∑' i, ‖T (b i)‖ₑ ^ 2 := by
  rw [hsNormSq, tsum_enorm_sq_eq_adjoint _ (stdHilbertBasis 𝕜 K),
    tsum_enorm_sq_eq_adjoint b (stdHilbertBasis 𝕜 K)]

/- English proof (translation)
Rewrite using `[hsNormSq_eq_tsum (stdHilbertBasis 𝕜 K) (T†), hsNormSq, tsum_enorm_sq_eq_adjoint (stdHilbertBasis 𝕜 H) (stdHilbertBasis 𝕜 K)]`.
-/
theorem hsNormSq_adjoint (T : H →L[𝕜] K) : hsNormSq (T†) = hsNormSq T := by
  rw [hsNormSq_eq_tsum (stdHilbertBasis 𝕜 K) (T†), hsNormSq,
    tsum_enorm_sq_eq_adjoint (stdHilbertBasis 𝕜 H) (stdHilbertBasis 𝕜 K)]

def IsHilbertSchmidt (T : H →L[𝕜] K) : Prop := hsNormSq T < ∞

/- English proof (translation)
Rewrite using `[IsHilbertSchmidt, hsNormSq_eq_tsum b]`.
-/
theorem isHilbertSchmidt_iff {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    IsHilbertSchmidt T ↔ ∑' i, ‖T (b i)‖ₑ ^ 2 < ∞ := by
  rw [IsHilbertSchmidt, hsNormSq_eq_tsum b]

/- English proof (translation)
Rewrite using `[IsHilbertSchmidt, IsHilbertSchmidt, hsNormSq_adjoint]`.
-/
theorem isHilbertSchmidt_adjoint_iff (T : H →L[𝕜] K) :
    IsHilbertSchmidt (T†) ↔ IsHilbertSchmidt T := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hsNormSq_adjoint]

/- English proof (translation)
The claim follows from `(isHilbertSchmidt_adjoint_iff T).2 hT`.
-/
theorem IsHilbertSchmidt.adjoint {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) :=
  (isHilbertSchmidt_adjoint_iff T).2 hT

def hsNorm (T : H →L[𝕜] K) : ℝ := √(hsNormSq T).toReal

/- English proof (translation)
The claim follows from `Real.sqrt_nonneg _`.
-/
theorem hsNorm_nonneg (T : H →L[𝕜] K) : 0 ≤ hsNorm T := Real.sqrt_nonneg _

/- English proof (translation)
The claim follows from `Real.sq_sqrt ENNReal.toReal_nonneg`.
-/
theorem hsNorm_sq (T : H →L[𝕜] K) : hsNorm T ^ 2 = (hsNormSq T).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

/- English proof (translation)
Rewrite using `[hsNorm, hsNorm, hsNormSq_adjoint]`.
-/
theorem hsNorm_adjoint (T : H →L[𝕜] K) : hsNorm (T†) = hsNorm T := by
  rw [hsNorm, hsNorm, hsNormSq_adjoint]

/- English proof (translation)
Set `c` to `stdHilbertBasis 𝕜 K`. Rewrite using `[← hsNormSq_adjoint, hsNormSq_eq_tsum c, enorm_sq_eq_tsum c, ← ENNReal.tsum_mul_right]`. Use `ENNReal.tsum_le_tsum fun j => ?_` and prove the remaining obligations. Rewrite using `[← adjoint_inner_left, ← mul_pow]`. Use `gcongr`.

Conclude with `enorm_inner_le _ _`.
-/
theorem enorm_apply_sq_le (T : H →L[𝕜] K) (x : H) :
    ‖T x‖ₑ ^ 2 ≤ hsNormSq T * ‖x‖ₑ ^ 2 := by
  let c := stdHilbertBasis 𝕜 K
  rw [← hsNormSq_adjoint, hsNormSq_eq_tsum c, enorm_sq_eq_tsum c, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← adjoint_inner_left, ← mul_pow]
  gcongr
  exact enorm_inner_le _ _

/- English proof (translation)
Use `T.opNorm_le_bound (hsNorm_nonneg T) fun x => ?_` and prove the remaining obligations. Establish `h` using `enorm_apply_sq_le T x`. Rewrite `h` using `[← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hT.ne, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_le_ofReal_iff (by positivity)]`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (T x)), hsNorm, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul ENNReal.toReal_nonneg]`. Conclude with `Real.sqrt_le_sqrt h`.
-/
theorem norm_le_hsNorm {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T := by
  refine T.opNorm_le_bound (hsNorm_nonneg T) fun x => ?_
  have h := enorm_apply_sq_le T x
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hT.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg (T x)), hsNorm, ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h

/- English proof (translation)
Simplify using `[hsNormSq]`.
-/
theorem hsNormSq_zero : hsNormSq (0 : H →L[𝕜] K) = 0 := by
  simp [hsNormSq]

/- English proof (translation)
Simplify using `only [hsNormSq, smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]`.
-/
theorem hsNormSq_smul (c : 𝕜) (T : H →L[𝕜] K) : hsNormSq (c • T) = ‖c‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]

/- English proof (translation)
Simplify using `only [hsNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]`. Use `ENNReal.tsum_le_tsum fun i => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsNormSq_add_le (S T : H →L[𝕜] K) :
    hsNormSq (S + T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  calc ‖(S + T) _‖ₑ ^ 2 ≤ (‖S _‖ₑ + ‖T _‖ₑ) ^ 2 := by
        gcongr; exact enorm_add_le _ _
    _ ≤ _ := ennreal_add_sq_le _ _

/- English proof (translation)
Simplify using `only [hsNormSq, ← ENNReal.tsum_mul_left, comp_apply]`. Use `ENNReal.tsum_le_tsum fun i => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Use `gcongr`. Conclude with `enorm_apply_le _ _`.
-/
theorem hsNormSq_comp_left_le (A : K →L[𝕜] L) (T : H →L[𝕜] K) :
    hsNormSq (A.comp T) ≤ ‖A‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, comp_apply]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← mul_pow]
  gcongr
  exact enorm_apply_le _ _

/- English proof (translation)
Rewrite using `[← hsNormSq_adjoint, adjoint_comp, ← hsNormSq_adjoint T]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ofReal_norm, ← ofReal_norm, adjoint.norm_map]`.
-/
theorem hsNormSq_comp_right_le (T : K →L[𝕜] L) (B : H →L[𝕜] K) :
    hsNormSq (T.comp B) ≤ ‖B‖ₑ ^ 2 * hsNormSq T := by
  rw [← hsNormSq_adjoint, adjoint_comp, ← hsNormSq_adjoint T]
  calc hsNormSq ((B†).comp (T†)) ≤ ‖B†‖ₑ ^ 2 * hsNormSq (T†) := hsNormSq_comp_left_le _ _
    _ = ‖B‖ₑ ^ 2 * hsNormSq (T†) := by
        rw [← ofReal_norm, ← ofReal_norm, adjoint.norm_map]

/- English proof (translation)
The claim follows from `(hsNormSq_comp_left_le A T).trans_lt (ENNReal.mul_lt_top (by simp) hT)`.
-/
theorem IsHilbertSchmidt.comp_left {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (A : K →L[𝕜] L) :
    IsHilbertSchmidt (A.comp T) :=
  (hsNormSq_comp_left_le A T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

/- English proof (translation)
The claim follows from `(hsNormSq_comp_right_le T B).trans_lt (ENNReal.mul_lt_top (by simp) hT)`.
-/
theorem IsHilbertSchmidt.comp_right {T : K →L[𝕜] L} (hT : IsHilbertSchmidt T) (B : H →L[𝕜] K) :
    IsHilbertSchmidt (T.comp B) :=
  (hsNormSq_comp_right_le T B).trans_lt (ENNReal.mul_lt_top (by simp) hT)

variable (𝕜 H K) in

def hilbertSchmidt : Submodule 𝕜 (H →L[𝕜] K) where
  carrier := {T | IsHilbertSchmidt T}
  add_mem' {S T} hS hT := by
    refine (hsNormSq_add_le S T).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hS, ENNReal.mul_lt_top (by simp) hT⟩
  zero_mem' := by
    show hsNormSq (0 : H →L[𝕜] K) < ∞
    simp [hsNormSq_zero]
  smul_mem' c T hT := by
    show hsNormSq (c • T) < ∞
    rw [hsNormSq_smul]
    exact ENNReal.mul_lt_top (by simp) hT

/- English proof (translation)
The claim follows from `(hilbertSchmidt 𝕜 H K).add_mem hS hT`.
-/
theorem IsHilbertSchmidt.add {S T : H →L[𝕜] K} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) :=
  (hilbertSchmidt 𝕜 H K).add_mem hS hT

/- English proof (translation)
The claim follows from `(hilbertSchmidt 𝕜 H K).smul_mem c hT`.
-/
theorem IsHilbertSchmidt.smul {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) :=
  (hilbertSchmidt 𝕜 H K).smul_mem c hT

/- English proof (translation)
Establish `hfin : ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞` using `by rw [← hsNormSq_eq_tsum b]; exact hT.ne`. Establish `hs` using `ENNReal.summable_toReal hfin`. Rewrite using `[hsNorm_sq, hsNormSq_eq_tsum b, ENNReal.tsum_toReal_eq fun i => by simp]`. Use `hs.hasSum using 2 with i` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules.
-/
theorem IsHilbertSchmidt.hasSum_norm_sq {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 H) : HasSum (fun i => ‖T (b i)‖ ^ 2) (hsNorm T ^ 2) := by
  have hfin : ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by rw [← hsNormSq_eq_tsum b]; exact hT.ne
  have hs := ENNReal.summable_toReal hfin
  rw [hsNorm_sq, hsNormSq_eq_tsum b, ENNReal.tsum_toReal_eq fun i => by simp]
  convert hs.hasSum using 2 with i; simp

/- English proof (translation)
Set `F : ι → κ → 𝕜` to `fun i j => ⟪(B†) (f j), e i⟫_𝕜 * ⟪e i, A (f j)⟫_𝕜`. Establish `hfin : ∑' p : ι × κ, ‖Function.uncurry F p‖ₑ ≠ ∞`. Use `ne_top_of_le_ne_top (b := ∑' p : ι × κ, (‖⟪e p.1, (B†) (f p.2)⟫_𝕜‖ₑ ^ 2 + ‖⟪e p.1, A (f p.2)⟫_𝕜‖ₑ ^ 2)) ?_ ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm, ENNReal.tsum_comm (f := fun i j => ‖⟪e i, A (f j)⟫_𝕜‖ₑ ^ 2)]`. Simplify using `only [← enorm_sq_eq_tsum e, ← hsNormSq_eq_tsum f]`.

Conclude with `ENNReal.add_ne_top.2 ⟨(hB.adjoint).ne, hA.ne⟩`. Use `ENNReal.tsum_le_tsum fun p => ?_` and prove the remaining obligations. Simplify using `only [Function.uncurry, F, enorm_mul]`. Rewrite using `[enorm_inner_comm ((B†) (f p.2))]`. Conclude with `ennreal_mul_le_sq_add_sq _ _`.

Establish `hF : Summable (Function.uncurry F)`. Use `Summable.of_norm ?_` and prove the remaining obligations. Use `ENNReal.summable_toReal hfin using 2 with p` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Establish `h1 : ∀ i, ∑' j, F i j = ⟪e i, A (B (e i))⟫_𝕜`.

Introduce `i`. Rewrite using `[← adjoint_inner_left A]`. Use `((f.hasSum_inner_mul_inner ((A†) (e i)) (B (e i))).congr_fun fun j => ?_).tsum_eq` and prove the remaining obligations. Simplify using `only [F]`. Rewrite using `[adjoint_inner_left, adjoint_inner_left, mul_comm]`.

Establish `h2 : ∀ j, ∑' i, F i j = ⟪f j, B (A (f j))⟫_𝕜`. Introduce `j`. Rewrite using `[← adjoint_inner_left B]`. Conclude with `(e.hasSum_inner_mul_inner ((B†) (f j)) (A (f j))).tsum_eq`. Establish `hsum` using `hF.prod`.

Simplify using `only [Function.uncurry_apply_pair] at hsum`. Establish `hval : ∑' j, ⟪f j, B (A (f j))⟫_𝕜 = ∑' i, ∑' j, F i j`. Repeatedly rewrite using `[← h2]`. Conclude with `hF.tsum_comm`. Rewrite using `[hval, show (fun i => ⟪e i, A (B (e i))⟫_𝕜) = fun i => ∑' j, F i j from`.

Use function extensionality and compare the values at `fun i => (h1 i).symm]`. Conclude with `hsum.hasSum`.
-/
theorem hasSum_inner_comp_comm {ι κ : Type*} (e : HilbertBasis ι 𝕜 H) (f : HilbertBasis κ 𝕜 K)
    {A : K →L[𝕜] H} {B : H →L[𝕜] K} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    HasSum (fun i => ⟪e i, A (B (e i))⟫_𝕜) (∑' j, ⟪f j, B (A (f j))⟫_𝕜) := by
  let F : ι → κ → 𝕜 := fun i j => ⟪(B†) (f j), e i⟫_𝕜 * ⟪e i, A (f j)⟫_𝕜

  have hfin : ∑' p : ι × κ, ‖Function.uncurry F p‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' p : ι × κ,
      (‖⟪e p.1, (B†) (f p.2)⟫_𝕜‖ₑ ^ 2 + ‖⟪e p.1, A (f p.2)⟫_𝕜‖ₑ ^ 2)) ?_ ?_
    · rw [ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm,
        ENNReal.tsum_comm (f := fun i j => ‖⟪e i, A (f j)⟫_𝕜‖ₑ ^ 2)]
      simp only [← enorm_sq_eq_tsum e, ← hsNormSq_eq_tsum f]
      exact ENNReal.add_ne_top.2 ⟨(hB.adjoint).ne, hA.ne⟩
    · refine ENNReal.tsum_le_tsum fun p => ?_
      simp only [Function.uncurry, F, enorm_mul]
      rw [enorm_inner_comm ((B†) (f p.2))]
      exact ennreal_mul_le_sq_add_sq _ _
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm ?_
    convert ENNReal.summable_toReal hfin using 2 with p
    simp
  have h1 : ∀ i, ∑' j, F i j = ⟪e i, A (B (e i))⟫_𝕜 := by
    intro i
    rw [← adjoint_inner_left A]
    refine ((f.hasSum_inner_mul_inner ((A†) (e i)) (B (e i))).congr_fun fun j => ?_).tsum_eq
    simp only [F]
    rw [adjoint_inner_left, adjoint_inner_left, mul_comm]
  have h2 : ∀ j, ∑' i, F i j = ⟪f j, B (A (f j))⟫_𝕜 := by
    intro j
    rw [← adjoint_inner_left B]
    exact (e.hasSum_inner_mul_inner ((B†) (f j)) (A (f j))).tsum_eq
  have hsum := hF.prod
  simp only [Function.uncurry_apply_pair] at hsum
  have hval : ∑' j, ⟪f j, B (A (f j))⟫_𝕜 = ∑' i, ∑' j, F i j := by
    simp_rw [← h2]
    exact hF.tsum_comm
  rw [hval, show (fun i => ⟪e i, A (B (e i))⟫_𝕜) = fun i => ∑' j, F i j from
    funext fun i => (h1 i).symm]
  exact hsum.hasSum

end HilbertSchmidt

end

end GroundTheory.Automorphic
