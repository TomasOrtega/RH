import ReciprocityTheory.SemistableReduction.SemiDegW

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

/- English proof (translation)
Introduce and unpack `⟨z, hz⟩`. Establish `hint : IsIntegral ℤ ((2 : K)⁻¹)`. Rewrite using `[← hz]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe z`. Establish `e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹)` using `by simp`.

Rewrite `hint` using `[e, isIntegral_algebraMap_iff (algebraMap ℚ K).injective]`. Take `⟨m, hm⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Establish `hm' : (m : ℚ) = 2⁻¹` using `by simpa using hm`. Establish `h2 : ((m * 2 : ℤ) : ℚ) = 1`. Use `push_cast`.

Rewrite using `[hm']`. Evaluate the numerical expressions. Establish `h3 : m * 2 = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem half_not_integral {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral ℤ ((2 : K)⁻¹) := by
    rw [← hz]
    exact NumberField.RingOfIntegers.isIntegral_coe z
  have e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm' : (m : ℚ) = 2⁻¹ := by simpa using hm
  have h2 : ((m * 2 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hm']
    norm_num
  have h3 : m * 2 = 1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (funext h)`.

Take `⟨⟨b, hb⟩, hbint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (S.biUnion fun v => Finset.univ.image v)`. Establish `hb0 : (b : K) ≠ 0`. Introduce `h0`. Establish `: b = 0` using `by exact_mod_cast h0`. Conclude with `nonZeroDivisors.ne_zero hb this`.

Establish `hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j)`. Introduce `v hv j`. Take `⟨z, hz⟩` from `hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)`. Use `⟨z, ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 K) K z = _`.

Rewrite using `[hz, Algebra.smul_def]`. Establish `hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j)`. Introduce `w hw`. Rewrite `hw` using `[← hS]`. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem v hv => exact hgen v hv`. Consider the case `zero => intro j; exact ⟨0, by simp⟩`. Consider the case `add v w _ _ hv hw`. Introduce `j`. Take `⟨z1, hz1⟩` from `hv j`.

Take `⟨z2, hz2⟩` from `hw j`. Use `⟨z1 + z2, ?_⟩` and prove the remaining obligations. Use `push_cast`. Rewrite using `[Pi.add_apply, mul_add]`. Conclude with `congrArg₂ (· + ·) hz1 hz2`.

Consider the case `smul a v _ hv`. Introduce `j`. Take `⟨z, hz⟩` from `hv j`. Use `⟨a * z, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hall _ (hline ((2 * (b : K) * x i)⁻¹)) i`. Apply `half_not_integral (K := K)` to reduce the goal to its premises.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts.
-/
theorem no_line {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) (x : Fin r → K) (hx : x ≠ 0) (hline : ∀ t : K, t • x ∈ L) : False := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun v => Finset.univ.image v)
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    have : b = 0 := by exact_mod_cast h0
    exact nonZeroDivisors.ne_zero hb this
  have hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j) := by
    intro v hv j
    obtain ⟨z, hz⟩ := hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    refine ⟨z, ?_⟩
    show algebraMap (𝓞 K) K z = _
    rw [hz, Algebra.smul_def]
  have hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j) := by
    intro w hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => intro j; exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      intro j
      obtain ⟨z1, hz1⟩ := hv j
      obtain ⟨z2, hz2⟩ := hw j
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [Pi.add_apply, mul_add]
      exact congrArg₂ (· + ·) hz1 hz2
    | smul a v _ hv =>
      intro j
      obtain ⟨z, hz⟩ := hv j
      refine ⟨a * z, ?_⟩
      push_cast
      rw [Pi.smul_apply, Algebra.smul_def]
      calc (a : K) * (z : K) = (a : K) * ((b : K) * v j) := congrArg (fun q => (a : K) * q) hz
        _ = (b : K) * (algebraMap (𝓞 K) K a * v j) := by
          show (a : K) * ((b : K) * v j) = (b : K) * ((a : K) * v j)
          ring
  have h1 := hall _ (hline ((2 * (b : K) * x i)⁻¹)) i
  apply half_not_integral (K := K)
  convert h1 using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/- English proof (translation)
Rewrite using `[HermForm.h, HermForm.h, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (t : K) (x y : Fin r → K) : S.h (t • x) y = S.c t * S.h x y := by
  rw [HermForm.h, HermForm.h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/- English proof (translation)
Introduce `hdet`. Establish `hdetT : S.Gᵀ.det = 0` using `by rw [Matrix.det_transpose]; exact hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdetT`. Establish `hw0 : (fun a => S.c (v a)) ≠ 0`. Introduce `h`.

Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Establish `h1` using `congrArg S.c (congrFun h a)`. Simplify `h1` using `[S.c_invol]`. Establish `hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0`.

Introduce `y`. Simplify using `only [HermForm.h, S.c_invol]`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`.

Establish `hb` using `congrFun hv b`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb`. Rewrite using `[← Finset.sum_mul]`. Establish `h2 : ∑ a, v a * S.G a b = 0`. Rewrite using `[← hb]`.

Conclude with `Finset.sum_congr rfl (fun a _ => mul_comm _ _)`. Rewrite using `[h2, zero_mul]`. Apply `no_line L hL.1 _ hw0` to reduce the goal to its premises. Introduce `t`. Apply `hSD.2` to reduce the goal to its premises.

Introduce `y _`. Rewrite using `[hermForm_smul_left, hzero, mul_zero]`. Conclude with `⟨0, by simp⟩`.
-/
theorem detG_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by
  intro hdet
  have hdetT : S.Gᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hw0 : (fun a => S.c (v a)) ≠ 0 := by
    intro h
    apply hv0
    funext a
    have h1 := congrArg S.c (congrFun h a)
    simpa [S.c_invol] using h1
  have hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0 := by
    intro y
    simp only [HermForm.h, S.c_invol]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have hb := congrFun hv b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb
    rw [← Finset.sum_mul]
    have h2 : ∑ a, v a * S.G a b = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [h2, zero_mul]
  apply no_line L hL.1 _ hw0
  intro t
  apply hSD.2
  intro y _
  rw [hermForm_smul_left, hzero, mul_zero]
  exact ⟨0, by simp⟩

end ReciprocityTheory.MultiplicativeHeights.SemiPt
