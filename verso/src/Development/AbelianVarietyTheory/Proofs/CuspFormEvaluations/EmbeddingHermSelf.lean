import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TraceDualMin

/- English proof (translation)
Simplify using `[herm, Matrix.one_apply]`.
-/
theorem herm_one_eq {n : ℕ} (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

/- English proof (translation)
Simplify using `[herm_one_eq, Finset.mul_sum, mul_assoc]`.
-/
theorem herm_smul_left {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 (a • x) y = a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[herm_one_eq, Finset.mul_sum, cc, mul_left_comm]`.
-/
theorem herm_smul_right {n : ℕ} (a : E) (x y : Fin n → E) :
    herm 1 x (a • y) = cc a * herm 1 x y := by
  simp [herm_one_eq, Finset.mul_sum, cc, mul_left_comm]

/- English proof (translation)
Simplify using `[cc]`.
-/
theorem cc_cc (a : E) : cc (cc a) = a := by
  simp [cc]

/- English proof (translation)
Simplify using `[herm_one_eq, cc, mul_comm]`.
-/
theorem cc_herm_self {n : ℕ} (x : Fin n → E) : cc (herm 1 x x) = herm 1 x x := by
  simp [herm_one_eq, cc, mul_comm]

/- English proof (translation)
The claim follows from `Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a`.
-/
theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

/- English proof (translation)
The claim follows from `ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom`.
-/
theorem isIntegral_cc {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom

/- English proof (translation)
Simplify using `[herm_one_eq, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']`.
-/
theorem embedding_herm_self {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (herm 1 x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by
  simp [herm_one_eq, cc, IsCMField.complexEmbedding_complexConj, Complex.mul_conj']

omit [IsCMField E] in

/- English proof (translation)
Rewrite using `[← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one, Submodule.mem_traceDual]`. Introduce `a ha`. Take `⟨b, rfl⟩` from `Submodule.mem_one.mp ha`. Take `⟨k, hk⟩` from `hx b`. Conclude with `⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩`.
-/
theorem mem_inv_different {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one,
    Submodule.mem_traceDual]
  intro a ha
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨k, hk⟩ := hx b
  exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩

end TraceDualMin

open TraceDualMin in

/- English proof (translation)
Use `set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD`. Establish `hD0 : D ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot`. Establish `h1 : ∀ y ∈ Λ, herm 1 u y ∈ D⁻¹`. Introduce `y hy`. Use `mem_inv_different fun a => ?_` and prove the remaining obligations.

Take `⟨k, hk⟩` from `htr _ (Λ.smul_mem (⟨cc (a : E), isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk]`. Express the relevant statement in the definitionally equal form `_ = Algebra.trace ℚ E (herm 1 u (cc (a : E) • y))`. Rewrite using `[herm_smul_right, cc_cc, mul_comm]`.

Establish `h2 : ∀ δ ∈ D, δ • u ∈ Λ`. Introduce `δ hδ`. Use `hdual _ fun y hy => ?_` and prove the remaining obligations. Rewrite using `[herm_smul_left]`. Use `FractionalIdeal.mul_mem_mul hδ (h1 y hy)` as an intermediate fact.

Rewrite `this` using `[mul_inv_cancel₀ hD0]`. Take `⟨b, hb⟩` from `(FractionalIdeal.mem_one_iff _).mp this`. Rewrite using `[← hb]`. Conclude with `b.isIntegral_coe`. Establish `h3 : ∀ δ ∈ D, herm 1 u u * δ ∈ D⁻¹`.

Introduce `δ hδ`. Use `mem_inv_different fun a => ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `htr _ (Λ.smul_mem a (h2 δ hδ))`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, ← trace_cc]`.

Express the relevant statement in the definitionally equal form `_ = Algebra.trace ℚ E (herm 1 u ((a : E) • δ • u))`. Rewrite using `[herm_smul_right, herm_smul_right]`. Use `congr 1`. Use `conv_rhs => rw [← cc_herm_self u]`. Simplify using `only [cc, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : herm 1 u u ∈ D⁻¹ * D⁻¹`. Rewrite using `[← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]`. Conclude with `h3`. Establish `hnorm : ∀ σ : E →+* ℂ, ‖σ (herm 1 u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2`.

Introduce `σ`. Rewrite using `[embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]`. Establish `h0 : herm 1 u u ≠ 0`. Introduce `h`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Use `hnorm σ` as an intermediate fact. Rewrite `this` using `[h, map_zero, norm_zero, eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]`. Apply `hu` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Simplify using `using this k (Finset.mem_univ k)`.

Establish `h5` using `absNorm_le_abs_norm_of_mem h4 h0`. Rewrite `h5` using `[map_mul, hD, absNorm_inv_differentIdeal]`. Establish `h6 : (dE E)⁻¹ * (dE E)⁻¹ ≤ |((Algebra.norm ℚ (herm 1 u u) : ℚ) : ℝ)|`. Establish `h` using `(Rat.cast_le (K := ℝ)).mpr h5`. Simplify `h` using `[dE]`.

Establish `h7` using `finrank_mul_abs_norm_rpow_le_sum (herm 1 u u)`. Simplify using `only [hnorm] at h7`. Use `le_trans ?_ h7` and prove the remaining obligations. Establish `hd : 0 ≤ dE E` using `abs_nonneg _`. Establish `hf : 2 * (fdeg E : ℝ) ≤ (Module.finrank ℚ E : ℝ)`.

Conclude with `Nat.mul_div_le (Module.finrank ℚ E) 2` after adjusting the coercions. Establish `h8 : (rdE E ^ 2)⁻¹ = ((dE E)⁻¹ * (dE E)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹)`. Rewrite using `[Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rdE, one_div, sq, mul_inv]`. Rewrite using `[div_eq_mul_inv, h8]`. Use `gcongr`.
-/
theorem trace_dual_min {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ)
    (u : Fin n → E) (hu : u ≠ 0) (htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (herm 1 u y) = k) :
    2 * (fdeg E : ℝ) / rdE E ^ 2 ≤ ∑ σ : E →+* ℂ, ∑ k, ‖σ (u k)‖ ^ 2 := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot

  have h1 : ∀ y ∈ Λ, herm 1 u y ∈ D⁻¹ := by
    intro y hy
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem (⟨cc (a : E), isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (herm 1 u (cc (a : E) • y))
    rw [herm_smul_right, cc_cc, mul_comm]
  have h2 : ∀ δ ∈ D, δ • u ∈ Λ := by
    intro δ hδ
    refine hdual _ fun y hy => ?_
    rw [herm_smul_left]
    have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
    rw [mul_inv_cancel₀ hD0] at this
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
    rw [← hb]
    exact b.isIntegral_coe
  have h3 : ∀ δ ∈ D, herm 1 u u * δ ∈ D⁻¹ := by
    intro δ hδ
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem a (h2 δ hδ))
    refine ⟨k, ?_⟩
    rw [← hk, ← trace_cc]
    change _ = Algebra.trace ℚ E (herm 1 u ((a : E) • δ • u))
    rw [herm_smul_right, herm_smul_right]
    congr 1
    conv_rhs => rw [← cc_herm_self u]
    simp only [cc, map_mul]
    ring
  have h4 : herm 1 u u ∈ D⁻¹ * D⁻¹ := by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]
    exact h3
  have hnorm : ∀ σ : E →+* ℂ, ‖σ (herm 1 u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2 := by
    intro σ
    rw [embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : herm 1 u u ≠ 0 := by
    intro h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hnorm σ
    rw [h, map_zero, norm_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
    apply hu
    funext k
    simpa using this k (Finset.mem_univ k)
  have h5 := absNorm_le_abs_norm_of_mem h4 h0
  rw [map_mul, hD, absNorm_inv_differentIdeal] at h5
  have h6 : (dE E)⁻¹ * (dE E)⁻¹ ≤ |((Algebra.norm ℚ (herm 1 u u) : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr h5
    simpa [dE] using h
  have h7 := finrank_mul_abs_norm_rpow_le_sum (herm 1 u u)
  simp only [hnorm] at h7
  refine le_trans ?_ h7
  have hd : 0 ≤ dE E := abs_nonneg _
  have hf : 2 * (fdeg E : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Nat.mul_div_le (Module.finrank ℚ E) 2
  have h8 : (rdE E ^ 2)⁻¹ = ((dE E)⁻¹ * (dE E)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rdE, one_div, sq,
      mul_inv]
  rw [div_eq_mul_inv, h8]
  gcongr

end GlobalTheory
