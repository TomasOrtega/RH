import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DeformedSum

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℂ => a + t * b) b u`. Simplify using `using ((hasDerivAt_id u).mul_const b).const_add a`. Establish `h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n) (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u` using `((h1.inv hu).pow n).const_mul c`. Use `h2.congr_deriv ?_` and prove the remaining obligations. Break down `n with _ | n` into its components or cases.

Simplify using the standard rewrite rules. Rewrite using `[Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_inv_pow_affine (c a b : ℂ) (n : ℕ) (u : ℂ) (hu : a + u * b ≠ 0) :
    HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (-(n : ℂ) * b * (a + u * b)⁻¹ ^ (n + 1))) u := by
  have h1 : HasDerivAt (fun t : ℂ => a + t * b) b u := by
    simpa using ((hasDerivAt_id u).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℂ => c * (a + t * b)⁻¹ ^ n)
      (c * (n * (a + u * b)⁻¹ ^ (n - 1) * (-b / (a + u * b) ^ 2))) u :=
    ((h1.inv hu).pow n).const_mul c
  refine h2.congr_deriv ?_
  rcases n with _ | n
  · simp
  · rw [Nat.add_sub_cancel, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring

/- English proof (translation)
Introduce `h`. Establish `hφ : φ i x ≠ 0` using `(map_ne_zero (φ i)).mpr hx`. Establish `hpos : 0 < ‖φ i x‖` using `norm_pos_iff.mpr hφ`. Establish `hz1 : ‖z i‖ < 1` using `hz i`. Unfold `defCoord at h`.

Establish `heq : φ i x = -(z i * starRingEnd ℂ (φ i x))` using `eq_neg_of_add_eq_zero_left h`. Establish `hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖` using `by conv_lhs => rw [heq]`. Rewrite using `[norm_neg, norm_mul, Complex.norm_conj]`. Establish `hlt` using `mul_lt_of_lt_one_left hpos hz1`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem defCoord_ne_zero {E : Type} [Field E] [NumberField E] {I : Type} (φ : I → E →+* ℂ) (z : I → ℂ)
    (hz : z ∈ polydisc I) (x : E) (hx : x ≠ 0) (i : I) : defCoord φ z x i ≠ 0 := by
  intro h
  have hφ : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx
  have hpos : 0 < ‖φ i x‖ := norm_pos_iff.mpr hφ
  have hz1 : ‖z i‖ < 1 := hz i
  unfold defCoord at h
  have heq : φ i x = -(z i * starRingEnd ℂ (φ i x)) := eq_neg_of_add_eq_zero_left h
  have hn : ‖φ i x‖ = ‖z i‖ * ‖φ i x‖ := by
    conv_lhs => rw [heq]
    rw [norm_neg, norm_mul, Complex.norm_conj]
  have hlt := mul_lt_of_lt_one_left hpos hz1
  linarith

/- English proof (translation)
Introduce `E _ _ I _ _ φ k m x hx z hz`. Use `set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i with hC`. Establish `hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) • ContinuousLinearMap.proj (R` using `ℂ) (φ := fun _ : I => ℂ) i) z := by`. Introduce `i`. Establish `h1` using `hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i) (defCoord_ne_zero φ z hz x hx i)`.

Establish `h2` using `h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)`. Conclude with `h2`. Establish `hprod` using `HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)`. Establish `hfun : (fun w : I → ℂ => dTerm φ k m w x) = (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i))` using `rfl`. Rewrite using `[hfun]`.

Use `hprod.congr_fderiv ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `congr 1`. Use `symm`.

Unfold `dTerm`. Rewrite using `[← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hij : i ≠ j` using `Finset.ne_of_mem_erase hi`.

Simplify using `[hC, hij]`. Simplify using `only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasFDerivAt_dTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ)
    (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x)
      (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := by
  intro E _ _ I _ _ φ k m x hx z hz
  set C : I → ℂ := fun i => ((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) *
    (starRingEnd ℂ (φ i x)) ^ m i with hC
  have hd : ∀ i, HasFDerivAt (fun w : I → ℂ => C i * (defCoord φ w x i)⁻¹ ^ (k + m i))
      ((C i * (-((k + m i : ℕ) : ℂ) * starRingEnd ℂ (φ i x) * (defCoord φ z x i)⁻¹ ^ (k + m i + 1))) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) z := by
    intro i
    have h1 := hasDerivAt_inv_pow_affine (C i) (φ i x) (starRingEnd ℂ (φ i x)) (k + m i) (z i)
      (defCoord_ne_zero φ z hz x hx i)
    have h2 := h1.comp_hasFDerivAt z (hasFDerivAt_apply (𝕜 := ℂ) (F' := fun _ : I => ℂ) i z)
    exact h2
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hd i)
  have hfun : (fun w : I → ℂ => dTerm φ k m w x) =
      (fun w => ∏ i ∈ Finset.univ, C i * (defCoord φ w x i)⁻¹ ^ (k + m i)) := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  symm
  unfold dTerm
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hij : i ≠ j := Finset.ne_of_mem_erase hi
    simp [hC, hij]
  · simp only [hC, Pi.add_apply, Pi.single_eq_same, Finset.prod_range_succ]
    push_cast
    ring

end GlobalTheory.DeformedSum

/- English proof (translation)
The claim follows from `GlobalTheory.DeformedSum.hasFDerivAt_dTerm`.
-/
example : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I, HasFDerivAt (fun w : I → ℂ => dTerm φ k m w x) (∑ j, dTerm φ k (m + Pi.single j 1) z x • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) j)) z := GlobalTheory.DeformedSum.hasFDerivAt_dTerm
