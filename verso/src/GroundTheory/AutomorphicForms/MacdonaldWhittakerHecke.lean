import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldWhittaker

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

/- English proof (translation)
Use `Continuous.integrable_of_hasCompactSupport ?_ (h : HeckeAlgebra μ).mem.2.mul_right` and prove the remaining obligations. Conclude with `(h : HeckeAlgebra μ).mem.1.continuous.mul ((continuous_of_mul_right_invariant hf).comp (continuous_mul_left g))`.
-/
theorem integrable_hecke_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (h : SphericalHecke μ (F := F) (n := n))
    (g : GL (Fin n) F) :
    Integrable (fun x => (h : HeckeAlgebra μ) x * f (g * x)) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (h : HeckeAlgebra μ).mem.2.mul_right
  exact (h : HeckeAlgebra μ).mem.1.continuous.mul
    ((continuous_of_mul_right_invariant hf).comp (continuous_mul_left g))

/- English proof (translation)
Establish `hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'`. Establish `: (fun x => ((1 : SphericalHecke μ (F` using `F) (n := n)) : HeckeAlgebra μ) x * f (g * x)) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ * f g) := by`. Use function extensionality and compare the values at `x`. Rewrite using `[HeckeAlgebraLevel.val_one, idem_apply]`. Distinguish the cases in `hx : x ∈ integralGL F n`.

Rewrite using `[Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), hf g x hx]`. Rewrite using `[Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]`. Rewrite using `[this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const, Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]`.
-/
theorem integral_one_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) :
    ∫ x, ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ = f g := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have : (fun x => ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x)) =
      (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ * f g) := by
    funext x
    rw [HeckeAlgebraLevel.val_one, idem_apply]
    by_cases hx : x ∈ integralGL F n
    · rw [Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), hf g x hx]
    · rw [Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]
  rw [this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]

/- English proof (translation)
Rewrite using `[map_mul, map_mul]`. Establish `hconv : ∀ x, (((h₁ * h₂ : SphericalHecke μ (F` using `F) (n := n)) : HeckeAlgebra μ) x) = ∫ y, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) ∂μ := by`. Introduce `x`. Rewrite using `[HeckeAlgebraLevel.val_mul, HeckeAlgebra.coe_mul]`. Both sides reduce to the same expression.

Simplify using `only [hconv, ← integral_mul_const]`. Use `set B := tsupport ((h₁ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)`. Use `set C := tsupport ((h₂ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)`. Establish `hB : IsCompact B` using `(h₁ : HeckeAlgebra μ).mem.2`. Establish `hC : IsCompact C` using `(h₂ : HeckeAlgebra μ).mem.2`.

Establish `hswap` using `integral_integral_swap_of_coset μ (integralOpen F n) (isCompact_integralGL F n) (hB.mul hC) hB (F := fun x y => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x)) (by`. Introduce `x y hxy`. Establish `hy : y ∈ B` using `subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hxy))`. Establish `hx : y⁻¹ * x ∈ C` using `subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hxy))`. Conclude with `⟨Set.mem_mul.2 ⟨y, hy, y⁻¹ * x, hx, by group⟩, hy⟩)`.

Use the proof step `(by`. Introduce `x y k hk`. Rewrite using `[← mul_assoc, (HeckeAlgebraLevel.val_mem _ _ h₂ k hk _).2, ← mul_assoc, hf _ k hk])`. Use the proof step `(by`. Introduce `x y k hk`.

Rewrite using `[(HeckeAlgebraLevel.val_mem _ _ h₁ k hk y).2, _root_.mul_inv_rev, show k⁻¹ * y⁻¹ * x = k⁻¹ * (y⁻¹ * x) from mul_assoc _ _ _, HeckeAlgebraLevel.apply_mul_left _ _ h₂ ((integralGL F n).inv_mem hk)])`. Rewrite using `[hswap]`. Establish `hinner : ∀ y, ∫ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x) ∂μ = (h₁ : HeckeAlgebra μ) y * f (g * y) * evalAt z (satakeTransform μ h₂)`. Introduce `y`. Establish `e` using `integral_mul_left_eq_self (μ := μ) (fun x => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x)) y`.

Simplify using `only [inv_mul_cancel_left] at e`. Rewrite using `[← e]`. Establish `hpt : ∀ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) x * f (g * (y * x)) = (h₁ : HeckeAlgebra μ) y * ((h₂ : HeckeAlgebra μ) x * f ((g * y) * x))`. Introduce `x`. Rewrite using `[mul_assoc g y x]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hh₂ (g * y)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const, hh₁ g]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_mul_mul_eigen (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {h₁ h₂ : SphericalHecke μ (F := F) (n := n)}
    (hh₁ : ∀ g, ∫ x, (h₁ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₁) * f g)
    (hh₂ : ∀ g, ∫ x, (h₂ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₂) * f g)
    (g : GL (Fin n) F) :
    ∫ x, ((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ =
      evalAt z (satakeTransform μ (h₁ * h₂)) * f g := by
  rw [map_mul, map_mul]
  have hconv : ∀ x, (((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x) =
      ∫ y, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) ∂μ := by
    intro x
    rw [HeckeAlgebraLevel.val_mul, HeckeAlgebra.coe_mul]
    rfl
  simp only [hconv, ← integral_mul_const]
  set B := tsupport ((h₁ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  set C := tsupport ((h₂ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  have hB : IsCompact B := (h₁ : HeckeAlgebra μ).mem.2
  have hC : IsCompact C := (h₂ : HeckeAlgebra μ).mem.2
  have hswap := integral_integral_swap_of_coset μ (integralOpen F n) (isCompact_integralGL F n)
    (hB.mul hC) hB (F := fun x y => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) *
      f (g * x))
    (by
      intro x y hxy
      have hy : y ∈ B := subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      have hx : y⁻¹ * x ∈ C := subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      exact ⟨Set.mem_mul.2 ⟨y, hy, y⁻¹ * x, hx, by group⟩, hy⟩)
    (by
      intro x y k hk
      rw [← mul_assoc, (HeckeAlgebraLevel.val_mem _ _ h₂ k hk _).2, ← mul_assoc, hf _ k hk])
    (by
      intro x y k hk
      rw [(HeckeAlgebraLevel.val_mem _ _ h₁ k hk y).2, _root_.mul_inv_rev,
        show k⁻¹ * y⁻¹ * x = k⁻¹ * (y⁻¹ * x) from mul_assoc _ _ _,
        HeckeAlgebraLevel.apply_mul_left _ _ h₂ ((integralGL F n).inv_mem hk)])
  rw [hswap]
  have hinner : ∀ y, ∫ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x) ∂μ =
      (h₁ : HeckeAlgebra μ) y * f (g * y) * evalAt z (satakeTransform μ h₂) := by
    intro y
    have e := integral_mul_left_eq_self (μ := μ)
      (fun x => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x)) y
    simp only [inv_mul_cancel_left] at e
    rw [← e]
    have hpt : ∀ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) x * f (g * (y * x)) =
        (h₁ : HeckeAlgebra μ) y * ((h₂ : HeckeAlgebra μ) x * f ((g * y) * x)) := by
      intro x
      rw [mul_assoc g y x]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hh₂ (g * y)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const, hh₁ g]
  ring

variable (μ) in

def eigenSubalgebra (z : Fin n → ℂˣ) (f : GL (Fin n) F → ℂ)
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) :
    Subalgebra ℂ (SphericalHecke μ (F := F) (n := n)) where
  carrier := {h | ∀ g, ∫ x, (h : HeckeAlgebra μ) x * f (g * x) ∂μ =
    evalAt z (satakeTransform μ h) * f g}
  mul_mem' {h₁ h₂} hh₁ hh₂ g := integral_mul_mul_eigen z hf hh₁ hh₂ g
  one_mem' g := by
    simp only [Set.mem_setOf_eq, map_one, one_mul]
    exact integral_one_mul hf g
  add_mem' {h₁ h₂} hh₁ hh₂ g := by
    simp only [HeckeAlgebraLevel.val_add, HeckeAlgebra.coe_add, Pi.add_apply, add_mul]
    rw [integral_add (integrable_hecke_mul hf h₁ g) (integrable_hecke_mul hf h₂ g), hh₁, hh₂,
      map_add, map_add, add_mul]
  zero_mem' g := by
    simp [HeckeAlgebraLevel.val_zero]
  algebraMap_mem' c g := by
    rw [Algebra.algebraMap_eq_smul_one, HeckeAlgebraLevel.val_smul, HeckeAlgebra.coe_smul, map_smul,
      map_smul, smul_eq_mul, map_one, map_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_one_mul hf g]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
/- English proof (translation)
Rewrite using `[MvPolynomial.esymm, map_sum, esymmL]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[map_prod]`. Simplify using `only [polyEmb_X, monomial]`. Rewrite using `[AddMonoidAlgebra.prod_single, Finset.prod_const_one, sum_single_one]`.
-/
theorem polyEmb_esymm (k : ℕ) : polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) = esymmL n k := by
  rw [MvPolynomial.esymm, map_sum, esymmL]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]
  simp only [polyEmb_X, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, sum_single_one]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
/- English proof (translation)
Rewrite using `[esymmL, Finset.powersetCard_eq_empty.2 (by simpa using hk), Finset.sum_empty]`.
-/
theorem esymmL_eq_zero {k : ℕ} (hk : n < k) : esymmL n k = 0 := by
  rw [esymmL, Finset.powersetCard_eq_empty.2 (by simpa using hk), Finset.sum_empty]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (n : ℤ) - 1 - 2 * (i : ℤ)) n, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]`. Establish `h` using `Finset.sum_range_id_mul_two n`. Establish `h' : (∑ i ∈ Finset.range n, (i : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1)`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Simplify using the standard rewrite rules. Establish `: (((∑ i ∈ Finset.range n, i) * 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ)` using `by rw [h]`. Move the coercions through the operations in `[Nat.cast_sub hn] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [nsmul_eq_mul]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_rho_coeff : ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (n : ℤ) - 1 - 2 * (i : ℤ)) n, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
  have h := Finset.sum_range_id_mul_two n
  have h' : (∑ i ∈ Finset.range n, (i : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have : (((∑ i ∈ Finset.range n, i) * 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by rw [h]
      push_cast [Nat.cast_sub hn] at this
      linarith
  simp only [nsmul_eq_mul]
  linarith

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

/- English proof (translation)
Rewrite using `[halfModulus_eq, rhoPair]`. Simplify using `only [mul_comm _ c, ← Finset.mul_sum, sum_rho_coeff, mul_zero, neg_zero, zpow_zero]`.
-/
theorem halfModulus_const (c : ℤ) : halfModulus F (fun _ : Fin n => c) = 1 := by
  rw [halfModulus_eq, rhoPair]
  simp only [mul_comm _ c, ← Finset.mul_sum, sum_rho_coeff, mul_zero, neg_zero, zpow_zero]

/- English proof (translation)
Use `eq_of_forall_evalAt fun w => ?_` and prove the remaining obligations. Rewrite using `[evalAt_satakeTransform_minusculeHecke w hk, map_smul, smul_eq_mul]`.
-/
theorem satakeTransform_minusculeHecke {k : ℕ} (hk : k ≤ n) :
    satakeTransform μ (minusculeHecke μ k) =
      ((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k))) • esymmL n k := by
  refine eq_of_forall_evalAt fun w => ?_
  rw [evalAt_satakeTransform_minusculeHecke w hk, map_smul, smul_eq_mul]

/- English proof (translation)
Rewrite using `[satakeTransform_apply, satake_centralHecke, map_smul, monomial, normalize_single, halfModulus_const, one_mul]`.
-/
theorem satakeTransform_centralHecke :
    satakeTransform μ (centralHecke μ) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) • monomial (fun _ : Fin n => (-1 : ℤ)) := by
  rw [satakeTransform_apply, satake_centralHecke, map_smul, monomial, normalize_single,
    halfModulus_const, one_mul]

/- English proof (translation)
Use `set E := eigenSubalgebra μ z f hf`. Use `set A := E.map (satakeTransform μ)`. Establish `hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'`. Establish `h1 : ∀ k, polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) ∈ A`. Introduce `k`.

Rewrite using `[polyEmb_esymm]`. Distinguish the cases in `hk : k ≤ n`. Establish `hc' : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k)) ≠ 0` using `mul_ne_zero hK (pow_ne_zero _ sqrtQ_ne_zero)`. Use `Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k)))⁻¹ • minusculeHecke μ k, E.smul_mem (hT k hk) _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, satakeTransform_minusculeHecke hk, smul_smul, inv_mul_cancel₀ hc', one_smul]`.

Rewrite using `[esymmL_eq_zero (by omega)]`. Conclude with `A.zero_mem`. Establish `h2 : monomial (fun _ : Fin n => (-1 : ℤ)) ∈ A`. Use `Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ))⁻¹ • centralHecke μ, E.smul_mem hc _, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, satakeTransform_centralHecke, smul_smul, inv_mul_cancel₀ hK, one_smul]`.

Establish `hsym` using `symmetricLaurent_le h1 h2`. Rewrite using `[Algebra.eq_top_iff]`. Introduce `h`. Take `⟨e, he, hSe⟩` from `Subalgebra.mem_map.1 (hsym (satakeTransform_mem_symmetric h))`. Rewrite using `[← satakeTransform_injective hSe]` and apply the resulting hypothesis.
-/
theorem eigenSubalgebra_eq_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : ∀ r ≤ n, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf)
    (hc : centralHecke μ ∈ eigenSubalgebra μ z f hf) : eigenSubalgebra μ z f hf = ⊤ := by
  set E := eigenSubalgebra μ z f hf
  set A := E.map (satakeTransform μ)
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 : ∀ k, polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) ∈ A := by
    intro k
    rw [polyEmb_esymm]
    by_cases hk : k ≤ n
    · have hc' : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k)) ≠ 0 :=
        mul_ne_zero hK (pow_ne_zero _ sqrtQ_ne_zero)
      refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        sqrtQ F ^ (k * (n - k)))⁻¹ • minusculeHecke μ k, E.smul_mem (hT k hk) _, ?_⟩
      rw [map_smul, satakeTransform_minusculeHecke hk, smul_smul, inv_mul_cancel₀ hc', one_smul]
    · rw [esymmL_eq_zero (by omega)]
      exact A.zero_mem
  have h2 : monomial (fun _ : Fin n => (-1 : ℤ)) ∈ A := by
    refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ))⁻¹ •
      centralHecke μ, E.smul_mem hc _, ?_⟩
    rw [map_smul, satakeTransform_centralHecke, smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hsym := symmetricLaurent_le h1 h2
  rw [Algebra.eq_top_iff]
  intro h
  obtain ⟨e, he, hSe⟩ := Subalgebra.mem_map.1 (hsym (satakeTransform_mem_symmetric h))
  rwa [← satakeTransform_injective hSe]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Use `h hij` as an intermediate fact. Simplify using `only [Pi.add_apply] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `h i j hij`. Simplify using `only [Pi.add_apply]`. Combine the linear relations using `[h hij]`.
-/
theorem antitone_add_const_iff (l : Fin n → ℤ) (c : ℤ) :
    Antitone (l + fun _ => c) ↔ Antitone l := by
  constructor
  · intro h i j hij
    have := h hij
    simp only [Pi.add_apply] at this
    linarith
  · intro h i j hij
    simp only [Pi.add_apply]
    linarith [h hij]

/- English proof (translation)
Rewrite using `[schur, schur, show l + (fun _ => c) + staircase n = (fun _ => c) + (l + staircase n) by abel, monomial_add, altQuot_mul_of_symm (permAct_monomial_const c)]`.
-/
theorem schur_add_const (l : Fin n → ℤ) (c : ℤ) :
    schur (l + fun _ => c) = monomial (fun _ : Fin n => c) * schur l := by
  rw [schur, schur, show l + (fun _ => c) + staircase n = (fun _ => c) + (l + staircase n) by abel,
    monomial_add, altQuot_mul_of_symm (permAct_monomial_const c)]

/- English proof (translation)
Establish `hg` using `eq_iwasawa g`. Establish `hu` using `iwasawaUnip_mem g`. Establish `hk` using `iwasawaInt_mem g`. Use `set u := iwasawaUnip g`. Use `set e := iwasawaExponent F n g`.

Use `set k := iwasawaInt g`. Establish `: g * torusPow F n (fun _ => c) = u * torusPow F n (e + fun _ => c) * k`. Rewrite using `[hg, torusPow_add, mul_assoc, ← torusPow_const_comm c k]`. Use `group`. Rewrite using `[this, sphericalWhittaker_apply hψ₀ z hu hk, hg, sphericalWhittaker_apply hψ₀ z hu hk]`.

Distinguish the cases in `he : Antitone e`. Rewrite using `[if_pos ((antitone_add_const_iff e c).2 he), if_pos he, halfModulus_add, halfModulus_const, schur_add_const, map_mul, monomial, evalAt_single, one_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg (fun h => he ((antitone_add_const_iff e c).1 h)), if_neg he, mul_zero]`.
-/
theorem sphericalWhittaker_mul_const {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) (c : ℤ) :
    sphericalWhittaker ψ₀ z (g * torusPow F n (fun _ => c)) =
      monomialChar (fun _ : Fin n => c) z * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  set u := iwasawaUnip g
  set e := iwasawaExponent F n g
  set k := iwasawaInt g
  have : g * torusPow F n (fun _ => c) = u * torusPow F n (e + fun _ => c) * k := by
    rw [hg, torusPow_add, mul_assoc, ← torusPow_const_comm c k]
    group
  rw [this, sphericalWhittaker_apply hψ₀ z hu hk, hg, sphericalWhittaker_apply hψ₀ z hu hk]
  by_cases he : Antitone e
  · rw [if_pos ((antitone_add_const_iff e c).2 he), if_pos he, halfModulus_add, halfModulus_const,
      schur_add_const, map_mul, monomial, evalAt_single, one_mul]
    ring
  · rw [if_neg (fun h => he ((antitone_add_const_iff e c).1 h)), if_neg he, mul_zero]

/- English proof (translation)
Use `set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))`. Establish `e` using `integral_mul_left_eq_self (μ := μ) (fun x => (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x)) g₀`. Rewrite using `[← e]`. Establish `hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) * sphericalWhittaker ψ₀ z (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator (fun _ => sphericalWhittaker ψ₀ z (g * g₀))`. Use function extensionality and compare the values at `y`.

Rewrite using `[centralHecke_apply]`. Distinguish the cases in `hy : y ∈ integralGL F n`. Establish `hm : g₀ * y ∈ centralSet F n`. Rewrite using `[mem_centralSet, inv_mul_cancel_left]`. Conclude with `hy`.

Rewrite using `[Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F)) from hy), one_mul, ← mul_assoc, sphericalWhittaker_mul_right hψ₀ z _ hy]`. Establish `hm : g₀ * y ∉ centralSet F n`. Rewrite using `[mem_centralSet, inv_mul_cancel_left]`. Conclude with `hy`. Rewrite using `[Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n : Set (GL (Fin n) F)) from hy), zero_mul]`.

Rewrite using `[hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const, Complex.real_smul, sphericalWhittaker_mul_const hψ₀, satakeTransform_centralHecke, map_smul, monomial, evalAt_single, one_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_centralHecke_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ}
    (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ (centralHecke μ)) * sphericalWhittaker ψ₀ z g := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      sphericalWhittaker ψ₀ z (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => sphericalWhittaker ψ₀ z (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, sphericalWhittaker_mul_right hψ₀ z _ hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, sphericalWhittaker_mul_const hψ₀, satakeTransform_centralHecke, map_smul,
    monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `htop` using `eigenSubalgebra_eq_top (μ := μ) z (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk) (fun r hr g => integral_minusculeHecke_mul_sphericalWhittaker hψ₀ hψ₁ z hr g) (fun g => integral_centralHecke_mul_sphericalWhittaker hψ₀ z g)`. Establish `hmem : h ∈ eigenSubalgebra μ z (sphericalWhittaker ψ₀ z) (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk)`. Rewrite using `[htop]`. Conclude with `Algebra.mem_top`. Conclude with `hmem g`.
-/
theorem integral_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    ∫ x, (h : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ h) * sphericalWhittaker ψ₀ z g := by
  have htop := eigenSubalgebra_eq_top (μ := μ) z
    (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk)
    (fun r hr g => integral_minusculeHecke_mul_sphericalWhittaker hψ₀ hψ₁ z hr g)
    (fun g => integral_centralHecke_mul_sphericalWhittaker hψ₀ z g)
  have hmem : h ∈ eigenSubalgebra μ z (sphericalWhittaker ψ₀ z)
      (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk) := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g

/- English proof (translation)
Establish `hg` using `eq_iwasawa g`. Establish `hu` using `iwasawaUnip_mem g`. Establish `hk` using `iwasawaInt_mem g`. Rewrite using `[hg, sphericalWhittaker_apply hψ₀ z hu hk, hWK _ _ hk, mul_assoc, hWN _ hu, casselman_shalika ψ₀ hψ₀ hψ₁ z hWN hWK heig]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem eq_smul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ) {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (g : GL (Fin n) F) : W g = W 1 * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, sphericalWhittaker_apply hψ₀ z hu hk, hWK _ _ hk, mul_assoc, hWN _ hu,
    casselman_shalika ψ₀ hψ₀ hψ₁ z hWN hWK heig]
  split_ifs <;> ring

end Spherical

end GroundTheory.Automorphic
