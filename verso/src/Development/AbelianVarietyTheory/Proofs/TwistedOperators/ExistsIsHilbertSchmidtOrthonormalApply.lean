import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitHeightSummableExpNegAbs
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `H K _ _ _ _ _ _ J u w hu hw`. Use `set S : ℝ := ∑' j, ‖w j‖ ^ 2`. Establish `hbes : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ ^ 2` using `fun v => hu.inner_products_summable v`. Establish `hbes_le : ∀ v : H, ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2` using `fun v => hu.tsum_inner_products_le v`. Establish `hsn : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ * ‖w j‖` using `fun v => Summable.of_nonneg_of_le (fun j => by positivity) (fun j => by nlinarith [sq_nonneg (‖⟪u j, v⟫_ℂ‖ - ‖w j‖)]) (((hbes v).add hw).div_const 2)`.

Establish `hsn' : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ • w j‖` using `fun v => (hsn v).congr fun j => (norm_smul _ _).symm`. Establish `hs : ∀ v : H, Summable fun j => ⟪u j, v⟫_ℂ • w j` using `fun v => (hsn' v).of_norm`. Set `L : H →ₗ[ℂ] K` to `{ toFun := fun v => ∑' j, ⟪u j, v⟫_ℂ • w j map_add' := fun v v' => by`. Simplify using `only [inner_add_right, add_smul]`. Conclude with `(hs v).tsum_add (hs v')`.

Use the proof step `map_smul' := fun c v => by`. Simplify using `only [inner_smul_right, mul_smul, RingHom.id_apply]`. Conclude with `(hs v).tsum_const_smul c }`. Establish `hbound : ∀ v, ‖L v‖ ≤ ((1 + S) / 2) * ‖v‖`. Introduce `v`.

Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using the standard rewrite rules. Use `set t := ‖v‖ with htdef`. Establish `ht : 0 < t` using `norm_pos_iff.2 hv`.

Use `set A : ℝ := ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2`. Establish `key : ∀ a b : ℝ, a * b ≤ (a ^ 2 * t⁻¹ + t * b ^ 2) / 2`. Introduce `a b`. Establish `h : a ^ 2 * t⁻¹ + t * b ^ 2 - 2 * (a * b) = t⁻¹ * (a - t * b) ^ 2` using `by field_simp; ring`. Establish `: 0 ≤ t⁻¹ * (a - t * b) ^ 2` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ‖L v‖ ≤ ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖`. Use `(norm_tsum_le_tsum_norm (hsn' v)).trans_eq ?_` and prove the remaining obligations. Simplify using `only [norm_smul]`. Establish `hA : HasSum (fun j => (‖⟪u j, v⟫_ℂ‖ ^ 2 * t⁻¹ + t * ‖w j‖ ^ 2) / 2) ((A * t⁻¹ + t * S) / 2)` using `(((hbes v).hasSum.mul_right t⁻¹).add (hw.hasSum.mul_left t)).div_const 2`.

Establish `h2 : ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ ≤ (A * t⁻¹ + t * S) / 2` using `hasSum_le (fun j => key _ _) (hsn v).hasSum hA`. Establish `h3 : A * t⁻¹ ≤ t`. Establish `: A * t⁻¹ ≤ t ^ 2 * t⁻¹` using `mul_le_mul_of_nonneg_right (hbes_le v) (inv_nonneg.2 ht.le)`. Establish `e : t ^ 2 * t⁻¹ = t` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `: (A * t⁻¹ + t * S) / 2 ≤ (1 + S) / 2 * t` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Set `G : H →L[ℂ] K` to `L.mkContinuous ((1 + S) / 2) hbound`. Establish `hG : ∀ v, G v = ∑' j, ⟪u j, v⟫_ℂ • w j` using `fun v => rfl`. Establish `hval : ∀ j, G (u j) = w j`.

Introduce `j`. Rewrite using `[hG, tsum_eq_single j (fun k hk => by rw [orthonormal_iff_ite.1 hu k j, if_neg hk, zero_smul]), orthonormal_iff_ite.1 hu j j, if_pos rfl, one_smul]`. Establish `hvan : ∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0`. Introduce `v h`. Rewrite using `[hG]`.

Simplify using `[h]`. Use `⟨G, hval, hvan, ?_⟩` and prove the remaining obligations. Take `⟨W, b, hsub, hb⟩` from `((orthonormal_subtype_range hu.linearIndependent.injective).2 hu).exists_hilbertBasis_extension`. Rewrite using `[GlobalTheory.OpTrace.isHilbertSchmidt_iff b]`. Set `e : J → W` to `fun j => ⟨u j, hsub ⟨j, rfl⟩⟩`.

Establish `hbe : ∀ j, b (e j) = u j` using `fun j => congrFun hb (e j)`. Establish `he : Function.Injective e` using `fun j k hjk => hu.linearIndependent.injective (congrArg Subtype.val hjk)`. Use `(he.summable_iff fun i hi => ?_).1 (hw.congr fun j => ?_)` and prove the remaining obligations. Establish `: G (b i) = 0` using `hvan _ fun j => by`. Rewrite using `[← hbe j]`.

Conclude with `b.orthonormal.2 fun h => hi ⟨j, h⟩`. Simplify using `[this]`. Simplify using `only [Function.comp_apply, hbe, hval]`.
-/
theorem exists_isHilbertSchmidt_orthonormal_apply : ∀ (H K : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (J : Type) (u : J → H) (w : J → K), Orthonormal ℂ u → Summable (fun j => ‖w j‖ ^ 2) → ∃ G : H →L[ℂ] K, (∀ j, G (u j) = w j) ∧ (∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0) ∧ GlobalTheory.OpTrace.IsHilbertSchmidt G := by
  intro H K _ _ _ _ _ _ J u w hu hw
  classical
  set S : ℝ := ∑' j, ‖w j‖ ^ 2
  have hbes : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ ^ 2 := fun v => hu.inner_products_summable v
  have hbes_le : ∀ v : H, ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 := fun v => hu.tsum_inner_products_le v
  have hsn : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := fun v =>
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => by nlinarith [sq_nonneg (‖⟪u j, v⟫_ℂ‖ - ‖w j‖)]) (((hbes v).add hw).div_const 2)
  have hsn' : ∀ v : H, Summable fun j => ‖⟪u j, v⟫_ℂ • w j‖ := fun v =>
    (hsn v).congr fun j => (norm_smul _ _).symm
  have hs : ∀ v : H, Summable fun j => ⟪u j, v⟫_ℂ • w j := fun v => (hsn' v).of_norm
  let L : H →ₗ[ℂ] K :=
    { toFun := fun v => ∑' j, ⟪u j, v⟫_ℂ • w j
      map_add' := fun v v' => by
        simp only [inner_add_right, add_smul]
        exact (hs v).tsum_add (hs v')
      map_smul' := fun c v => by
        simp only [inner_smul_right, mul_smul, RingHom.id_apply]
        exact (hs v).tsum_const_smul c }
  have hbound : ∀ v, ‖L v‖ ≤ ((1 + S) / 2) * ‖v‖ := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    set t := ‖v‖ with htdef
    have ht : 0 < t := norm_pos_iff.2 hv
    set A : ℝ := ∑' j, ‖⟪u j, v⟫_ℂ‖ ^ 2
    have key : ∀ a b : ℝ, a * b ≤ (a ^ 2 * t⁻¹ + t * b ^ 2) / 2 := by
      intro a b
      have h : a ^ 2 * t⁻¹ + t * b ^ 2 - 2 * (a * b) = t⁻¹ * (a - t * b) ^ 2 := by
        field_simp; ring
      have : 0 ≤ t⁻¹ * (a - t * b) ^ 2 := by positivity
      linarith
    have h1 : ‖L v‖ ≤ ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ := by
      refine (norm_tsum_le_tsum_norm (hsn' v)).trans_eq ?_
      simp only [norm_smul]
    have hA : HasSum (fun j => (‖⟪u j, v⟫_ℂ‖ ^ 2 * t⁻¹ + t * ‖w j‖ ^ 2) / 2) ((A * t⁻¹ + t * S) / 2) :=
      (((hbes v).hasSum.mul_right t⁻¹).add (hw.hasSum.mul_left t)).div_const 2
    have h2 : ∑' j, ‖⟪u j, v⟫_ℂ‖ * ‖w j‖ ≤ (A * t⁻¹ + t * S) / 2 :=
      hasSum_le (fun j => key _ _) (hsn v).hasSum hA
    have h3 : A * t⁻¹ ≤ t := by
      have : A * t⁻¹ ≤ t ^ 2 * t⁻¹ := mul_le_mul_of_nonneg_right (hbes_le v) (inv_nonneg.2 ht.le)
      have e : t ^ 2 * t⁻¹ = t := by field_simp
      linarith
    have : (A * t⁻¹ + t * S) / 2 ≤ (1 + S) / 2 * t := by nlinarith
    linarith
  let G : H →L[ℂ] K := L.mkContinuous ((1 + S) / 2) hbound
  have hG : ∀ v, G v = ∑' j, ⟪u j, v⟫_ℂ • w j := fun v => rfl
  have hval : ∀ j, G (u j) = w j := by
    intro j
    rw [hG, tsum_eq_single j (fun k hk => by rw [orthonormal_iff_ite.1 hu k j, if_neg hk, zero_smul]),
      orthonormal_iff_ite.1 hu j j, if_pos rfl, one_smul]
  have hvan : ∀ v, (∀ j, inner ℂ (u j) v = 0) → G v = 0 := by
    intro v h
    rw [hG]
    simp [h]
  refine ⟨G, hval, hvan, ?_⟩
  obtain ⟨W, b, hsub, hb⟩ :=
    ((orthonormal_subtype_range hu.linearIndependent.injective).2 hu).exists_hilbertBasis_extension
  rw [GlobalTheory.OpTrace.isHilbertSchmidt_iff b]
  let e : J → W := fun j => ⟨u j, hsub ⟨j, rfl⟩⟩
  have hbe : ∀ j, b (e j) = u j := fun j => congrFun hb (e j)
  have he : Function.Injective e := fun j k hjk =>
    hu.linearIndependent.injective (congrArg Subtype.val hjk)
  refine (he.summable_iff fun i hi => ?_).1 (hw.congr fun j => ?_)
  · have : G (b i) = 0 := hvan _ fun j => by
      rw [← hbe j]
      exact b.orthonormal.2 fun h => hi ⟨j, h⟩
    simp [this]
  · simp only [Function.comp_apply, hbe, hval]

end GlobalTheory
