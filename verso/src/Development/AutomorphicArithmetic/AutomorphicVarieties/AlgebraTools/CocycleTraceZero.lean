import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DerInner

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Introduce `K G _ _ σ _ _ d _ _ _ r φ hspan hφ htr`. Set `m : G → ∀ s, Matrix (d s) (d s) K` to `fun g => φ g * r g`. Establish `hinv : ∀ g, r g⁻¹ * r g = 1` using `fun g => by rw [← map_mul, inv_mul_cancel, map_one]`. Establish `hinv' : ∀ g, r g * r g⁻¹ = 1` using `fun g => by rw [← map_mul, mul_inv_cancel, map_one]`. Establish `hm : ∀ g h, m (g * h) = m g * r h + r g * m h`.

Introduce `g h`. Simplify using `only [m, hφ, map_mul, add_mul, mul_assoc]`. Rewrite using `[← mul_assoc (r g⁻¹), hinv, one_mul]`. Set `T : (∀ s, Matrix (d s) (d s) K) →ₗ[K] K` to `∑ s, (Matrix.traceLinearMap (d s) K K) ∘ₗ LinearMap.proj s`. Establish `hT : ∀ x, T x = ∑ s, (x s).trace`.

Introduce `x`. Simplify using `[T, LinearMap.sum_apply]`. Establish `hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0`. Introduce `x hx`. Use function extensionality and compare the values at `s`.

Rewrite using `[Matrix.ext_iff_trace_mul_right]`. Introduce `y`. Use `hx (Pi.single s y)` as an intermediate fact. Rewrite `this` using `[hT, Finset.sum_eq_single s]`. Simplify using `using this`.

Introduce `t _ ht`. Simplify using `[Pi.single_eq_of_ne ht]`. Simplify using the standard rewrite rules. Establish `hkey : ∀ g h, T (m g * r h) = - T (r g * m h)`. Introduce `g h`.

Establish `: T (m (g * h)) = 0` using `by rw [hT]; exact htr _`. Rewrite `this` using `[hm, map_add]`. Conclude with `eq_neg_of_add_eq_zero_left this`. Set `R` to `Finsupp.linearCombination K (fun g => r g)`. Set `M` to `Finsupp.linearCombination K m`.

Establish `hR : Function.Surjective R`. Rewrite using `[← LinearMap.range_eq_top, Finsupp.range_linearCombination]`. Conclude with `hspan`. Establish `hkey2 : ∀ f h, T (M f * r h) = - T (R f * m h)`. Introduce `f h`.

Proceed by induction on `f using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f₁ f₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `single g a`.

Simplify using `only [R, M, Finsupp.linearCombination_single, smul_mul_assoc, map_smul, hkey, smul_neg]`. Establish `hle : LinearMap.ker R ≤ LinearMap.ker M`. Introduce `f hf`. Rewrite `hf`, the goal using `[LinearMap.mem_ker]`. Apply `hnd` to reduce the goal to its premises.

Introduce `y`. Establish `hy : y ∈ Submodule.span K (Set.range r)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨h, rfl⟩` from `hx`.

Rewrite using `[hkey2, hf]`. Simplify using the standard rewrite rules. Consider the case `zero => simp`. Consider the case `add x y _ _ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_zero]`. Consider the case `smul a x _ h₁ => rw [mul_smul_comm, map_smul, h₁, smul_zero]`.

Set `D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] (∀ s, Matrix (d s) (d s) K)` to `(LinearMap.ker R).liftQ M hle ∘ₗ (R.quotKerEquivOfSurjective hR).symm.toLinearMap`. Establish `hDR : ∀ f, D (R f) = M f`. Introduce `f`. Establish `: (R.quotKerEquivOfSurjective hR).symm (R f) = Submodule.Quotient.mk f`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `[D, this]`. Establish `hDr : ∀ g, D (r g) = m g`. Introduce `g`. Simplify `hDR (Finsupp.single g 1)` using `[R, M]`.

Establish `hder : ∀ x y, D (x * y) = D x * y + x * D y`. Introduce `x y`. Establish `hx : x ∈ Submodule.span K (Set.range r)` using `hspan ▸ Submodule.mem_top`. Establish `hy : y ∈ Submodule.span K (Set.range r)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hx, hy using Submodule.span_induction₂ with`.

Consider the case `mem_mem x y hx hy`. Take `⟨g, rfl⟩` from `hx`. Take `⟨h, rfl⟩` from `hy`. Rewrite using `[← map_mul, hDr, hDr, hDr, hm]`. Consider the case `zero_left => simp`.

Consider the case `zero_right => simp`. Consider the case `add_left x y z _ _ _ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]`. Normalize the expressions using the abelian group laws. Consider the case `add_right x y z _ _ _ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]`. Normalize the expressions using the abelian group laws.

Consider the case `smul_left a x y _ _ h₁ => simp only [smul_mul_assoc, map_smul, h₁, smul_add]`. Consider the case `smul_right a x y _ _ h₁ => simp only [mul_smul_comm, map_smul, h₁, smul_add]`. Take `⟨Y, hY⟩` from `UpperTheory.V.AlgebraTools.der_inner d (AlgHom.id K _) D hder`. Use `⟨Y, fun g => ?_⟩` and prove the remaining obligations. Establish `h1 : φ g = m g * r g⁻¹` using `by simp only [m, mul_assoc, hinv', mul_one]`.

Rewrite using `[h1, ← hDr, hY]`. Simplify using `only [AlgHom.id_apply, sub_mul]`. Rewrite using `[mul_assoc Y, hinv', mul_one]`.
-/
theorem UpperTheory.V.AlgebraTools.cocycle_trace_zero :
    ∀ {K G : Type} [CommRing K] [Group G] {σ : Type} [Fintype σ] [DecidableEq σ] (d : σ → Type) [∀ s, Fintype (d s)] [∀ s, DecidableEq (d s)] [∀ s, Nonempty (d s)] (r : G →* (∀ s, Matrix (d s) (d s) K)) (φ : G → ∀ s, Matrix (d s) (d s) K), Submodule.span K (Set.range r) = ⊤ → (∀ g h, φ (g * h) = φ g + r g * φ h * r g⁻¹) → (∀ g, ∑ s, ((φ g * r g) s).trace = 0) → ∃ Y, ∀ g, φ g = Y - r g * Y * r g⁻¹ := by
  intro K G _ _ σ _ _ d _ _ _ r φ hspan hφ htr
  classical
  let m : G → ∀ s, Matrix (d s) (d s) K := fun g => φ g * r g
  have hinv : ∀ g, r g⁻¹ * r g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, r g * r g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hm : ∀ g h, m (g * h) = m g * r h + r g * m h := by
    intro g h
    simp only [m, hφ, map_mul, add_mul, mul_assoc]
    rw [← mul_assoc (r g⁻¹), hinv, one_mul]
  let T : (∀ s, Matrix (d s) (d s) K) →ₗ[K] K :=
    ∑ s, (Matrix.traceLinearMap (d s) K K) ∘ₗ LinearMap.proj s
  have hT : ∀ x, T x = ∑ s, (x s).trace := by
    intro x
    simp [T, LinearMap.sum_apply]
  have hnd : ∀ x, (∀ y, T (x * y) = 0) → x = 0 := by
    intro x hx
    funext s
    rw [Matrix.ext_iff_trace_mul_right]
    intro y
    have := hx (Pi.single s y)
    rw [hT, Finset.sum_eq_single s] at this
    · simpa using this
    · intro t _ ht
      simp [Pi.single_eq_of_ne ht]
    · simp
  have hkey : ∀ g h, T (m g * r h) = - T (r g * m h) := by
    intro g h
    have : T (m (g * h)) = 0 := by rw [hT]; exact htr _
    rw [hm, map_add] at this
    exact eq_neg_of_add_eq_zero_left this
  let R := Finsupp.linearCombination K (fun g => r g)
  let M := Finsupp.linearCombination K m
  have hR : Function.Surjective R := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hkey2 : ∀ f h, T (M f * r h) = - T (R f * m h) := by
    intro f h
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂]; ring
    | single g a =>
      simp only [R, M, Finsupp.linearCombination_single, smul_mul_assoc, map_smul, hkey, smul_neg]
  have hle : LinearMap.ker R ≤ LinearMap.ker M := by
    intro f hf
    rw [LinearMap.mem_ker] at hf ⊢
    apply hnd
    intro y
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hkey2, hf]; simp
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, add_zero]
    | smul a x _ h₁ => rw [mul_smul_comm, map_smul, h₁, smul_zero]
  let D : (∀ s, Matrix (d s) (d s) K) →ₗ[K] (∀ s, Matrix (d s) (d s) K) :=
    (LinearMap.ker R).liftQ M hle ∘ₗ (R.quotKerEquivOfSurjective hR).symm.toLinearMap
  have hDR : ∀ f, D (R f) = M f := by
    intro f
    have : (R.quotKerEquivOfSurjective hR).symm (R f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp [D, this]
  have hDr : ∀ g, D (r g) = m g := by
    intro g
    simpa [R, M] using hDR (Finsupp.single g 1)
  have hder : ∀ x y, D (x * y) = D x * y + x * D y := by
    intro x y
    have hx : x ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    have hy : y ∈ Submodule.span K (Set.range r) := hspan ▸ Submodule.mem_top
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      rw [← map_mul, hDr, hDr, hDr, hm]
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; abel
    | add_right x y z _ _ _ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; abel
    | smul_left a x y _ _ h₁ => simp only [smul_mul_assoc, map_smul, h₁, smul_add]
    | smul_right a x y _ _ h₁ => simp only [mul_smul_comm, map_smul, h₁, smul_add]
  obtain ⟨Y, hY⟩ := UpperTheory.V.AlgebraTools.der_inner d (AlgHom.id K _) D hder
  refine ⟨Y, fun g => ?_⟩
  have h1 : φ g = m g * r g⁻¹ := by simp only [m, mul_assoc, hinv', mul_one]
  rw [h1, ← hDr, hY]
  simp only [AlgHom.id_apply, sub_mul]
  rw [mul_assoc Y, hinv', mul_one]
