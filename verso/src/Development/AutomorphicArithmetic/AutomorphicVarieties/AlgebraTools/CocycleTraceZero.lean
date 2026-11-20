import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DerInner

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Treat this case separately. Treat this case separately. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

Normalize the expressions using the abelian group laws. Treat this case separately. Normalize the expressions using the abelian group laws. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
