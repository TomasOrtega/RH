import Mathlib

open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately.

Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_span_image_of_orthogonal_rational_annihilator :
    ∀ (F R : Type) [Field F] [CommRing R] [Algebra F R] (κ : Type) [Fintype κ] (A : Set (κ → F)) (x : κ → R),
    (∀ y : κ → F, (∀ a ∈ A, a ⬝ᵥ y = 0) → x ⬝ᵥ (fun i => algebraMap F R (y i)) = 0) →
    x ∈ Submodule.span R ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) := by
  intro F R _ _ _ κ _ A x hx
  classical
  set W := Submodule.span F A with hW
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  set P : (κ → F) →ₗ[F] (κ → F) := W.subtype ∘ₗ Submodule.linearProjOfIsCompl W C hC with hP
  have hPW : ∀ v, P v ∈ W := fun v => (Submodule.linearProjOfIsCompl W C hC v).2
  have hPa : ∀ a ∈ W, P a = a := fun a ha => by
    have h := Submodule.linearProjOfIsCompl_apply_left hC ⟨a, ha⟩
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val h
  set S := ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) with hS
  have hφ : ∀ v ∈ W, (fun i => algebraMap F R (v i)) ∈ Submodule.span R S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩
    | zero =>
        convert Submodule.zero_mem (Submodule.span R S) using 1
        ext i; simp
    | add u w _ _ hu hw =>
        convert add_mem hu hw using 1
        ext i; simp
    | smul c u _ hu =>
        convert Submodule.smul_mem _ (algebraMap F R c) hu using 1
        ext i; simp
  let e : κ → κ → F := fun j => fun i => if j = i then 1 else 0
  have key : ∀ k, x k = ∑ j, x j * algebraMap F R (P (e j) k) := by
    intro k
    let g : (κ → F) →ₗ[F] F := LinearMap.proj k ∘ₗ (LinearMap.id - P)
    have hy : ∀ a ∈ A, a ⬝ᵥ (fun j => g (e j)) = 0 := by
      intro a ha
      have h1 : g a = 0 := by
        simp [g, hPa a (Submodule.subset_span ha)]
      rw [← h1, LinearMap.pi_apply_eq_sum_univ g a]
      simp [dotProduct, e]
    have h := hx _ hy
    simp [dotProduct, g, e, mul_sub, Finset.sum_sub_distrib] at h
    rw [sub_eq_zero] at h
    simpa [e] using h
  have hx' : x = ∑ j, x j • (fun i => algebraMap F R (P (e j) i)) := by
    funext k
    rw [key k]
    simp [Finset.sum_apply]
  rw [hx']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφ _ (hPW _))

end GlobalTheory
