import Mathlib

open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `F R _ _ _ κ _ A x hx`. Use `set W := Submodule.span F A with hW`. Take `⟨C, hC⟩` from `Submodule.exists_isCompl W`. Use `set P : (κ → F) →ₗ[F] (κ → F) := W.subtype ∘ₗ Submodule.linearProjOfIsCompl W C hC with hP`. Establish `hPW : ∀ v, P v ∈ W` using `fun v => (Submodule.linearProjOfIsCompl W C hC v).2`.

Establish `hPa : ∀ a ∈ W, P a = a` using `fun a ha => by`. Establish `h` using `Submodule.linearProjOfIsCompl_apply_left hC ⟨a, ha⟩`. Simplify using `only [P, LinearMap.comp_apply, Submodule.subtype_apply]`. Conclude with `congrArg Subtype.val h`. Use `set S := ((fun a : κ → F => fun i => algebraMap F R (a i)) '' A) with hS`.

Establish `hφ : ∀ v ∈ W, (fun i => algebraMap F R (v i)) ∈ Submodule.span R S`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem a ha => exact Submodule.subset_span ⟨a, ha, rfl⟩`. Consider the case `zero`.

Use `Submodule.zero_mem (Submodule.span R S) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`. Simplify using the standard rewrite rules. Consider the case `add u w _ _ hu hw`. Use `add_mem hu hw using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i`. Simplify using the standard rewrite rules. Consider the case `smul c u _ hu`. Use `Submodule.smul_mem _ (algebraMap F R c) hu using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i`.

Simplify using the standard rewrite rules. Set `e : κ → κ → F` to `fun j => fun i => if j = i then 1 else 0`. Establish `key : ∀ k, x k = ∑ j, x j * algebraMap F R (P (e j) k)`. Introduce `k`. Set `g : (κ → F) →ₗ[F] F` to `LinearMap.proj k ∘ₗ (LinearMap.id - P)`.

Establish `hy : ∀ a ∈ A, a ⬝ᵥ (fun j => g (e j)) = 0`. Introduce `a ha`. Establish `h1 : g a = 0`. Simplify using `[g, hPa a (Submodule.subset_span ha)]`. Rewrite using `[← h1, LinearMap.pi_apply_eq_sum_univ g a]`.

Simplify using `[dotProduct, e]`. Establish `h` using `hx _ hy`. Simplify using `[dotProduct, g, e, mul_sub, Finset.sum_sub_distrib] at h`. Rewrite `h` using `[sub_eq_zero]`. Simplify `h` using `[e]`.

Establish `hx' : x = ∑ j, x j • (fun i => algebraMap F R (P (e j) i))`. Use function extensionality and compare the values at `k`. Rewrite using `[key k]`. Simplify using `[Finset.sum_apply]`. Rewrite using `[hx']`.

Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφ _ (hPW _))`.
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
