import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory

/- English proof (translation)
Set `e` to `stdOrthonormalBasis ℂ W`. Use `⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← e.sum_repr' x]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]`. Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`.
-/
theorem exists_endomorphism_representing_sesquilinear_form
    (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : ∃ A : W →ₗ[ℂ] W, ∀ x y, B x y = ⟪x, A y⟫_ℂ := by
  classical
  let e := stdOrthonormalBasis ℂ W
  refine ⟨∑ j, (B (e j)).smulRight (e j), fun x y => ?_⟩
  conv_lhs => rw [← e.sum_repr' x]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, inner_sum, inner_smul_right, smul_eq_mul, inner_conj_symm]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/- English proof (translation)
Introduce `W _ _ _ I π B hiso hirr hinv hherm hpos`. Break down `subsingleton_or_nontrivial W with hW | hW` into its components or cases. Conclude with `⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩`. Take `⟨A, hA⟩` from `exists_endomorphism_representing_sesquilinear_form W B`. Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue A`.

Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Establish `hv0 : v ≠ 0` using `hv.2`. Establish `hAv : A v = μ • v` using `hv.apply_eq_smul`. Establish `hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun i x y => (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y`. Establish `hsurj : ∀ i, Function.Surjective (π i)` using `fun i => (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1 (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective`.

Set `S : Submodule ℂ W` to `{ carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ} add_mem' := fun {a b} ha hb x => by`. Rewrite using `[map_add, inner_add_right, ha x, hb x, mul_add]`. Use the proof step `zero_mem' := fun x => by simp`. Use the proof step `smul_mem' := fun c a ha x => by`. Rewrite using `[map_smul, inner_smul_right, ha x, smul_eq_mul]`.

Use `ring }`. Establish `hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ` using `fun y => Iff.rfl`. Establish `hvS : v ∈ S`. Rewrite using `[hS]`. Introduce `x`.

Rewrite using `[hA, hAv, inner_smul_right]`. Establish `hstab : ∀ i, ∀ y ∈ S, π i y ∈ S`. Introduce `i y hy`. Rewrite `hy`, the goal using `[hS]`. Introduce `x`.

Take `⟨x', rfl⟩` from `hsurj i x`. Rewrite using `[hinv, hinner, hy]`. Establish `htop : S = ⊤`. Break down `hirr S hstab with h | h` into its components or cases. Rewrite `hvS` using `[h]`.

Conclude with `absurd ((Submodule.mem_bot ℂ).1 hvS) hv0`. Conclude with `h`. Establish `hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ` using `fun x y => (hS y).1 (htop ▸ Submodule.mem_top) x`. Establish `hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[hall, inner_self_eq_norm_sq_to_K]`.

Simplify using the standard rewrite rules. Establish `hn : (0 : ℝ) < ‖v‖ ^ 2` using `pow_pos (norm_pos_iff.2 hv0) 2`. Establish `him : μ.im = 0`. Establish `h1` using `congrArg Complex.im (hherm v v)`. Rewrite `h1` using `[hvv]`.

Simplify using `only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add] at h1`. Establish `h2 : μ.im * ‖v‖ ^ 2 = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 h2).resolve_right hn.ne'`. Establish `hre : 0 < μ.re`. Establish `h1` using `hpos v hv0`.

Rewrite `h1` using `[hvv]`. Simplify using `only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1`. Conclude with `(mul_pos_iff_of_pos_right hn).1 h1`. Use `⟨μ.re, hre, fun _ x y => ?_⟩` and prove the remaining obligations. Establish `: (μ.re : ℂ) = μ` using `Complex.ext rfl (by simp [him])`.

Rewrite using `[this, hall]`.
-/
theorem invariant_posDef_form_eq_smul_inner_of_irreducible :
    ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (I : Type) (π : I → (W →L[ℂ] W)) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ i v, ‖π i v‖ = ‖v‖) → (∀ S : Submodule ℂ W, (∀ i, ∀ v ∈ S, π i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i x y, B (π i x) (π i y) = B x y) → (∀ x y, B y x = star (B x y)) → (∀ x, x ≠ 0 → 0 < (B x x).re) → ∃ c : ℝ, 0 < c ∧ (Nontrivial W → ∀ x y, B x y = c * ⟪x, y⟫_ℂ) := by
  intro W _ _ _ I π B hiso hirr hinv hherm hpos
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact ⟨1, one_pos, fun h => absurd h (not_nontrivial W)⟩
  obtain ⟨A, hA⟩ := exists_endomorphism_representing_sesquilinear_form W B
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hAv : A v = μ • v := hv.apply_eq_smul
  have hinner : ∀ i x y, ⟪π i x, π i y⟫_ℂ = ⟪x, y⟫_ℂ := fun i x y =>
    (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y
  have hsurj : ∀ i, Function.Surjective (π i) := fun i =>
    (LinearMap.injective_iff_surjective (f := (π i : W →ₗ[ℂ] W))).1
      (⟨(π i : W →ₗ[ℂ] W), hiso i⟩ : W →ₗᵢ[ℂ] W).injective
  let S : Submodule ℂ W :=
    { carrier := {y | ∀ x, B x y = μ * ⟪x, y⟫_ℂ}
      add_mem' := fun {a b} ha hb x => by
        rw [map_add, inner_add_right, ha x, hb x, mul_add]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by
        rw [map_smul, inner_smul_right, ha x, smul_eq_mul]; ring }
  have hS : ∀ y, y ∈ S ↔ ∀ x, B x y = μ * ⟪x, y⟫_ℂ := fun y => Iff.rfl
  have hvS : v ∈ S := by
    rw [hS]; intro x
    rw [hA, hAv, inner_smul_right]
  have hstab : ∀ i, ∀ y ∈ S, π i y ∈ S := by
    intro i y hy
    rw [hS] at hy ⊢
    intro x
    obtain ⟨x', rfl⟩ := hsurj i x
    rw [hinv, hinner, hy]
  have htop : S = ⊤ := by
    rcases hirr S hstab with h | h
    · rw [h] at hvS
      exact absurd ((Submodule.mem_bot ℂ).1 hvS) hv0
    · exact h
  have hall : ∀ x y, B x y = μ * ⟪x, y⟫_ℂ := fun x y =>
    (hS y).1 (htop ▸ Submodule.mem_top) x
  have hvv : B v v = μ * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [hall, inner_self_eq_norm_sq_to_K]; simp
  have hn : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv0) 2
  have him : μ.im = 0 := by
    have h1 := congrArg Complex.im (hherm v v)
    rw [hvv] at h1
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, mul_zero, zero_add] at h1
    have h2 : μ.im * ‖v‖ ^ 2 = 0 := by linarith
    exact (mul_eq_zero.1 h2).resolve_right hn.ne'
  have hre : 0 < μ.re := by
    have h1 := hpos v hv0
    rw [hvv] at h1
    simp only [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, mul_zero, sub_zero] at h1
    exact (mul_pos_iff_of_pos_right hn).1 h1
  refine ⟨μ.re, hre, fun _ x y => ?_⟩
  have : (μ.re : ℂ) = μ := Complex.ext rfl (by simp [him])
  rw [this, hall]

end GlobalTheory
