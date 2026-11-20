import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.Projection
import GroundTheory.AutomorphicForms.HarishChandraCentre.Fischer

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

/- English proof (translation)
Proceed by induction on `u using U.induction with`. Consider the case `halg r`. Use `⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩` and prove the remaining obligations. Simplify using `only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]`. Consider the case `hι X`.

Use `⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩` and prove the remaining obligations. Rewrite using `[ι_eq_sum_e]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left, fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]`.

Consider the case `hmul a b ha hb`. Take `⟨a', ha'⟩` from `ha`. Take `⟨b', hb'⟩` from `hb`. Use `⟨b' * a', fun f g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]`.

Consider the case `hadd a b ha hb`. Take `⟨a', ha'⟩` from `ha`. Take `⟨b', hb'⟩` from `hb`. Use `⟨a' + b', fun f g => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, LinearMap.add_apply, fischer_add_left, ha', hb', map_add, LinearMap.add_apply, fischer_add_right]`.
-/
theorem exists_adjoint (u : U n) :
    ∃ u' : U n, ∀ f g : Poly n, fischer (rho 0 u f) g = fischer f (rho 0 u' g) := by
  induction u using U.induction with
  | halg r =>
    refine ⟨algebraMap ℂ (U n) (star r), fun f g => ?_⟩
    simp only [AlgHom.commutes, Module.algebraMap_end_apply, fischer_smul_left, fischer_smul_right]
  | hι X =>
    refine ⟨∑ a : Fin n × Fin n, star (X a.1 a.2) • e (a.2, a.1), fun f g => ?_⟩
    rw [ι_eq_sum_e]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fischer_sum_left,
      fischer_sum_right, fischer_smul_left, fischer_smul_right, star_star]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [show e a = e (a.1, a.2) from rfl, rho_zero_e, rho_zero_e, fischer_rowOp]
  | hmul a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨b' * a', fun f g => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha', hb', map_mul, Module.End.mul_apply]
  | hadd a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    refine ⟨a' + b', fun f g => ?_⟩
    rw [map_add, LinearMap.add_apply, fischer_add_left, ha', hb', map_add, LinearMap.add_apply,
      fischer_add_right]

/- English proof (translation)
Take `⟨z', hz'⟩` from `exists_adjoint z`. Establish `hc : ∀ u : U n, u * z = z * u` using `fun u => (Subalgebra.mem_center_iff.1 hz) u`. Apply `eq_zero_of_rho_zero_eq_zero` to reduce the goal to its premises. Use `eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_` and prove the remaining obligations. Introduce `i j`.

Rewrite using `[← rho_zero_e, ← map_mul, ← map_mul, hc]`. Rewrite using `[← map_mul, ← map_mul, hc]`. Introduce `v μ hup hwt`. Use `rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v) (fun a ha => by` as an intermediate fact. Rewrite using `[show e a = e (a.1, a.2) from rfl, rho_zero_e]`.

Conclude with `hup a.1 a.2 ha)`. Use the proof step `(fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)`. Use the proof step `(fun k => hc (e (k, k)))`. Rewrite using `[this, h, map_zero, zero_smul]`.
-/
theorem eq_zero_of_mem_center_of_hcProjLin_eq_zero {z : U n}
    (hz : z ∈ Subalgebra.center ℂ (U n)) (h : hcProjLin z = 0) : z = 0 := by
  obtain ⟨z', hz'⟩ := exists_adjoint z
  have hc : ∀ u : U n, u * z = z * u := fun u => (Subalgebra.mem_center_iff.1 hz) u
  apply eq_zero_of_rho_zero_eq_zero
  refine eq_zero_of_forall_highestWeight (rho 0 z) (rho 0 z') ?_ hz' ?_ ?_
  · intro i j
    rw [← rho_zero_e, ← map_mul, ← map_mul, hc]
  · rw [← map_mul, ← map_mul, hc]
  · intro v μ hup hwt
    have := rep_apply_of_highestWeight (rho 0) (fun i => (μ i : ℂ)) (v := v)
      (fun a ha => by
        rw [show e a = e (a.1, a.2) from rfl, rho_zero_e]
        exact hup a.1 a.2 ha)
      (fun k => by rw [rho_zero_e]; exact rowOp_self_of_wtProj μ v k hwt)
      (fun k => hc (e (k, k)))
    rw [this, h, map_zero, zero_smul]

/- English proof (translation)
Introduce `z hz z' hz' h`. Use `eq_zero_of_mem_center_of_hcProjLin_eq_zero (Subalgebra.sub_mem _ hz hz') (by rw [map_sub, h, sub_self])` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.
-/
theorem hcProjLin_injOn_center :
    Set.InjOn (hcProjLin (n := n)) (Subalgebra.center ℂ (U n) : Set (U n)) := by
  intro z hz z' hz' h
  have := eq_zero_of_mem_center_of_hcProjLin_eq_zero (Subalgebra.sub_mem _ hz hz')
    (by rw [map_sub, h, sub_self])
  exact sub_eq_zero.1 this

/- English proof (translation)
Use `MvPolynomial.funext fun lam => ?_` and prove the remaining obligations. Rewrite using `[eval_translate, eval_translate, neg_add_cancel_right]`.
-/
theorem translate_neg_translate (c : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    translate (-c) (translate c p) = p := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_translate, eval_translate, neg_add_cancel_right]

/- English proof (translation)
The claim follows from `Function.LeftInverse.injective (translate_neg_translate c)`.
-/
theorem translate_injective (c : Fin n → ℂ) : Function.Injective (translate (n := n) c) :=
  Function.LeftInverse.injective (translate_neg_translate c)

/- English proof (translation)
Introduce `z z' h`. Rewrite `h` using `[harishChandraHom_apply, harishChandraHom_apply]`. Conclude with `Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))`.
-/
theorem harishChandraHom_injective : Function.Injective (harishChandraHom (n := n)) := by
  intro z z' h
  rw [harishChandraHom_apply, harishChandraHom_apply] at h
  exact Subtype.ext (hcProjLin_injOn_center z.2 z'.2 (translate_injective _ h))

end GroundTheory.Automorphic.HarishChandra
