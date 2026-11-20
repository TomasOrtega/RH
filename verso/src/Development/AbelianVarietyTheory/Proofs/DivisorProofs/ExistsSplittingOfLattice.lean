import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

namespace GlobalTheory.BplusDescent

/- English proof (translation)
Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R L`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Set `e : Fin h → L` to `fun i => ⟨c • Pi.single i 1, hL _⟩`. Use `⟨n, fun k => (π (Pi.single k 1) : L), fun k i => f (s (e i) k) / f c, fun k => (π (Pi.single k 1)).2, fun i i' => ?_, fun v hv k => ⟨s ⟨v, hv⟩ k, ?_⟩⟩` and prove the remaining obligations. Establish `h1 : π (s (e i')) = e i'` using `LinearMap.congr_fun hs (e i')`.

Establish `h2 : π (s (e i')) = ∑ k, s (e i') k • π (Pi.single k 1)` using `by conv_lhs => rw [pi_eq_sum_univ' (s (e i'))]`. Simplify using `only [map_sum, map_smul]`. Establish `h3 : ∑ k, (π (Pi.single k 1) : Fin h → R) i * s (e i') k = c * (if i = i' then 1 else 0)`. Use `congrArg (fun x : L => (x : Fin h → R) i) (h2.symm.trans h1)` as an intermediate fact. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_apply] at this`.

Rewrite using `[← this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `h4` using `congrArg f h3`. Simplify using `only [map_sum, map_mul, apply_ite f, map_one, map_zero] at h4`. Simplify using `only [← mul_div_assoc]`.

Rewrite using `[← Finset.sum_div, h4, mul_div_cancel_left₀ _ hc]`. Establish `h1 : c • (⟨v, hv⟩ : L) = ∑ i, v i • e i`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `[e, Pi.single_apply, mul_comm]`.

Establish `h2 : c * s ⟨v, hv⟩ k = ∑ i, s (e i) k * v i`. Use `congrArg (fun x : L => s x k) h1` as an intermediate fact. Simplify using `only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.

Establish `h4` using `congrArg f h2`. Simplify using `only [map_sum, map_mul] at h4`. Simplify using `only [div_mul_eq_mul_div]`. Rewrite using `[← Finset.sum_div, ← h4, mul_div_cancel_left₀ _ hc]`.
-/
theorem exists_split_of_finite_projective {R K : Type*} [CommRing R] [Field K] (f : R →+* K) (h : ℕ)
    (L : Submodule R (Fin h → R)) (c : R) (hc : f c ≠ 0) [Module.Finite R L] [Module.Projective R L]
    (hL : ∀ x : Fin h → R, c • x ∈ L) :
    ∃ (n : ℕ) (g : Fin n → Fin h → R) (S : Fin n → Fin h → K), (∀ k, g k ∈ L) ∧
      (∀ i i' : Fin h, ∑ k, f (g k i) * S k i' = if i = i' then 1 else 0) ∧
      ∀ v ∈ L, ∀ k, ∃ r : R, f r = ∑ i, S k i * f (v i) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let e : Fin h → L := fun i => ⟨c • Pi.single i 1, hL _⟩
  refine ⟨n, fun k => (π (Pi.single k 1) : L), fun k i => f (s (e i) k) / f c,
    fun k => (π (Pi.single k 1)).2, fun i i' => ?_, fun v hv k => ⟨s ⟨v, hv⟩ k, ?_⟩⟩
  · have h1 : π (s (e i')) = e i' := LinearMap.congr_fun hs (e i')
    have h2 : π (s (e i')) = ∑ k, s (e i') k • π (Pi.single k 1) := by
      conv_lhs => rw [pi_eq_sum_univ' (s (e i'))]
      simp only [map_sum, map_smul]
    have h3 : ∑ k, (π (Pi.single k 1) : Fin h → R) i * s (e i') k = c * (if i = i' then 1 else 0) := by
      have := congrArg (fun x : L => (x : Fin h → R) i) (h2.symm.trans h1)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e,
        Pi.single_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have h4 := congrArg f h3
    simp only [map_sum, map_mul, apply_ite f, map_one, map_zero] at h4
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div, h4, mul_div_cancel_left₀ _ hc]
  · have h1 : c • (⟨v, hv⟩ : L) = ∑ i, v i • e i := by
      apply Subtype.ext
      ext j
      simp [e, Pi.single_apply, mul_comm]
    have h2 : c * s ⟨v, hv⟩ k = ∑ i, s (e i) k * v i := by
      have := congrArg (fun x : L => s x k) h1
      simp only [map_smul, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have h4 := congrArg f h2
    simp only [map_sum, map_mul] at h4
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← h4, mul_div_cancel_left₀ _ hc]

/- English proof (translation)
Introduce `X _ U h L c hc hf hp hL`. Conclude with `exists_split_of_finite_projective (SubringClass.subtype _ : U.Bp →+* Kbar X) h L c hc hL`.
-/
theorem exists_splits : ∀ (X : Scheme.{0}) [IsIntegral X] (U : AffOp X) (h : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (c : U.Bp), (c : Kbar X) ≠ 0 → Module.Finite U.Bp L → Module.Projective U.Bp L → (∀ x : Fin h → U.Bp, c • x ∈ L) → ∃ (n : ℕ) (g : Fin n → Fin h → U.Bp) (S : Fin n → Fin h → Kbar X), Splits U L g S := by
  intro X _ U h L c hc hf hp hL
  exact exists_split_of_finite_projective (SubringClass.subtype _ : U.Bp →+* Kbar X) h L c hc hL

end GlobalTheory.BplusDescent
