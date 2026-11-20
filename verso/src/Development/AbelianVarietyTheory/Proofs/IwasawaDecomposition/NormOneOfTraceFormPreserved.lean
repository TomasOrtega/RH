import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Formalism.LocalToGlobal.ProjectiveLattices.FibreUniformisationLevelTwo
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ r X hr ζ h`. Assume the negation of the conclusion as `hc`. Establish `hc' : ζ * cc ζ - 1 ≠ 0` using `sub_ne_zero.mpr hc`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu, v, hv, huv⟩ : ∃ u ∈ X.Λ, ∃ v ∈ X.Λ, herm X.Gm u v ≠ 0 := by`. Assume the negation of the conclusion as `hall`.

Use `push_neg at hall`. Set `L : (Fin r → E) → (Fin r → E) →ₗ[E] E` to `fun y => { toFun := fun x => herm X.Gm x y map_add' := by`. Introduce `x x'`. Simplify using `only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `a x`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }`. Set `M : (Fin r → E) → (Fin r → E) →ₗ[E] E` to `fun x => { toFun := fun y => cc (herm X.Gm x y) map_add' := by`. Introduce `y y'`. Simplify using `only [herm, cc, Pi.add_apply, map_add, map_sum, map_mul, mul_add, Finset.sum_add_distrib]`.

Use the proof step `map_smul' := by`. Introduce `a y`. Simplify using `only [herm, cc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_sum, map_mul, IsCMField.complexConj_apply_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }` and prove the remaining obligations. Establish `h1 : ∀ v ∈ X.Λ, ∀ x, herm X.Gm x v = 0`.

Introduce `v hv x`. Establish `hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ LinearMap.ker (L v)`. Rewrite using `[Submodule.span_le]`. Introduce `w hw`. Conclude with `hall w hw v hv`.

Establish `: x ∈ LinearMap.ker (L v)` using `hle (X.Λ_span ▸ Submodule.mem_top)`. Conclude with `this`. Establish `h2 : ∀ x y, herm X.Gm x y = 0`. Introduce `x y`. Establish `hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ LinearMap.ker (M x)`.

Rewrite using `[Submodule.span_le]`. Introduce `w hw`. Use `show cc (herm X.Gm x w) = 0`. Rewrite using `[h1 w hw x]`. Simplify using `[cc]`.

Establish `: cc (herm X.Gm x y) = 0` using `hle (X.Λ_span ▸ Submodule.mem_top)`. Simplify `this` using `[cc]`. Establish `hG : X.Gm = 0`. Use extensionality with `i j`. Use `h2 (Pi.single i 1) (Pi.single j 1)` as an intermediate fact.

Simplify `this` using `[herm, cc, Pi.single_apply]`. Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Conclude with `X.Gm_det (by rw [hG]; exact Matrix.det_zero)`. Use `set β : E := -X.ξ0 * (ζ * cc ζ - 1) * herm X.Gm u v with hβ`. Establish `hβ0 : β ≠ 0` using `mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr X.ξ0_ne) hc') huv`.

Establish `key : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * β) = 0`. Introduce `a`. Establish `hs : herm X.Gm (a • u) v = (a : E) * herm X.Gm u v`. Simplify using `only [herm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Simplify using `only [mul_assoc]`. Use `h (a • u) (X.Λ.smul_mem a hu) v hv` as an intermediate fact. Rewrite `this` using `[hs]`. Rewrite using `[show (a : E) * β = -X.ξ0 * (ζ * cc ζ * ((a : E) * herm X.Gm u v)) - -X.ξ0 * ((a : E) * herm X.Gm u v) by`.

Rewrite using `[hβ]`. Use the proof step `ring, map_sub, this, sub_self]`. Establish `halg : IsAlgebraic ℤ β⁻¹` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)`. Take `⟨y, hy0, hyint⟩` from `halg.exists_integral_multiple`. Use `key ⟨y • β⁻¹, hyint⟩` as an intermediate fact.

Express the relevant statement in the definitionally equal form `Algebra.trace ℚ E ((y • β⁻¹) * β) = 0 at this`. Rewrite `this` using `[zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hβ0, mul_one]`. Establish `h3 : ((y : E)) = algebraMap ℚ E (y : ℚ)` using `by simp`. Rewrite `this` using `[h3, Algebra.trace_algebraMap, nsmul_eq_mul]`. Establish `hpos : (0 : ℚ) < Module.finrank ℚ E` using `by exact_mod_cast Module.finrank_pos`.

Break down `mul_eq_zero.mp this with h4 | h4` into its components or cases. Conclude with `absurd h4 hpos.ne'`. Conclude with `hy0 (by exact_mod_cast h4)`.
-/
theorem trace_form_scalar_norm_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (hr : 0 < r) (ζ : E), (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, Algebra.trace ℚ E (-X.ξ0 * (ζ * cc ζ * herm X.Gm u v)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm u v)) → ζ * cc ζ = 1 := by
  intro E _ _ _ r X hr ζ h
  by_contra hc
  have hc' : ζ * cc ζ - 1 ≠ 0 := sub_ne_zero.mpr hc
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ X.Λ, ∃ v ∈ X.Λ, herm X.Gm u v ≠ 0 := by
    by_contra hall
    push_neg at hall
    let L : (Fin r → E) → (Fin r → E) →ₗ[E] E := fun y =>
      { toFun := fun x => herm X.Gm x y
        map_add' := by
          intro x x'
          simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        map_smul' := by
          intro a x
          simp only [herm, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
    let M : (Fin r → E) → (Fin r → E) →ₗ[E] E := fun x =>
      { toFun := fun y => cc (herm X.Gm x y)
        map_add' := by
          intro y y'
          simp only [herm, cc, Pi.add_apply, map_add, map_sum, map_mul, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro a y
          simp only [herm, cc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, map_sum, map_mul,
            IsCMField.complexConj_apply_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
    have h1 : ∀ v ∈ X.Λ, ∀ x, herm X.Gm x v = 0 := by
      intro v hv x
      have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ LinearMap.ker (L v) := by
        rw [Submodule.span_le]
        intro w hw
        exact hall w hw v hv
      have : x ∈ LinearMap.ker (L v) := hle (X.Λ_span ▸ Submodule.mem_top)
      exact this
    have h2 : ∀ x y, herm X.Gm x y = 0 := by
      intro x y
      have hle : Submodule.span E (X.Λ : Set (Fin r → E)) ≤ LinearMap.ker (M x) := by
        rw [Submodule.span_le]
        intro w hw
        show cc (herm X.Gm x w) = 0
        rw [h1 w hw x]; simp [cc]
      have : cc (herm X.Gm x y) = 0 := hle (X.Λ_span ▸ Submodule.mem_top)
      simpa [cc] using this
    have hG : X.Gm = 0 := by
      ext i j
      have := h2 (Pi.single i 1) (Pi.single j 1)
      simpa [herm, cc, Pi.single_apply] using this
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    exact X.Gm_det (by rw [hG]; exact Matrix.det_zero)
  set β : E := -X.ξ0 * (ζ * cc ζ - 1) * herm X.Gm u v with hβ
  have hβ0 : β ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr X.ξ0_ne) hc') huv
  have key : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * β) = 0 := by
    intro a
    have hs : herm X.Gm (a • u) v = (a : E) * herm X.Gm u v := by
      simp only [herm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, Algebra.smul_def]
      simp only [mul_assoc]
    have := h (a • u) (X.Λ.smul_mem a hu) v hv
    rw [hs] at this
    rw [show (a : E) * β = -X.ξ0 * (ζ * cc ζ * ((a : E) * herm X.Gm u v)) - -X.ξ0 * ((a : E) * herm X.Gm u v) by
      rw [hβ]; ring, map_sub, this, sub_self]
  have halg : IsAlgebraic ℤ β⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have := key ⟨y • β⁻¹, hyint⟩
  change Algebra.trace ℚ E ((y • β⁻¹) * β) = 0 at this
  rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hβ0, mul_one] at this
  have h3 : ((y : E)) = algebraMap ℚ E (y : ℚ) := by simp
  rw [h3, Algebra.trace_algebraMap, nsmul_eq_mul] at this
  have hpos : (0 : ℚ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  rcases mul_eq_zero.mp this with h4 | h4
  · exact absurd h4 hpos.ne'
  · exact hy0 (by exact_mod_cast h4)

end GlobalTheory
