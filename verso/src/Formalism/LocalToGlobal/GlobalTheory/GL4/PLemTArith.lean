import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree

noncomputable section

open NumberField FractionalIdeal
open scoped nonZeroDivisors

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def starO (w : 𝓞 E) : 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E) w

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem starO_coe (w : 𝓞 E) : ((starO w : 𝓞 E) : E) = star (w : E) := rfl

/- English proof (translation)
Apply `(algebraMap ℚ ℂ).injective` to reduce the goal to its premises. Rewrite using `[trace_eq_sum_embeddings (E := ℂ), trace_eq_sum_embeddings (E := ℂ)]`. Establish `h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ (star a) = star (∑ σ : E →ₐ[ℚ] ℂ, σ a)`. Rewrite using `[star_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ ↦ hσ σ.toRingHom a`.

Rewrite using `[h1, ← trace_eq_sum_embeddings (E := ℂ)]`. Simplify using the standard rewrite rules.
-/
theorem trace_star (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a)) (a : E) :
    Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a := by
  apply (algebraMap ℚ ℂ).injective
  rw [trace_eq_sum_embeddings (E := ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have h1 : ∑ σ : E →ₐ[ℚ] ℂ, σ (star a) = star (∑ σ : E →ₐ[ℚ] ℂ, σ a) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ hσ σ.toRingHom a
  rw [h1, ← trace_eq_sum_embeddings (E := ℂ)]
  simp

/- English proof (translation)
Rewrite using `[mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `h w`. Conclude with `h _ ((mem_one_iff _).2 ⟨w, rfl⟩)`. Introduce `h y hy`.

Take `⟨w, rfl⟩` from `(mem_one_iff _).1 hy`. Conclude with `h w`.
-/
theorem mem_dual_one_iff (x : E) :
    x ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ w : 𝓞 E, Algebra.trace ℚ E (x * w) ∈ (algebraMap ℤ ℚ).range := by
  rw [mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  constructor
  · intro h w
    exact h _ ((mem_one_iff _).2 ⟨w, rfl⟩)
  · intro h y hy
    obtain ⟨w, rfl⟩ := (mem_one_iff _).1 hy
    exact h w

def TrDual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Prop :=
  ∀ l ∈ L, Algebra.trace ℚ E (S.hT l z) ∈ (algebraMap ℤ ℚ).range

/- English proof (translation)
Rewrite using `[LinearMap.map_smulₛₗ₂]`. Both sides reduce to the same expression.
-/
theorem hT_smul_left (S : HSpace E) (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  rw [LinearMap.map_smulₛₗ₂]
  rfl

/- English proof (translation)
Rewrite using `[mem_dual_one_iff]`. Introduce `w`. Establish `hm : (starO w) • l ∈ L` using `L.smul_mem _ hl`. Use `hz _ hm` as an intermediate fact. Rewrite `this` using `[← algebraMap_smul E (starO w) l, hT_smul_left]`.

Establish `e : star (algebraMap (𝓞 E) E (starO w)) * S.hT l z = S.hT l z * (w : E)`. Rewrite using `[show algebraMap (𝓞 E) E (starO w) = star (w : E) from rfl, star_star, mul_comm]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem hT_left_mem_dual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) : S.hT l z ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_dual_one_iff]
  intro w
  have hm : (starO w) • l ∈ L := L.smul_mem _ hl
  have := hz _ hm
  rw [← algebraMap_smul E (starO w) l, hT_smul_left] at this
  have e : star (algebraMap (𝓞 E) E (starO w)) * S.hT l z = S.hT l z * (w : E) := by
    rw [show algebraMap (𝓞 E) E (starO w) = star (w : E) from rfl, star_star, mul_comm]
  rwa [e] at this

/- English proof (translation)
Establish `hx` using `hT_left_mem_dual S L z hz hl`. Rewrite `hx`, the goal using `[mem_dual_one_iff]`. Introduce `w`. Establish `h1` using `hx (starO w)`. Establish `hsym : S.hT z l = star (S.hT l z)` using `(S.herm.eq l z).symm`.

Rewrite using `[hsym, ← trace_star hσ, star_mul, star_star, mul_comm]`. Rewrite `h1` using `[starO_coe]`. Then use the resulting hypothesis.
-/
theorem hT_right_mem_dual (S : HSpace E) (hσ : ∀ (φ : E →+* ℂ) a, φ (star a) = star (φ a))
    (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) : S.hT z l ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hx := hT_left_mem_dual S L z hz hl
  rw [mem_dual_one_iff] at hx ⊢
  intro w
  have h1 := hx (starO w)
  have hsym : S.hT z l = star (S.hT l z) := (S.herm.eq l z).symm
  rw [hsym, ← trace_star hσ, star_mul, star_star, mul_comm]
  rwa [starO_coe] at h1

/- English proof (translation)
Rewrite using `[coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]`. Conclude with `mul_inv_cancel₀ (dual_ne_zero ℤ ℚ one_ne_zero)`.
-/
theorem dual_mul_diff :
    dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) * ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
      = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact mul_inv_cancel₀ (dual_ne_zero ℤ ℚ one_ne_zero)

/- English proof (translation)
Introduce `l hl`. Establish `hx` using `hT_left_mem_dual S L z hz hl`. Establish `hm : S.hT l z * (δ : E) ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) * ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)` using `mul_mem_mul hx ((mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩)`. Rewrite `hm` using `[dual_mul_diff, mem_one_iff]`. Take `⟨w, hw⟩` from `hm`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul E δ z, map_smul, smul_eq_mul, hw, mul_comm]`.
-/
theorem diff_smul_mem (S : HSpace E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {δ : 𝓞 E} (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) : δ • z ∈ dualSub S L := by
  intro l hl
  have hx := hT_left_mem_dual S L z hz hl
  have hm : S.hT l z * (δ : E) ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    mul_mem_mul hx ((mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩)
  rw [dual_mul_diff, mem_one_iff] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨w, ?_⟩
  rw [← algebraMap_smul E δ z, map_smul, smul_eq_mul, hw, mul_comm]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
