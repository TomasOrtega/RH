import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

/- English proof (translation)
Introduce and unpack `h s₀ c c' ⟨p, hp0, hp⟩ hh`. Establish `h1 : Tendsto (fun s : ℂ => p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 (c' - c))`. Use `(hh.sub hp).congr fun s => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0)`.

Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀))` using `(continuous_id.sub continuous_const).tendsto s₀`. Rewrite `this` using `[sub_self]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with s hs`.

Conclude with `sub_ne_zero.2 hs`. Establish `h3 : Tendsto (fun s : ℂ => ‖(s - s₀)⁻¹‖) (𝓝[≠] s₀) atTop` using `tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp h2)`. Distinguish the cases in `hd : 0 < p.degree`. Conclude with `absurd (p.tendsto_norm_atTop hd h3) (not_tendsto_atTop_of_tendsto_nhds h1.norm)`. Establish `hp' : p = 0`.

Rewrite using `[Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd), hp0, map_zero]`. Substitute `hp'` using the available equality. Simplify using `only [Polynomial.eval_zero, sub_zero] at hp`. Conclude with `tendsto_nhds_unique hp hh`.
-/
theorem laurentConst_eq_of_tendsto :
    ∀ (h : ℂ → ℂ) (s₀ c c' : ℂ), LaurentConst h s₀ c → Tendsto h (𝓝[≠] s₀) (𝓝 c') → c = c' := by
  rintro h s₀ c c' ⟨p, hp0, hp⟩ hh
  have h1 : Tendsto (fun s : ℂ => p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 (c' - c)) := by
    refine (hh.sub hp).congr fun s => ?_
    ring
  have h2 : Tendsto (fun s : ℂ => s - s₀) (𝓝[≠] s₀) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℂ => s - s₀) (𝓝 s₀) (𝓝 (s₀ - s₀)) :=
        (continuous_id.sub continuous_const).tendsto s₀
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.2 hs
  have h3 : Tendsto (fun s : ℂ => ‖(s - s₀)⁻¹‖) (𝓝[≠] s₀) atTop :=
    tendsto_norm_cobounded_atTop.comp (tendsto_inv₀_nhdsNE_zero.comp h2)
  by_cases hd : 0 < p.degree
  · exact absurd (p.tendsto_norm_atTop hd h3) (not_tendsto_atTop_of_tendsto_nhds h1.norm)
  · have hp' : p = 0 := by
      rw [Polynomial.eq_C_of_degree_le_zero (not_lt.1 hd), hp0, map_zero]
    subst hp'
    simp only [Polynomial.eval_zero, sub_zero] at hp
    exact tendsto_nhds_unique hp hh

end GlobalTheory.ThetaInner
