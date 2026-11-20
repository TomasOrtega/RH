import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ _ a b hsq g hg hu W hW`. Use `set s := g.re with hs`. Set `φ : R × R → ℍ[R, a, b]` to `fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩`. Establish `hφ : Continuous φ`. Apply `continuous_induced_rng.2` to reduce the goal to its premises.

Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify `continuous_fst` using `[coords, φ]`. Simplify using `only [coords, φ]`. Conclude with `(continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)`.

Simplify using `only [coords, φ]`. Conclude with `(continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)`. Simplify using `only [coords, φ]`. Conclude with `(continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)`. Apply the tactic sequence `have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]`.

Establish `hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R))` using `hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)`. Take `⟨O₀, hO₀, V, hV, hOV⟩` from `mem_nhds_prod_iff.1 hpre`. Take `⟨U, hU, hUV⟩` from `hsq V hV`. Use `set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def`. Establish `hc : c * (1 - s ^ 2) = 1`.

Rewrite using `[hc_def]`. Use `hu.unit.inv_mul` as an intermediate fact. Simplify using `using this`. Set `r : R → R` to `fun t => (1 - t ^ 2) * c`. Establish `hr : Continuous r` using `(continuous_const.sub (continuous_id.pow 2)).mul continuous_const`.

Establish `hrs : r s = 1` using `by simp only [r]; rw [mul_comm]; exact hc`. Use `⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_interior_iff_mem_nhds]`. Use `Filter.inter_mem hO₀ ?_` and prove the remaining obligations. Conclude with `hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)`.

Introduce `t ht`. Establish `ht'` using `interior_subset ht`. Take `⟨μ, hμV, hμ⟩` from `hUV (r t) ht'.2`. Use `⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩` and prove the remaining obligations. Establish `hμ' : μ ^ 2 = (1 - t ^ 2) * c` using `hμ`.

Simplify using `only [nrm, φ] at hg ⊢`. Take the linear combination `μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc`.
-/
theorem traceOpen_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro R _ _ _ a b hsq g hg hu W hW
  set s := g.re with hs
  let φ : R × R → ℍ[R, a, b] := fun p => ⟨p.1, p.2 * g.imI, p.2 * g.imJ, p.2 * g.imK⟩
  have hφ : Continuous φ := by
    apply continuous_induced_rng.2
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa [coords, φ] using continuous_fst
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
    · simp only [coords, φ]; exact (continuous_snd.mul continuous_const : Continuous fun p : R × R => p.2 * _)
  have hφs : φ (s, 1) = g := by ext <;> simp [φ, s]
  have hpre : φ ⁻¹' W ∈ 𝓝 (s, (1 : R)) := hφ.continuousAt.preimage_mem_nhds (by rw [hφs]; exact hW)
  obtain ⟨O₀, hO₀, V, hV, hOV⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨U, hU, hUV⟩ := hsq V hV
  set c : R := ((hu.unit⁻¹ : Rˣ) : R) with hc_def
  have hc : c * (1 - s ^ 2) = 1 := by
    rw [hc_def]
    have := hu.unit.inv_mul
    simpa using this
  let r : R → R := fun t => (1 - t ^ 2) * c
  have hr : Continuous r := (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
  have hrs : r s = 1 := by simp only [r]; rw [mul_comm]; exact hc
  refine ⟨interior (O₀ ∩ r ⁻¹' U), isOpen_interior, ?_, ?_⟩
  · rw [mem_interior_iff_mem_nhds]
    refine Filter.inter_mem hO₀ ?_
    exact hr.continuousAt.preimage_mem_nhds (by rw [hrs]; exact hU)
  · intro t ht
    have ht' := interior_subset ht
    obtain ⟨μ, hμV, hμ⟩ := hUV (r t) ht'.2
    refine ⟨φ (t, μ), hOV (Set.mk_mem_prod ht'.1 hμV), ?_, rfl⟩
    have hμ' : μ ^ 2 = (1 - t ^ 2) * c := hμ
    simp only [nrm, φ] at hg ⊢
    linear_combination μ ^ 2 * hg + (1 - s ^ 2) * hμ' + (1 - t ^ 2) * hc

end GlobalTheory
