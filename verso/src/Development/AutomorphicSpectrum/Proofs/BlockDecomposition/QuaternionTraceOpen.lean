import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

/- English proof (translation)
Introduce `U hU`. Establish `hc : 1 - a.re ^ 2 ≠ 0` using `fun h => hp (sub_eq_zero.1 h).symm`. Set `g : K × K → Q d β K` to `fun z => ⟨z.1, z.2 * a.imI, z.2 * a.imJ, z.2 * a.imK⟩`. Establish `hg : Continuous g`. Rewrite using `[continuous_q_iff]`.

Apply the tactic sequence `refine ⟨continuous_fst, ?_, ?_, ?_⟩ <;> exact continuous_snd.mul continuous_const`. Establish `hg1 : g (a.re, 1) = a`. Apply the tactic sequence `ext <;> simp [g]`. Establish `hpre : g ⁻¹' U ∈ 𝓝 ((a.re, 1) : K × K)` using `hg.continuousAt.preimage_mem_nhds (by rwa [hg1])`. Take `⟨A, hA, V, hV, hAV⟩` from `mem_nhds_prod_iff.1 hpre`.

Establish `hx : Filter.Tendsto (fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2)) (𝓝 a.re) (𝓝 1)`. Establish `hcont : Continuous fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2)`. Simplify using `only [div_eq_mul_inv]`. Conclude with `(continuous_const.sub (continuous_id.pow 2)).mul continuous_const`. Use `hcont.tendsto a.re` as an intermediate fact.

Simplify `this` using `[div_self hc]`. Use `filter_upwards [hA, hx.eventually (hsq V hV)] with r hrA hr`. Take `⟨μ, hμV, hμ⟩` from `hr`. Use `⟨g (r, μ), hAV (Set.mk_mem_prod hrA hμV), ?_, rfl⟩` and prove the remaining obligations. Establish `hy : algebraMap F K d * a.imI ^ 2 + algebraMap F K β * a.imJ ^ 2 - algebraMap F K d * algebraMap F K β * a.imK ^ 2 = a.re ^ 2 - 1`.

Establish `: qn a = 1` using `ha`. Simplify using `only [qn] at this`. Take the linear combination `-this`. Establish `hμ' : μ ^ 2 * (1 - a.re ^ 2) = 1 - r ^ 2`. Rewrite using `[hμ]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [qn, g]`. Take the linear combination `-(μ ^ 2) * hy + hμ'`.
-/
theorem re_normOne_open_of_sq_ne_one {F K : Type} [Field F] [Field K] [Algebra F K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] (d β : F)
    (a : Q d β K) (ha : qn a = 1) (hp : a.re ^ 2 ≠ 1)
    (hsq : ∀ V ∈ 𝓝 (1 : K), ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x) :
    ∀ U ∈ 𝓝 a, ∀ᶠ r in 𝓝 a.re, ∃ b ∈ U, qn b = 1 ∧ b.re = r := by
  intro U hU
  have hc : 1 - a.re ^ 2 ≠ 0 := fun h => hp (sub_eq_zero.1 h).symm
  let g : K × K → Q d β K := fun z => ⟨z.1, z.2 * a.imI, z.2 * a.imJ, z.2 * a.imK⟩
  have hg : Continuous g := by
    rw [continuous_q_iff]
    refine ⟨continuous_fst, ?_, ?_, ?_⟩ <;> exact continuous_snd.mul continuous_const
  have hg1 : g (a.re, 1) = a := by
    ext <;> simp [g]
  have hpre : g ⁻¹' U ∈ 𝓝 ((a.re, 1) : K × K) :=
    hg.continuousAt.preimage_mem_nhds (by rwa [hg1])
  obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.1 hpre
  have hx : Filter.Tendsto (fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2)) (𝓝 a.re) (𝓝 1) := by
    have hcont : Continuous fun r : K => (1 - r ^ 2) / (1 - a.re ^ 2) := by
      simp only [div_eq_mul_inv]
      exact (continuous_const.sub (continuous_id.pow 2)).mul continuous_const
    have := hcont.tendsto a.re
    simpa [div_self hc] using this
  filter_upwards [hA, hx.eventually (hsq V hV)] with r hrA hr
  obtain ⟨μ, hμV, hμ⟩ := hr
  refine ⟨g (r, μ), hAV (Set.mk_mem_prod hrA hμV), ?_, rfl⟩
  have hy : algebraMap F K d * a.imI ^ 2 + algebraMap F K β * a.imJ ^ 2
      - algebraMap F K d * algebraMap F K β * a.imK ^ 2 = a.re ^ 2 - 1 := by
    have : qn a = 1 := ha
    simp only [qn] at this
    linear_combination -this
  have hμ' : μ ^ 2 * (1 - a.re ^ 2) = 1 - r ^ 2 := by
    rw [hμ]; field_simp
  simp only [qn, g]
  linear_combination -(μ ^ 2) * hy + hμ'

end GlobalTheory.CompanionTheory.PlaneSA
