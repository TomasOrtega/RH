import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

open Cardinal Filter Topology

namespace GlobalTheory.PadicCard

/- English proof (translation)
Establish `h : ∀ x : X, ∃ u : ℕ → D, Tendsto (fun n => f (u n)) atTop (𝓝 x)`. Introduce `x`. Take `⟨v, hv, hlim⟩` from `mem_closure_iff_seq_limit.1 (hf x)`. Use `choose u hu using hv`. Conclude with `⟨u, by simpa only [hu] using hlim⟩`.

Use `choose g hg using h`. Establish `hinj : Function.Injective g`. Introduce `x y hxy`. Use `hg y` as an intermediate fact. Rewrite `this` using `[← hxy]`.

Conclude with `tendsto_nhds_unique (hg x) this`. Simplify using `using mk_le_of_injective hinj`.
-/
theorem mk_le_pow_aleph0_of_denseRange {D X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [T2Space X] (f : D → X) (hf : DenseRange f) : #X ≤ #D ^ ℵ₀ := by
  have h : ∀ x : X, ∃ u : ℕ → D, Tendsto (fun n => f (u n)) atTop (𝓝 x) := by
    intro x
    obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose u hu using hv
    exact ⟨u, by simpa only [hu] using hlim⟩
  choose g hg using h
  have hinj : Function.Injective g := by
    intro x y hxy
    have := hg y
    rw [← hxy] at this
    exact tendsto_nhds_unique (hg x) this
  simpa using mk_le_of_injective hinj

/- English proof (translation)
Simplify using `using mk_le_pow_aleph0_of_denseRange _ (Padic.denseRange_ratCast l)`.
-/
theorem mk_padic_le (l : ℕ) [Fact l.Prime] : #ℚ_[l] ≤ 𝔠 := by
  simpa using mk_le_pow_aleph0_of_denseRange _ (Padic.denseRange_ratCast l)

/- English proof (translation)
The claim follows from `le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans (max_le (mk_padic_le l) aleph0_le_continuum)) ((continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]).trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective))`.
-/
theorem mk_padicAlgCl (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 :=
  le_antisymm
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (mk_padic_le l) aleph0_le_continuum))
    ((continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]).trans
      (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective))

/- English proof (translation)
Use `le_antisymm ?_ (continuum_le_cardinal_of_nontriviallyNormedField ℂ_[l])` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mk_padicComplex (l : ℕ) [Fact l.Prime] : #ℂ_[l] = 𝔠 := by
  refine le_antisymm ?_ (continuum_le_cardinal_of_nontriviallyNormedField ℂ_[l])
  calc #ℂ_[l] ≤ #(PadicAlgCl l) ^ ℵ₀ :=
        mk_le_pow_aleph0_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l))
    _ = 𝔠 := by rw [mk_padicAlgCl, continuum_power_aleph0]

/- English proof (translation)
Introduce `l _`. Conclude with `⟨by rw [mk_padicAlgCl, mk_complex], by rw [mk_padicComplex, mk_complex]⟩`.
-/
theorem card_padicAlgCl_padicComplex :
    ∀ (l : ℕ) [Fact l.Prime], Cardinal.mk (PadicAlgCl l) = Cardinal.mk ℂ ∧
      Cardinal.mk ℂ_[l] = Cardinal.mk ℂ := by
  intro l _
  exact ⟨by rw [mk_padicAlgCl, mk_complex], by rw [mk_padicComplex, mk_complex]⟩

end GlobalTheory.PadicCard
