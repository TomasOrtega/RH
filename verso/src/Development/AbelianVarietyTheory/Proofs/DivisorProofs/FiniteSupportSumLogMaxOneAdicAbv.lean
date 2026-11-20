import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory

/- English proof (translation)
Introduce `v hv`. Simplify using `only [Function.mem_support] at hv`. Use `show 1 < v.valuation F c`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hv` to reduce the goal to its premises. Establish `hle : NumberField.HeightOneSpectrum.adicAbv F v c ≤ 1`. Rewrite using `[NumberField.HeightOneSpectrum.adicAbv_def]`. Establish `hmono` using `(WithZeroMulInt.toNNReal_strictMono (e := (Ideal.absNorm v.asIdeal : NNReal)) ?_).monotone h`. Rewrite `hmono` using `[map_one]`.

Conclude with `hmono` after adjusting the coercions. Conclude with `NumberField.HeightOneSpectrum.one_lt_absNorm v` after adjusting the coercions. Rewrite using `[max_eq_left hle, Real.log_one]`.
-/
theorem support_log_max_one_adicAbv_subset (F : Type) [Field F] [NumberField F] (c : F) :
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c))) ⊆
      HeightOneSpectrum.Support (𝓞 F) c := by
  intro v hv
  simp only [Function.mem_support] at hv
  show 1 < v.valuation F c
  by_contra h
  push_neg at h
  apply hv
  have hle : NumberField.HeightOneSpectrum.adicAbv F v c ≤ 1 := by
    rw [NumberField.HeightOneSpectrum.adicAbv_def]
    have hmono := (WithZeroMulInt.toNNReal_strictMono (e := (Ideal.absNorm v.asIdeal : NNReal)) ?_).monotone h
    · rw [map_one] at hmono
      exact_mod_cast hmono
    · exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  rw [max_eq_left hle, Real.log_one]

/- English proof (translation)
Introduce `F _ _ s`. Use `(Set.Finite.biUnion s.finite_toSet fun c _ => (HeightOneSpectrum.Support.finite (𝓞 F) c).subset (support_log_max_one_adicAbv_subset F c)).subset ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite `hv` using `[Function.mem_support]`. Take `⟨c, hc, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hv`.

Conclude with `Set.mem_biUnion (Finset.mem_coe.2 hc) hne`.
-/
theorem finite_support_sum_log_max_one_adicAbv :
    ∀ (F : Type) [Field F] [NumberField F] (s : Finset F),
    (Function.support fun v : HeightOneSpectrum (𝓞 F) =>
      ∑ c ∈ s, Real.log (max 1 (NumberField.HeightOneSpectrum.adicAbv F v c))).Finite := by
  intro F _ _ s
  refine (Set.Finite.biUnion s.finite_toSet fun c _ =>
    (HeightOneSpectrum.Support.finite (𝓞 F) c).subset
      (support_log_max_one_adicAbv_subset F c)).subset ?_
  intro v hv
  rw [Function.mem_support] at hv
  obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact Set.mem_biUnion (Finset.mem_coe.2 hc) hne

end GlobalTheory
