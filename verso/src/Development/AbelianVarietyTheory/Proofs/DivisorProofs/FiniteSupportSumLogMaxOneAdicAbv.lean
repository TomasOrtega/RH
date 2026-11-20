import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
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
