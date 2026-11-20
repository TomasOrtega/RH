import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
open scoped Pointwise

namespace GlobalTheory.TypePrimeSplit

/- English proof (translation)
Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `haveI : Finite K := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)`. Use `haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (h ▸ hp.one_lt)`. Take `⟨n, hn⟩` from `mem_zmultiples_of_prime_card (G := K) h (g := 1) (g' := x) one_ne_zero`. Conclude with `⟨n, by simpa using hn.symm⟩`.
-/
theorem exists_intCast_of_card {K : Type} [CommRing K] {p : ℕ} (hp : p.Prime) (h : Nat.card K = p) (x : K) :
    ∃ n : ℤ, x = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (h ▸ hp.one_lt)
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := K) h (g := 1) (g' := x) one_ne_zero
  exact ⟨n, by simpa using hn.symm⟩

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `key : ∀ x ∈ v.asIdeal, (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x ∈ v.asIdeal`. Introduce `x hx`. Assume the negation of the conclusion as `hy'`. Use `hn ⟨x, hx, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `: z = (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x` using `RingOfIntegers.ext hz`. Rewrite using `[this]` and apply the resulting hypothesis. Apply `H.der.unramEF v.asIdeal v.isPrime v.ne_bot` to reduce the goal to its premises. Introduce `x`. Use `show (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x ∈ v.asIdeal`.

Take `⟨n, hx⟩` from `exists_intCast_of_card hp h (Ideal.Quotient.mk v.asIdeal x)`. Establish `ha : x - n ∈ v.asIdeal` using `Ideal.Quotient.eq.1 (by rw [hx, map_intCast])`. Establish `h3` using `key _ ha`. Establish `hf : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • (n : 𝓞 H.E) = n` using `map_intCast (MulSemiringAction.toRingHom _ (𝓞 H.E) (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H)) n`. Rewrite `h3` using `[smul_sub, hf]`.

Establish `h4 : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x = ((PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - n) - (x - n)` using `by ring`. Rewrite using `[h4]`. Conclude with `sub_mem h3 ha`.
-/
theorem isSplitPl_of_card {R : Ranks} (H : Host R) (v : PlE H) {p : ℕ} (hp : p.Prime)
    (h : Nat.card (𝓞 H.E ⧸ v.asIdeal) = p) : IsSplitPl H v := by
  by_contra hn
  have key : ∀ x ∈ v.asIdeal, (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x ∈ v.asIdeal := by
    intro x hx
    by_contra hy'
    refine hn ⟨x, hx, fun z hz => ?_⟩
    have : z = (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x := RingOfIntegers.ext hz
    rwa [this]
  apply H.der.unramEF v.asIdeal v.isPrime v.ne_bot
  intro x
  show (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x ∈ v.asIdeal
  obtain ⟨n, hx⟩ := exists_intCast_of_card hp h (Ideal.Quotient.mk v.asIdeal x)
  have ha : x - n ∈ v.asIdeal := Ideal.Quotient.eq.1 (by rw [hx, map_intCast])
  have h3 := key _ ha
  have hf : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • (n : 𝓞 H.E) = n :=
    map_intCast (MulSemiringAction.toRingHom _ (𝓞 H.E) (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H)) n
  rw [smul_sub, hf] at h3
  have h4 : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x = ((PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - n) - (x - n) := by ring
  rw [h4]
  exact sub_mem h3 ha

/- English proof (translation)
Introduce `D k v hv` and use `isSplitPl_of_card D.host v (D.host.g_prime k) (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hv)`.
-/
theorem typePrime_split :
    ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v :=
  fun D k v hv => isSplitPl_of_card D.host v (D.host.g_prime k)
    (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hv)

end GlobalTheory.TypePrimeSplit
