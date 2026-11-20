import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem contDiffOn_zpow_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  unfold IsSmoothHerm at hA
  have hne : ∀ z ∈ {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, A.h z ≠ 0 :=
    fun z hz => (A.pos z hz).ne'
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hA.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hA.pow m).inv (fun z hz => pow_ne_zero _ (hne z hz))

end Ii

open Ii in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem combLine_smooth_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun h => ?_, fun h z => ?_, ?_⟩
  · exact contDiffOn_prod fun j _ => contDiffOn_zpow_h (ℓ j) (h j) (n j)
  · exact Finset.prod_congr rfl fun j _ => by rw [h j z]
  · exact contDiffOn_const

end RootFieldNumerics
