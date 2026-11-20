import Mathlib
import GroundTheory.AutomorphicForms.JacquetAdmissible
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

section Bridge

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] in

/- English proof (translation)
Use extensionality with `v`. Express the relevant statement in the definitionally equal form `(∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ ∀ h ∈ K, ρ h v = v`. Simplify using the standard rewrite rules.
-/
theorem fixed_eq_fixedVectors (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  change (∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ ∀ h ∈ K, ρ h v = v
  simp

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem isSmooth_found_iff (ρ : Representation ℂ G V) :
    GroundTheory.Automorphic.IsSmooth ρ ↔ GlobalTheory.PRep.IsSmooth ρ := Iff.rfl

/- English proof (translation)
Use `⟨(isSmooth_found_iff ρ).1 h.1, fun K hKo hKc => ?_⟩` and prove the remaining obligations. Rewrite using `[fixed_eq_fixedVectors]`. Conclude with `h.2 K hKc hKo`.
-/
theorem isAdmissible_of_found {ρ : Representation ℂ G V} (h : GroundTheory.Automorphic.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible ρ := by
  refine ⟨(isSmooth_found_iff ρ).1 h.1, fun K hKo hKc => ?_⟩
  rw [fixed_eq_fixedVectors]
  exact h.2 K hKc hKo

end Bridge

/- English proof (translation)
Introduce `k _ _ _ _ N X _ _ π hs hi`. Establish `: π.IsIrreducible` using `hi`. Conclude with `isAdmissible_of_found (GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible ((isSmooth_found_iff π).2 hs))`.
-/
theorem irrSmoothAdmissible_holds : IrrSmoothAdmissible := by
  intro k _ _ _ _ N X _ _ π hs hi
  have : π.IsIrreducible := hi
  exact isAdmissible_of_found
    (GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible ((isSmooth_found_iff π).2 hs))

end PositivityTheory.PfBern.Props1
