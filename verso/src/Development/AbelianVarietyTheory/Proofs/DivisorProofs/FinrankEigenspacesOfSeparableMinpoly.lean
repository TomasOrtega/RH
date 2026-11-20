import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.EigSum

/- English proof (translation)
Establish `hf : f = minpoly Ω T`. Apply `Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))` to reduce the goal to its premises. Conclude with `associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)`. Establish `hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots`. Introduce `z`.

Rewrite using `[Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]`. Establish `hss : T.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0`. Use `⟨?_, fun z hz => (hroot z).2 hz⟩` and prove the remaining obligations. Use `set s := f.roots.toFinset`. Set `N : s → Submodule Ω V` to `fun z => T.eigenspace z`.

Establish `hind : iSupIndep N` using `iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective`. Establish `htop : ⨆ z, N z = ⊤`. Establish `h1` using `Module.End.iSup_maxGenEigenspace_eq_top T`. Simplify using `only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1`. Rewrite using `[eq_top_iff, ← h1]`.

Use `iSup_le fun μ => ?_` and prove the remaining obligations. Distinguish the cases in `hμ : μ ∈ s`. Conclude with `le_iSup N ⟨μ, hμ⟩`. Establish `: ¬ T.HasEigenvalue μ`. Rewrite using `[hroot]`.

Simplify `hμ` using `[s]`. Rewrite `this` using `[Module.End.hasEigenvalue_iff, not_not]`. Simplify using `[this]`. Establish `hint` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop`. Rewrite using `[← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq, Module.finrank_directSum]`.

Conclude with `(Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm`.
-/
theorem finrank_eigenspaces_of_separable_minpoly
    (Ω V : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [AddCommGroup V] [Module Ω V]
    [FiniteDimensional Ω V] (T : Module.End Ω V) (f : Polynomial Ω) (hm : f.Monic)
    (hs : f.Separable) (h0 : Polynomial.aeval T f = 0)
    (hmin : ∀ g : Polynomial Ω, Polynomial.aeval T g = 0 → f ∣ g) :
    ∑ z ∈ f.roots.toFinset, Module.finrank Ω (T.eigenspace z) = Module.finrank Ω V ∧
      ∀ z ∈ f.roots, T.eigenspace z ≠ ⊥ := by
  have hf : f = minpoly Ω T := by
    apply Polynomial.eq_of_monic_of_associated hm (minpoly.monic (Algebra.IsIntegral.isIntegral T))
    exact associated_of_dvd_dvd (hmin _ (minpoly.aeval Ω T)) (minpoly.dvd Ω T h0)
  have hroot : ∀ z, T.HasEigenvalue z ↔ z ∈ f.roots := by
    intro z
    rw [Module.End.hasEigenvalue_iff_isRoot, ← hf, Polynomial.mem_roots hm.ne_zero]
  have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  refine ⟨?_, fun z hz => (hroot z).2 hz⟩
  set s := f.roots.toFinset
  let N : s → Submodule Ω V := fun z => T.eigenspace z
  have hind : iSupIndep N :=
    iSupIndep.comp (Module.End.eigenspaces_iSupIndep T) Subtype.val_injective
  have htop : ⨆ z, N z = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top T
    simp only [hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
    rw [eq_top_iff, ← h1]
    refine iSup_le fun μ => ?_
    by_cases hμ : μ ∈ s
    · exact le_iSup N ⟨μ, hμ⟩
    · have : ¬ T.HasEigenvalue μ := by
        rw [hroot]; simpa [s] using hμ
      rw [Module.End.hasEigenvalue_iff, not_not] at this
      simp [this]
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap N) hint).finrank_eq,
    Module.finrank_directSum]
  exact (Finset.sum_coe_sort s (fun z => Module.finrank Ω (T.eigenspace z))).symm

end GlobalTheory.EigSum
