import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BisimplicialActionSecondFactor
open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx GlobalTheory.CompanionTheory.HopfLe

namespace GlobalTheory.CompanionTheory.HopfLe

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_dual_functionals_of_linearIndependent :
    ∀ {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V] [DecidableEq ι], IsField R →
      ∀ x : ι → V, LinearIndependent R x →
        ∃ l : ι → V →ₗ[R] R, ∀ i j, l i (x j) = if i = j then 1 else 0 := by
  intro R V ι _ _ _ _ hR x hx
  letI : Field R := hR.toField
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis ι R (Submodule.span R (Set.range x)),
      ∀ k, (b k : V) = x k := ⟨Module.Basis.span hx, fun k => by rw [Module.Basis.span_apply hx k]⟩
  have hext : ∀ i : ι, ∃ g : V →ₗ[R] R,
      g ∘ₗ (Submodule.span R (Set.range x)).subtype = b.coord i :=
    fun i => LinearMap.exists_extend _
  choose l hl using hext
  refine ⟨l, fun i j => ?_⟩
  have h : l i (b j : V) = b.coord i (b j) := LinearMap.congr_fun (hl i) (b j)
  rw [hb j] at h
  rw [h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.HopfLe
