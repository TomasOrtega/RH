import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Adelic

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Equip the data with the indicated structure. Introduce a local definition for the expression. Introduce a local definition for the expression.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem subset_of_forall_pt_mem : ∀ (k : Type) [Field k] (S : LinSys k), S.IsVariety → ∀ (Ω : Type) [Field Ω]
    [Algebra k Ω] [IsAlgClosed Ω] (Z : Set S.Y), IsClosed Z → ∀ U : Set S.Y, IsOpen U →
    (∀ x : S.Pt Ω, ptOf x.1 ∈ Z → ptOf x.1 ∈ U) → Z ⊆ U := by
  intro k _ S hS Ω _ _ _ Z hZ U hU h
  haveI := hS.smooth
  haveI : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  haveI : LocallyOfFiniteType S.str := inferInstance
  haveI : JacobsonSpace S.Y := LocallyOfFiniteType.jacobsonSpace S.str
  by_contra hne
  obtain ⟨z, hzZ, hzU⟩ := Set.not_subset.1 hne
  obtain ⟨y, ⟨hyZ, hyU⟩, hy⟩ := nonempty_inter_closedPoints (Z := Z ∩ Uᶜ) ⟨z, hzZ, hzU⟩
    (hZ.inter hU.isClosed_compl).isLocallyClosed
  have hyc : IsClosed ({y} : Set S.Y) := hy
  haveI : IsFinite (resPt y ≫ S.str) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hyc
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    unfold resPt
    infer_instance
  have hφ : (S.baseHom (resPt y)).IsIntegral := by
    have : IsIntegralHom (Spec.map (Spec.preimage (resPt y ≫ S.str))) := by
      rw [Spec.map_preimage]; infer_instance
    rw [IsIntegralHom.SpecMap_iff] at this
    exact this
  letI : Algebra k (S.Y.residueField y) := (S.baseHom (resPt y)).toAlgebra
  haveI : Algebra.IsIntegral k (S.Y.residueField y) := ⟨hφ⟩
  let τ : S.Y.residueField y →ₐ[k] Ω := IsAlgClosed.lift
  let x : S.Pt Ω := ⟨spMap τ.toRingHom ≫ resPt y, by
    rw [Category.assoc, S.comp_str, ← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a⟩
  have hx : ptOf x.1 = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  exact hyU (hx ▸ h x (hx.symm ▸ hyZ))

end GlobalTheory.Adelic
