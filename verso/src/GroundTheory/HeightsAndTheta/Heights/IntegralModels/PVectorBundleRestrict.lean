import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGlue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsBasisOn.restrict {X : Scheme.{u}} {M : X.Modules} {U : X.Opens} {n : ℕ}
    {s : Fin n → Γ(M, U)} (hs : IsBasisOn M U s) {V : X.Opens} (hVU : V ≤ U) :
    IsBasisOn M V (fun i => (M.presheaf.map (homOfLE hVU).op).hom (s i)) := by
  intro W hWV
  have key : (fun r : Fin n → Γ(X, W) =>
      ∑ i, r i • (M.presheaf.map (homOfLE hWV).op).hom
        ((M.presheaf.map (homOfLE hVU).op).hom (s i))) =
      (fun r : Fin n → Γ(X, W) =>
        ∑ i, r i • (M.presheaf.map (homOfLE (hWV.trans hVU)).op).hom (s i)) := by
    funext r
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    show _ = (M.presheaf.map ((homOfLE hVU).op ≫ (homOfLE hWV).op)).hom (s i)
    rw [Functor.map_comp]
    rfl
  rw [key]
  exact hs W (hWV.trans hVU)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem IsBasisOn.restrictImage {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {U : X.Opens} {n : ℕ} {s : Fin n → Γ(M, f ''ᵁ U)} (hs : IsBasisOn M (f ''ᵁ U) s) :
    IsBasisOn (M.restrict f) U (fun i => (M.restrictAppIso f U).inv.hom (s i)) := by
  intro W hWU
  let e : Γ(X, W) ≃+* Γ(Y, f ''ᵁ W) := ((f.appIso W).commRingCatIsoToRingEquiv).symm
  have hb := (hs (f ''ᵁ W) (Scheme.Hom.image_mono f hWU)).comp
    (Equiv.piCongrRight fun _ : Fin n => e.toEquiv).bijective
  exact hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem VectorBundleRestrict.proof : VectorBundleRestrict.Statement := by
  intro X Y f _ E hE
  refine IsVectorBundle.of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app E) ?_
  intro x
  obtain ⟨U, -, hxU, n, s, hs⟩ := hE (f.base x)
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ U from hxU)
  have hle : f ''ᵁ V ≤ U := (Scheme.Hom.image_mono f hVU).trans (f.image_preimage_le U)
  exact ⟨V, hV, hxV, n, _, (hs.restrict hle).restrictImage f⟩

end

end GroundTheory.Heights₂.Heights.Model
