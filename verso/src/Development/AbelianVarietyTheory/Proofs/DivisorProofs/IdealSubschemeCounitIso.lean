import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.QCoh.ClosedCounit

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isIso_unit_pushforward_subschemeι {X : Scheme.{0}} (I : X.IdealSheafData)
    (G : I.subscheme.Modules) [G.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app
      ((Scheme.Modules.pushforward I.subschemeι).obj G)) := by
  refine (QCoh.isIso_iff_forall_affine (M := (Scheme.Modules.pushforward I.subschemeι).obj G)
    (N := (Scheme.Modules.pushforward I.subschemeι).obj ((Scheme.Modules.pullback I.subschemeι).obj
      ((Scheme.Modules.pushforward I.subschemeι).obj G))) _).2 fun U hU => ?_
  obtain ⟨h₁, h₂⟩ := surjective_and_ker_unit_subschemeι I ((Scheme.Modules.pushforward I.subschemeι).obj G) ⟨U, hU⟩
  refine ⟨(LinearMap.ker_eq_bot (f := QCoh.appLinear _ U)).1 (h₂.trans ?_), h₁⟩
  rw [eq_bot_iff, Submodule.smul_le]
  intro a ha m _
  have h0 : (I.subschemeι.app U).hom a = 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app ⟨U, hU⟩]; exact ha
  rw [Submodule.mem_bot]
  have key : ∀ m' : Γ(G, I.subschemeι ⁻¹ᵁ U), (I.subschemeι.app U).hom a • m' = 0 := fun m' => by
    rw [h0, zero_smul]
  exact key m

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_preimage_eq_subschemeι {X : Scheme.{0}} (I : X.IdealSheafData) (V : I.subscheme.Opens) :
    ∃ U : X.Opens, I.subschemeι ⁻¹ᵁ U = V := by
  obtain ⟨t, ht, e⟩ := I.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.1 V.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext e⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem isIso_counit_subschemeι : ∀ {X : Scheme.{0}} (I : X.IdealSheafData) (G : I.subscheme.Modules)
    [G.IsQuasicoherent],
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).counit.app G) := by
  intro X I G _
  set adj := Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι
  have := isIso_unit_pushforward_subschemeι I G
  have h3 : IsIso ((Scheme.Modules.pushforward I.subschemeι).map (adj.counit.app G)) := by
    have e := adj.right_triangle_components G
    have : IsIso (adj.unit.app ((Scheme.Modules.pushforward I.subschemeι).obj G) ≫
        (Scheme.Modules.pushforward I.subschemeι).map (adj.counit.app G)) := by
      rw [e]; infer_instance
    exact IsIso.of_isIso_comp_left (adj.unit.app _) _
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  obtain ⟨U, rfl⟩ := exists_preimage_eq_subschemeι I V
  have := (Scheme.Modules.Hom.isIso_iff_isIso_app.1 h3) U
  rwa [Scheme.Modules.pushforward_map_app] at this

end GlobalTheory.QCoh.ClosedCounit
