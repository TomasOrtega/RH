import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KSGraph

/- English proof (translation)
Express the relevant statement in the definitionally equal form `ConnectedSpace (PrimeSpectrum (DualNumber k))`. Establish `: PreconnectedSpace (PrimeSpectrum (DualNumber k))`. Use `⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦ ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩` and prove the remaining obligations. Conclude with `(IsLocalRing.specializes_closedPoint y).mem_closure`. Conclude with `⟨inferInstance⟩`.
-/
theorem connectedSpace_sp_dualNumber (k : Type) [Field k] : ConnectedSpace (Sp (DualNumber k)) := by
  change ConnectedSpace (PrimeSpectrum (DualNumber k))
  have : PreconnectedSpace (PrimeSpectrum (DualNumber k)) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (DualNumber k)) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  exact ⟨inferInstance⟩

/- English proof (translation)
Use `hA'.smooth` as an intermediate fact. Use `hA'.geomConnected` as an intermediate fact. Use `connectedSpace_sp_dualNumber k` as an intermediate fact. Establish `: ConnectedSpace A'.left` using `GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap`. Conclude with `exists_dim_of_preconnected A'.hom (Classical.arbitrary _)`.
-/
theorem exists_dim {k : Type} [Field k] (A' : Over (Sp (DualNumber k))) [GrpObj A']
    (hA' : IsAbelianScheme A') : ∃ g, SmoothOfRelativeDimension g A'.hom := by
  have := hA'.smooth
  have := hA'.geomConnected
  have := connectedSpace_sp_dualNumber k
  have : ConnectedSpace A'.left := GeometricallyConnected.connectedSpace A'.hom A'.hom.isOpenMap
  exact exists_dim_of_preconnected A'.hom (Classical.arbitrary _)

/- English proof (translation)
Introduce `k _ A₀ _ A' _ i h hA' x hx y y' hy`. Take `⟨g, hg⟩` from `exists_dim A' hA'`. Establish `P` using `GlobalTheory.abelianDeRham`. Establish `hA₀` using `PolPull.isAbelianScheme_of_isGrpPullback hA' h`. Establish `g₀` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg`.

Establish `hL` using `(P.2.1 k A₀ g hA₀ g₀).1`. Establish `reg` using `ksRegular_of_isAbelianScheme P h hA' hg`. Prove the components needed by the constructor for the conclusion. Introduce `hy'`. Take `⟨w, hw, -⟩` from `hL.1 y`.

Take `⟨w', hw', -⟩` from `hL.1 y'`. Establish `e` using `(reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩`. Substitute `e` using the available equality. Conclude with `hw'.sub_mem hw`. Introduce `hz`.

Take `⟨v, ⟨z, hz', -⟩, -⟩` from `reg (y' - y) hz`. Take `⟨d, hd, e⟩` from `hy`. Take `⟨d', hd', e'⟩` from `hz'`. Use `⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]`.

Apply the tactic sequence `ext <;> simp`.
-/
theorem isFilLift_iff_sub_mem : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (A' : Over (Sp (DualNumber k))) [GrpObj A'] (i : A₀.left ⟶ A'.left) (h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i), IsAbelianScheme A' → ∀ x ∈ Fil A₀, ∀ y y' : HdR A₀, IsFilLift h x y → (IsFilLift h x y' ↔ y' - y ∈ Fil A₀) := by
  intro k _ A₀ _ A' _ i h hA' x hx y y' hy
  obtain ⟨g, hg⟩ := exists_dim A' hA'
  have P := GlobalTheory.abelianDeRham
  have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA' h
  have g₀ := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback h.1 hg
  have hL := (P.2.1 k A₀ g hA₀ g₀).1
  have reg := ksRegular_of_isAbelianScheme P h hA' hg
  constructor
  · intro hy'
    obtain ⟨w, hw, -⟩ := hL.1 y
    obtain ⟨w', hw', -⟩ := hL.1 y'
    have e := (reg x hx).unique ⟨y, hy, hw⟩ ⟨y', hy', hw'⟩
    subst e
    exact hw'.sub_mem hw
  · intro hz
    obtain ⟨v, ⟨z, hz', -⟩, -⟩ := reg (y' - y) hz
    obtain ⟨d, hd, e⟩ := hy
    obtain ⟨d', hd', e'⟩ := hz'
    refine ⟨d + (TrivSqZeroExt.inr 1 : DualNumber k) • d', add_mem hd (Submodule.smul_mem _ _ hd'), fun c ↦ ?_⟩
    rw [LinearMap.add_apply, LinearMap.smul_apply, e, e', smul_eq_mul]
    ext <;> simp

end GlobalTheory.KSGraph
