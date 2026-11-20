import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsAffineOpenOfFiniteOpensProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

def autOfRightAction {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X)) (h1 : ρ 1 = 𝟙 X)
    (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) : Ga →* Aut X :=
  MonoidHom.mk' (fun a ↦
    { hom := ρ a⁻¹
      inv := ρ a
      hom_inv_id := by rw [← hm, inv_mul_cancel, h1]
      inv_hom_id := by rw [← hm, mul_inv_cancel, h1] }) fun a c ↦
    Iso.ext (show ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹ by rw [mul_inv_rev, hm])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem autOfRightAction_hom {X : Scheme.{0}} {Ga : Type} [Group Ga] (ρ : Ga → (X ⟶ X))
    (h1 : ρ 1 = 𝟙 X) (hm : ∀ a c, ρ (a * c) = ρ a ≫ ρ c) (a : Ga) :
    (autOfRightAction ρ h1 hm a).hom = ρ a⁻¹ := rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Take `⟨N, i, hi, hqc, rfl⟩` from `h`. Use `haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N`. Conclude with `⟨inferInstance, inferInstance, inferInstance⟩`.
-/
theorem _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f := by
  obtain ⟨N, i, hi, hqc, rfl⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  exact ⟨inferInstance, inferInstance, inferInstance⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Introduce `K _ X s Ga _ _ ρ hq h1 hm hs hfree`. Use `set τ := _root_.GlobalTheory.ZM.autOfRightAction ρ h1 hm with hτ`. Use `haveI : _root_.GlobalTheory.OrbitsInAffineOpens τ := _root_.GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hq τ`. Establish `hτg : ∀ g : Ga, (τ g).hom = ρ g⁻¹` using `fun _ ↦ rfl`. Establish `hτs : ∀ g : Ga, (τ g).hom ≫ s = s` using `fun g ↦ hs g⁻¹`.

Establish `hfreeτ : _root_.GlobalTheory.IsFreeAction τ`. Use `_root_.GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)` and prove the remaining obligations. Conclude with `inv_eq_one.mp (hfree k x g⁻¹ hx)`. Use `set π := _root_.GlobalTheory.finiteQuotient.π τ with hπ`. Establish `hπs : π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs = s` using `_root_.GlobalTheory.finiteQuotient.π_desc τ s hτs`.

Establish `hQ` using `_root_.GlobalTheory.finiteQuotient.isAffineQuotient τ`. Take `⟨hsep, hlft, hqc⟩` from `_root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq`. Use `⟨_, π, _root_.GlobalTheory.finiteQuotient.desc τ s hτs, hπs, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `⟨inferInstance, h1, hm, fun a ↦ ?_, _root_.GlobalTheory.finiteQuotient.isFinite_π_of_isFreeAction hfreeτ, _root_.GlobalTheory.finiteQuotient.etale_π hfreeτ, hQ.surjective, ?_⟩` and prove the remaining obligations. Use `_root_.GlobalTheory.finiteQuotient.comp_π τ a⁻¹` as an intermediate fact.

Rewrite `this` using `[hτg, inv_inv]`. Then use the resulting hypothesis. Introduce `k _ _ y y' hyy`. Take `⟨g, hg⟩` from `(_root_.GlobalTheory.finiteQuotient.comp_π_eq_iff τ y y').mp hyy`. Use `⟨g⁻¹, hg, fun b hb ↦ ?_⟩` and prove the remaining obligations. Establish `key : y ≫ ρ (b * g) = y`.

Rewrite using `[hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]`. Conclude with `eq_inv_of_mul_eq_one_left (hfree k y _ key)`. Use `haveI : IsSeparated (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by`. Rewrite using `[hπs]`. Conclude with `hsep`.

Conclude with `hQ.isSeparated _`. Use `haveI : LocallyOfFiniteType (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by`. Rewrite using `[hπs]`. Conclude with `hlft`. Use `haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))`.

Conclude with `hQ.locallyOfFiniteType _`. Use `haveI : QuasiCompact (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by`. Rewrite using `[hπs]`. Conclude with `hqc`. Conclude with `hQ.quasiCompact _`.
-/
theorem _root_.GlobalTheory.ZM.exists_isGaloisCover_of_isQProjOver :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) (Ga : Type) [Group Ga] [Finite Ga] (ρ : Ga → (X ⟶ X)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s → ρ 1 = 𝟙 X → (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a, ρ a ≫ s = s) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k ⟶ X) (a : Ga), y ≫ ρ a = y → a = 1) → ∃ (Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K), π ≫ sY = s ∧ _root_.GlobalTheory.ZM.IsGaloisCover Ga ρ π ∧ IsSeparated sY ∧ LocallyOfFiniteType sY ∧ QuasiCompact sY := by
  intro K _ X s Ga _ _ ρ hq h1 hm hs hfree
  set τ := _root_.GlobalTheory.ZM.autOfRightAction ρ h1 hm with hτ
  haveI : _root_.GlobalTheory.OrbitsInAffineOpens τ := _root_.GlobalTheory.OrbitsInAffineOpens.of_isQProjOver hq τ
  have hτg : ∀ g : Ga, (τ g).hom = ρ g⁻¹ := fun _ ↦ rfl
  have hτs : ∀ g : Ga, (τ g).hom ≫ s = s := fun g ↦ hs g⁻¹
  have hfreeτ : _root_.GlobalTheory.IsFreeAction τ := by
    refine _root_.GlobalTheory.IsFreeAction.of_isAlgClosed.{0} (fun k _ _ x g hx ↦ ?_)
    exact inv_eq_one.mp (hfree k x g⁻¹ hx)
  set π := _root_.GlobalTheory.finiteQuotient.π τ with hπ
  have hπs : π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs = s :=
    _root_.GlobalTheory.finiteQuotient.π_desc τ s hτs
  have hQ := _root_.GlobalTheory.finiteQuotient.isAffineQuotient τ
  obtain ⟨hsep, hlft, hqc⟩ := _root_.GlobalTheory.ZM.isSeparated_finiteType_of_isQProjOver hq
  refine ⟨_, π, _root_.GlobalTheory.finiteQuotient.desc τ s hτs, hπs, ?_, ?_, ?_, ?_⟩
  · refine ⟨inferInstance, h1, hm, fun a ↦ ?_,
      _root_.GlobalTheory.finiteQuotient.isFinite_π_of_isFreeAction hfreeτ,
      _root_.GlobalTheory.finiteQuotient.etale_π hfreeτ, hQ.surjective, ?_⟩
    · have := _root_.GlobalTheory.finiteQuotient.comp_π τ a⁻¹
      rwa [hτg, inv_inv] at this
    · intro k _ _ y y' hyy
      obtain ⟨g, hg⟩ :=
        (_root_.GlobalTheory.finiteQuotient.comp_π_eq_iff τ y y').mp hyy
      refine ⟨g⁻¹, hg, fun b hb ↦ ?_⟩
      have key : y ≫ ρ (b * g) = y := by
        rw [hm, ← Category.assoc, hb, ← hg, hτg, Category.assoc, ← hm, inv_mul_cancel, h1, Category.comp_id]
      exact eq_inv_of_mul_eq_one_left (hfree k y _ key)
  · haveI : IsSeparated (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by
      rw [hπs]; exact hsep
    exact hQ.isSeparated _
  · haveI : LocallyOfFiniteType (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by
      rw [hπs]; exact hlft
    haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
    exact hQ.locallyOfFiniteType _
  · haveI : QuasiCompact (π ≫ _root_.GlobalTheory.finiteQuotient.desc τ s hτs) := by
      rw [hπs]; exact hqc
    exact hQ.quasiCompact _

end GlobalTheory.ZM
