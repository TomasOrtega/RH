import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.FieldTriv

/- English proof (translation)
Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace f`. Establish `: QuasiSeparatedSpace X` using `quasiSeparatedSpace_of_quasiSeparated f`. Establish `: IsIntegral X'` using `GeometricallyIntegral.geometrically_isIntegral _ _ _ H`. Establish `: IsIso p.appTop` using `ProperFunctions.isIso_appTop_baseChange_of_field H`. Establish `hflat : β.Flat`.

Set `_` to `β.toAlgebra`. Conclude with `inferInstanceAs (Module.Flat k k')`. Establish `lift : ∀ x : X, ∃ y, π y = x` using `fun x => by`. Take `⟨y, hy, -⟩` from `Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k') (Subsingleton.elim (α := PrimeSpectrum k) _ _)`. Conclude with `⟨y, hy⟩`.

Take `⟨σ, hσ⟩` from `GenericTriv.exists_sec_isUnit β hflat f π p H (ConcreteCategory.bijective_of_isIso p.appTop).2 hN t ht`. Establish `hu : ∀ i, IsUnit (σ.f i)` using `fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by`. Take `⟨y, rfl⟩` from `lift x`. Use `hσ y i hx` as an intermediate fact. Rewrite `this` using `[gs_stalkMap π y _ hx, isUnit_map_iff]`.

Conclude with `(congrArg IsUnit (gs_eq (𝟙 X) (π y) (N.U i) hx _)).mp this`. Conclude with `⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (σ.compat i i')⟩`.
-/
theorem exists_gen_of_isPullback {k k' : Type} [Field k] [Field k'] (β : k →+* k') {X X' : Scheme.{0}}
    (f : X ⟶ Sp k) [IsProper f] [GeometricallyIntegral f] (π : X' ⟶ X) (p : X' ⟶ Sp k')
    (H : IsPullback π p f (spMap β)) {N : LB X} (hN : N.IsLB) (t : (N.pull π).Gen) (ht : t.IsGen) :
    ∃ u : N.Gen, u.IsGen := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_baseChange_of_field H
  have hflat : β.Flat := by
    let _ := β.toAlgebra
    exact inferInstanceAs (Module.Flat k k')
  have lift : ∀ x : X, ∃ y, π y = x := fun x => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k')
      (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    exact ⟨y, hy⟩
  obtain ⟨σ, hσ⟩ := GenericTriv.exists_sec_isUnit β hflat f π p H
    (ConcreteCategory.bijective_of_isIso p.appTop).2 hN t ht
  have hu : ∀ i, IsUnit (σ.f i) := fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    obtain ⟨y, rfl⟩ := lift x
    have := hσ y i hx
    rw [gs_stalkMap π y _ hx, isUnit_map_iff] at this
    exact (congrArg IsUnit (gs_eq (𝟙 X) (π y) (N.U i) hx _)).mp this
  exact ⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (σ.compat i i')⟩

/- English proof (translation)
Introduce `k k' _ _ β A _ hA X' π p H N hN ⟨t, ht⟩`. Use `hA.proper` as an intermediate fact. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact. Conclude with `exists_gen_of_isPullback β A.hom π p H hN t ht`.
-/
theorem exists_gen_of_field_extension : ∀ (k k' : Type) [Field k] [Field k'] (β : k →+* k') (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k'), IsPullback π p A.hom (spMap β) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro k k' _ _ β A _ hA X' π p H N hN ⟨t, ht⟩
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  exact exists_gen_of_isPullback β A.hom π p H hN t ht

end GlobalTheory.FieldTriv
