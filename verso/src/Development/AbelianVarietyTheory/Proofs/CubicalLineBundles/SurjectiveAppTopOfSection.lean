import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.TrivDedekind

/- English proof (translation)
Establish `hF : IsField Γ(Y, ⊤)` using `isField_of_universallyClosed K p`. Set `_` to `hF.toField`. Establish `hinj : Function.Injective e.appTop.hom` using `e.appTop.hom.injective`. Establish `hc : ∀ a, e.appTop.hom (p.appTop.hom a) = a` using `fun a => by`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]`.

Simplify using the standard rewrite rules. Conclude with `fun c => ⟨e.appTop.hom c, hinj (hc _)⟩`.
-/
theorem surjective_appTop_of_section {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp K)
    [UniversallyClosed p] (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) : Function.Surjective p.appTop.hom := by
  have hF : IsField Γ(Y, ⊤) := isField_of_universallyClosed K p
  let _ := hF.toField
  have hinj : Function.Injective e.appTop.hom := e.appTop.hom.injective
  have hc : ∀ a, e.appTop.hom (p.appTop.hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    simp
  exact fun c => ⟨e.appTop.hom c, hinj (hc _)⟩

/- English proof (translation)
Introduce `R K _ _ _ _ _ A _ hA X' π p H N hN ⟨ρ, hρ⟩ ⟨t, ht⟩`. Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact. Establish `: CompactSpace A.left` using `QuasiCompact.compactSpace_of_compactSpace A.hom`.

Establish `: QuasiSeparatedSpace A.left` using `quasiSeparatedSpace_of_quasiSeparated A.hom`. Establish `: IsIntegral X'` using `DvrModel.isIntegral_of_geometricallyIntegral H`. Establish `: UniversallyClosed p` using `MorphismProperty.of_isPullback H inferInstance`. Establish `he : eSec A ≫ A.hom = 𝟙 _` using `Over.w η[A]`. Conclude with `GenericTriv.exists_gen_of_fibre (algebraMap R K) (IsFractionRing.injective R K) A.hom (eSec A) he π p H (surjective_appTop_of_section p (H.lift (spMap (algebraMap R K) ≫ eSec A) (𝟙 _) (by rw [Category.assoc, he]; simp)) (H.lift_snd _ _ _)) hN ρ hρ t ht`.
-/
theorem exists_gen_of_generic : ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp K), IsPullback π p A.hom (spMap (algebraMap R K)) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull (eSec A)), t.IsGen) → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R K _ _ _ _ _ A _ hA X' π p H N hN ⟨ρ, hρ⟩ ⟨t, ht⟩
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have : IsIntegral X' := DvrModel.isIntegral_of_geometricallyIntegral H
  have : UniversallyClosed p := MorphismProperty.of_isPullback H inferInstance
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w η[A]
  exact GenericTriv.exists_gen_of_fibre (algebraMap R K) (IsFractionRing.injective R K) A.hom (eSec A) he π p H
    (surjective_appTop_of_section p (H.lift (spMap (algebraMap R K) ≫ eSec A) (𝟙 _)
      (by rw [Category.assoc, he]; simp)) (H.lift_snd _ _ _)) hN ρ hρ t ht

end GlobalTheory.TrivDedekind
