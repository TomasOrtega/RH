import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteMulByNatAbelianVarietyAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.MulFiniteFlat

open GlobalTheory.AbLaw.MulN

/- English proof (translation)
Set `K` to `AlgebraicClosure (Y.left.residueField y)`. Set `u : Spec (CommRingCat.of K) ⟶ Y.left` to `Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫ Y.left.fromSpecResidueField y`. Set `t` to `u ≫ Y.hom`. Establish `hs` using `h K t`. Set `p : Spec (CommRingCat.of K)` to `(⊥ : PrimeSpectrum K)`.

Set `v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t` to `pullback.lift u (𝟙 _) (by simp [t])`. Establish `hv : pullback.fst Y.hom t (v p) = y`. Rewrite using `[← Scheme.Hom.comp_apply]`. Establish `: v ≫ pullback.fst Y.hom t = u` using `pullback.lift_fst _ _ _`. Rewrite using `[this]`.

Conclude with `(Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)`. Establish `hfin` using `((Over.pullback t).map f).left.finite_preimage_singleton (v p)`. Use `(hfin.image (pullback.fst X.hom t)).subset fun x hx => ?_` and prove the remaining obligations. Take `⟨z, hz₁, hz₂⟩` from `Scheme.exists_preimage_of_isPullback (isPullback_baseChange t f) x (v p) ((show f.left x = y from hx).trans hv.symm)`. Conclude with `⟨z, hz₂, hz₁⟩`.
-/
theorem finite_preimage_of_geomFibres {S : Scheme.{0}} {X Y : Over S} (f : X ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map f).left) (y : Y.left) : (f.left ⁻¹' {y}).Finite := by
  let K := AlgebraicClosure (Y.left.residueField y)
  let u : Spec (CommRingCat.of K) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.left.residueField y) K)) ≫
      Y.left.fromSpecResidueField y
  let t := u ≫ Y.hom
  have hs := h K t
  let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  let v : Spec (CommRingCat.of K) ⟶ pullback Y.hom t := pullback.lift u (𝟙 _) (by simp [t])
  have hv : pullback.fst Y.hom t (v p) = y := by
    rw [← Scheme.Hom.comp_apply]
    have : v ≫ pullback.fst Y.hom t = u := pullback.lift_fst _ _ _
    rw [this]
    exact (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply y _)
  have hfin := ((Over.pullback t).map f).left.finite_preimage_singleton (v p)
  refine (hfin.image (pullback.fst X.hom t)).subset fun x hx => ?_
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback (isPullback_baseChange t f) x (v p)
    ((show f.left x = y from hx).trans hv.symm)
  exact ⟨z, hz₂, hz₁⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Over.pullback t).map (𝟙 A ^ n) = 𝟙 _ ^ n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, Functor.map_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, CategoryTheory.Functor.map_id]`.
-/
theorem pullback_map_mulA {S T : Scheme.{0}} (t : T ⟶ S) (A : Over S) [GrpObj A] (n : ℕ) :
    (Over.pullback t).map (mulA A n) = mulA ((Over.pullback t).obj A) n := by
  change (Over.pullback t).map (𝟙 A ^ n) = 𝟙 _ ^ n
  induction n with
  | zero => rw [pow_zero, pow_zero, Functor.map_one]
  | succ n ih => rw [pow_succ, pow_succ, Functor.map_mul, ih, CategoryTheory.Functor.map_id]

/- English proof (translation)
Introduce `S _ A _ _ hA k hk`. Express the relevant statement in the definitionally equal form `IsFinite (mulA A k).left ∧ Flat (mulA A k).left`. Establish `hsm` using `hA.smooth`. Establish `hpr` using `hA.proper`. Establish `hm` using `isMonHom_mulA A k`.

Establish `hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), IsFinite ((Over.pullback t).map (mulA A k)).left` using `fun K _ _ t => by`. Rewrite using `[pullback_map_mulA]`. Conclude with `GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk`. Establish `h1 : IsProper ((mulA A k).left ≫ A.hom)` using `by rw [Over.w]; exact hpr`. Establish `h2 : IsProper (mulA A k).left` using `IsProper.of_comp _ A.hom`.

Establish `h3 : LocallyQuasiFinite (mulA A k).left` using `LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_of_geomFibres _ hg)`. Establish `hf : IsFinite (mulA A k).left` using `.of_isProper_of_locallyQuasiFinite _`. Use `⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance hf fun K _ _ t => ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _ (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1`.
-/
theorem isFinite_and_flat_mul : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 A) ^ k : A ⟶ A).left ∧ Flat ((𝟙 A) ^ k : A ⟶ A).left := by
  intro S _ A _ _ hA k hk
  change IsFinite (mulA A k).left ∧ Flat (mulA A k).left
  have hsm := hA.smooth
  have hpr := hA.proper
  have hm := isMonHom_mulA A k
  have hg : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      IsFinite ((Over.pullback t).map (mulA A k)).left := fun K _ _ t => by
    rw [pullback_map_mulA]
    exact GlobalTheory.MulFiniteAny.isFinite_mulA K _ (TLinPf.isAb_pullback t A hA) k hk
  have h1 : IsProper ((mulA A k).left ≫ A.hom) := by rw [Over.w]; exact hpr
  have h2 : IsProper (mulA A k).left := IsProper.of_comp _ A.hom
  have h3 : LocallyQuasiFinite (mulA A k).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_of_geomFibres _ hg)
  have hf : IsFinite (mulA A k).left := .of_isProper_of_locallyQuasiFinite _
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance hf
    fun K _ _ t => ?_⟩
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (TLinPf.isAb_pullback t A hA) _ inferInstance (hg K t)).1

end GlobalTheory.MulFiniteFlat
