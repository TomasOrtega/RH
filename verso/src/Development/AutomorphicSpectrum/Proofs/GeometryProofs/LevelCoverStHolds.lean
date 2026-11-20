import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LevelCoverSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullLevelFiniteExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteNormalModelOfResidueFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCoverStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictIntStatement

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.XR

/- English proof (translation)
Unfold `genPt`. Use `show ξ ((spMap i) (closedPoint Ω)) = ξ (closedPoint K)`. Use `congr 1`. Use `first`. Consider the case `exact Subsingleton.elim _ _`.

Consider the case `exact IsLocalRing.comap_closedPoint i`. Consider the case `exact (IsLocalRing.PrimeSpectrum.comap_closedPoint i)`.
-/
theorem genPt_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (ξ : Sp K ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ := by
  unfold genPt
  show ξ ((spMap i) (closedPoint Ω)) = ξ (closedPoint K)
  congr 1
  first
  | exact Subsingleton.elim _ _
  | exact IsLocalRing.comap_closedPoint i
  | exact (IsLocalRing.PrimeSpectrum.comap_closedPoint i)

/- English proof (translation)
Establish `hA : ∀ p : Sp K, (ξ.stalkMap p).hom.Finite`. Introduce `p`. Take `rfl : p = closedPoint K` from `Subsingleton.elim _ _`. Apply `RingHom.Finite.of_surjective` to reduce the goal to its premises. Establish `e : Scheme.stalkClosedPointTo ξ = ξ.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (CommRingCat.of K)).hom` using `by first`.

Consider the case `rfl`. Consider the case `simp [Scheme.stalkClosedPointTo]`. Introduce `y`. Take `⟨a, ha⟩` from `hξ ((stalkClosedPointIso (CommRingCat.of K)).hom y)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Apply `(ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1` to reduce the goal to its premises. Rewrite using `[← ha, e]`. Both sides reduce to the same expression. Establish `hB : (Scheme.stalkClosedPointTo (spMap i)).hom.Finite`. Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i))).hom.Finite`.

Establish `h` using `Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom i)`. Use `RingHom.Finite.of_comp_finite (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).presheaf.germ ⊤ ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) trivial).hom) ?_` and prove the remaining obligations. Rewrite using `[← CommRingCat.hom_comp, Category.assoc, h, Iso.inv_hom_id_assoc]`. Simplify using `using hi`. Establish `hC : (Scheme.stalkClosedPointTo (spMap i ≫ ξ)).hom.Finite`.

Establish `e2` using `Scheme.stalkClosedPointTo_comp (R := CommRingCat.of Ω) (spMap i) ξ`. Establish `h3` using `hB.comp (hA ((spMap i) (closedPoint Ω)))`. Rewrite `h3` using `[← CommRingCat.hom_comp]`. Use `first`. Consider the case `exact e2 ▸ h3`.

Consider the case `exact (congrArg (fun φ => (CommRingCat.Hom.hom φ).Finite) e2).mpr h3`. Consider the case `(rw [e2]; exact h3)`. Use `RingHom.Finite.of_comp_finite (f := (X.residue _).hom) ?_` and prove the remaining obligations. Rewrite using `[← CommRingCat.hom_comp, Scheme.residue_descResidueField]`. Conclude with `hC`.
-/
theorem finite_descResidueField_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω)
    (hi : i.Finite) (ξ : Sp K ⟶ X) (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (spMap i ≫ ξ))).hom.Finite := by
  have hA : ∀ p : Sp K, (ξ.stalkMap p).hom.Finite := by
    intro p
    obtain rfl : p = closedPoint K := Subsingleton.elim _ _
    apply RingHom.Finite.of_surjective
    have e : Scheme.stalkClosedPointTo ξ =
        ξ.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (CommRingCat.of K)).hom := by
      first
      | rfl
      | simp [Scheme.stalkClosedPointTo]
    intro y
    obtain ⟨a, ha⟩ := hξ ((stalkClosedPointIso (CommRingCat.of K)).hom y)
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1
    rw [← ha, e]
    rfl
  have hB : (Scheme.stalkClosedPointTo (spMap i)).hom.Finite := by
    change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i))).hom.Finite
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom i)
    refine RingHom.Finite.of_comp_finite
      (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) trivial).hom) ?_
    rw [← CommRingCat.hom_comp, Category.assoc, h, Iso.inv_hom_id_assoc]
    simpa using hi
  have hC : (Scheme.stalkClosedPointTo (spMap i ≫ ξ)).hom.Finite := by
    have e2 := Scheme.stalkClosedPointTo_comp (R := CommRingCat.of Ω) (spMap i) ξ
    have h3 := hB.comp (hA ((spMap i) (closedPoint Ω)))
    rw [← CommRingCat.hom_comp] at h3
    first
    | exact e2 ▸ h3
    | exact (congrArg (fun φ => (CommRingCat.Hom.hom φ).Finite) e2).mpr h3
    | (rw [e2]; exact h3)
  refine RingHom.Finite.of_comp_finite (f := (X.residue _).hom) ?_
  rw [← CommRingCat.hom_comp, Scheme.residue_descResidueField]
  exact hC

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y e he N hN`. Take `⟨K, _, _, n0, x0, y0, htie, -, hgen⟩` from `GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y e he`. Take `⟨Ω, _, _, z, ev, hfd, hfull⟩` from `GlobalTheory.T.exists_full_level_finite_extension E H D l Xo c _ _ Y K y0 N hN`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective`. Use `haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }`.

Establish `hproj : IsProjOver (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F)))` using `GlobalTheory.T.projective_over_restrict_int _ Y.X Y.s Y.proj`. Establish `hsurj : Function.Surjective (Scheme.stalkClosedPointTo (y0 ≫ Y.j)).hom`. Take `⟨hg, -, -, -⟩` from `htie`. Take `⟨hb, -⟩` from `hg`. Conclude with `hb.2`.

Establish `hi : (algebraMap K Ω).Finite` using `by first`. Consider the case `exact RingHom.finite_algebraMap.mpr hfd`. Consider the case `exact hfd`. Establish `hfin` using `finite_descResidueField_spMap_comp (algebraMap K Ω) hi (y0 ≫ Y.j) hsurj`. Take `⟨n, x, M, π, hMn, hπ, hMπ⟩` from `GlobalTheory.T.exists_finite_normal_model_of_residue_finite Y.X _ hproj Ω (spMap (algebraMap K Ω) ≫ (y0 ≫ Y.j)) hfin`.

Establish `hMg : IsCptGen M.ξ`. Take `⟨hg, -, -, -⟩` from `M.tie`. Conclude with `hg`. Take `⟨t, hx, ev', h1, h2, h3⟩` from `GlobalTheory.T.full_level_generic_cover E H D l Xo c Y K Ω (algebraMap K Ω) y0 N z ev hN hfull M.X M.ξ hMg hMn π hMπ`. Use `⟨Ω, inferInstance, inferInstance, n, x, M, π, spMap (algebraMap K Ω) ≫ y0, t, hx, z, ev', hMn, hπ, ?_, ?_, h1, h2, h3⟩` and prove the remaining obligations.

Use `show genPt (M.ξ ≫ π) = e`. Rewrite using `[hMπ, genPt_spMap_comp, hgen]`. Rewrite using `[hMπ, Category.assoc]`.
-/
theorem levelCover : LevelCoverSt := by
  intro E _ _ _ H D l Xo c Y e he N hN
  obtain ⟨K, _, _, n0, x0, y0, htie, -, hgen⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y e he
  obtain ⟨Ω, _, _, z, ev, hfd, hfull⟩ := GlobalTheory.T.exists_full_level_finite_extension E H D l Xo c _ _ Y K y0 N hN
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : NumberField c.F :=
    { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hproj : IsProjOver (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F))) :=
    GlobalTheory.T.projective_over_restrict_int _ Y.X Y.s Y.proj
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo (y0 ≫ Y.j)).hom := by
    obtain ⟨hg, -, -, -⟩ := htie
    obtain ⟨hb, -⟩ := hg
    exact hb.2
  have hi : (algebraMap K Ω).Finite := by
    first
    | exact RingHom.finite_algebraMap.mpr hfd
    | exact hfd
  have hfin := finite_descResidueField_spMap_comp (algebraMap K Ω) hi (y0 ≫ Y.j) hsurj
  obtain ⟨n, x, M, π, hMn, hπ, hMπ⟩ :=
    GlobalTheory.T.exists_finite_normal_model_of_residue_finite Y.X _ hproj Ω (spMap (algebraMap K Ω) ≫ (y0 ≫ Y.j)) hfin
  have hMg : IsCptGen M.ξ := by
    obtain ⟨hg, -, -, -⟩ := M.tie
    exact hg
  obtain ⟨t, hx, ev', h1, h2, h3⟩ :=
    GlobalTheory.T.full_level_generic_cover E H D l Xo c Y K Ω (algebraMap K Ω) y0 N z ev hN hfull M.X M.ξ hMg hMn π hMπ
  refine ⟨Ω, inferInstance, inferInstance, n, x, M, π, spMap (algebraMap K Ω) ≫ y0, t, hx, z, ev',
    hMn, hπ, ?_, ?_, h1, h2, h3⟩
  · show genPt (M.ξ ≫ π) = e
    rw [hMπ, genPt_spMap_comp, hgen]
  · rw [hMπ, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.XR
