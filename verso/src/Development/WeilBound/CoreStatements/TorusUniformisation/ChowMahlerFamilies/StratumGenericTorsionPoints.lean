import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTorusExtensionFinite
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionMulCardToricTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.StratumGenericTorsion

noncomputable def rk {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (τ : TorusExtension G) : ℕ :=
  letI := τ.addCommGroup; Module.finrank ℤ τ.X

/- English proof (translation)
Use `haveI : IsMonHom (pullCompIso (spMap e) x G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso (spMap e) x G).inv)`. Conclude with `⟨torusExtOfIso (pullCompIso (spMap e) x G).symm (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC (spMap e) τ), rfl⟩`.
-/
theorem exists_ext {S : Scheme.{0}} (G : Over S) [GrpObj G] {K K' : Type} [Field K] [Field K'] (x : Sp K ⟶ S)
    (τ : TorusExtension ((Over.pullback x).obj G)) (e : K →+* K') :
    ∃ τ' : TorusExtension ((Over.pullback (spMap e ≫ x)).obj G), rk τ' = rk τ := by
  haveI : IsMonHom (pullCompIso (spMap e) x G).symm.hom :=
    inferInstanceAs (IsMonHom (pullCompIso (spMap e) x G).inv)
  exact ⟨torusExtOfIso (pullCompIso (spMap e) x G).symm
    (GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC.torusExtBC (spMap e) τ), rfl⟩

/- English proof (translation)
Rewrite using `[← GlobalTheory.card_torsion_mul_card_toric_torsion k G E g 2 hG dG h2]`. Use `congr 1`. Use `letI := E.addCommGroup`. Use `letI := E.grpB`. Use `haveI := E.free`.

Use `haveI := E.finite`. Use `haveI := E.i_hom`. Establish `hk` using `E.isKernel`. Take `⟨e⟩` from `GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X`. Take `⟨-, hcard⟩` from `GlobalTheory.SemiAbTorsionCount.divisible_and_card e 2 h2`.

Set `i` to `IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))`. Establish `hi : Function.Injective i` using `fun a b h => hk.hom_ext h (toUnit_unique _ _)`. Use `hcard.symm.trans ?_` and prove the remaining obligations. Use `Nat.card_eq_of_bijective (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`.

Conclude with `Subtype.ext (hi (congrArg Subtype.val h))`. Introduce and unpack `⟨x, hx, t, rfl⟩`. Establish `hx₁ : i t ^ 2 = 1` using `hx`. Conclude with `⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩`.
-/
theorem card_field (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ)
    (hG : IsSemiAbelian G) (dG : SmoothOfRelativeDimension g G.hom) (h2 : ((2 : ℕ) : k) ≠ 0) :
    Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ 2 = 1} * 2 ^ rk E = 2 ^ (2 * g) := by
  rw [← GlobalTheory.card_torsion_mul_card_toric_torsion k G E g 2 hG dG h2]
  congr 1
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  have hk := E.isKernel
  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k E.X
  obtain ⟨-, hcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e 2 h2
  let i := IsMonHom.monoidHom E.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  refine hcard.symm.trans ?_
  refine Nat.card_eq_of_bijective
    (fun t => ⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (hi (congrArg Subtype.val h))
  · rintro ⟨x, hx, t, rfl⟩
    have hx₁ : i t ^ 2 = 1 := hx
    exact ⟨⟨t, hi (by rw [map_pow, hx₁, map_one])⟩, rfl⟩

/- English proof (translation)
Establish `hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) dG`. Rewrite using `[← card_field k _ E g (IsSemiAbelian.pullback t G hG) hg' h2]`. Use `congr 1`. Set `e` to `GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp k))) t (Category.id_comp t)`. Use `(Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations.

Use `show x ^ 2 = 1 ↔ e x ^ 2 = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`.
-/
theorem card_point {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (k : Type) [Field k] [IsAlgClosed k] (h2 : ((2 : ℕ) : k) ≠ 0)
    (t : Sp k ⟶ S) (E : TorusExtension ((Over.pullback t).obj G)) :
    Nat.card {x : Over.mk t ⟶ G // x ^ 2 = 1} * 2 ^ rk E = 2 ^ (2 * g) := by
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) dG
  rw [← card_field k _ E g (IsSemiAbelian.pullback t G hG) hg' h2]
  congr 1
  let e := GlobalTheory.TorsionLift.ptsEquiv t G (𝟙_ (Over (Sp k))) t (Category.id_comp t)
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ 2 = 1 ↔ e x ^ 2 = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

/- English proof (translation)
Set `F` to `AlgebraicClosure K`. Use `haveI := hG.smooth`. Take `⟨τF, hτF⟩` from `exists_ext G x τ (algebraMap K F)`. Establish `hc` using `card_point G hG g dG F (by exact_mod_cast (two_ne_zero : (2 : F) ≠ 0)) _ τF`. Rewrite `hc` using `[hτF]`.

Establish `hne : Nat.card {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1} ≠ 0`. Introduce `h0`. Rewrite `hc` using `[h0, zero_mul]`. Conclude with `(pow_ne_zero _ two_ne_zero) hc.symm`. Use `haveI := Nat.finite_of_card_ne_zero hne`.

Set `u` to `(Finite.equivFin {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1}).symm`. Use `choose T hT using fun j => GlobalTheory.TorsionRat.exists_finset_over G x (u j).1`. Set `s : Set F` to `⋃ j, (T j : Set F)`. Use `haveI : Finite s := (Set.finite_iUnion fun j => (T j).finite_toSet).to_subtype`. Set `L` to `IntermediateField.adjoin K s`.

Use `⟨L, inferInstance, inferInstance, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩` and prove the remaining obligations. Introduce and unpack `y rfl`. Take `⟨τ', hτ'⟩` from `exists_ext G x τ (algebraMap K L)`. Use `choose P hP using fun j => hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))`. Set `c₀ : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ Over.mk (spMap (algebraMap K L) ≫ x)` to `Over.homMk (spMap (algebraMap L F)) (by`.

Express the relevant statement in the definitionally equal form `spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x = spMap (algebraMap K F) ≫ x`. Rewrite using `[← Category.assoc, GlobalTheory.TorsionRat.sp_comp]`. Use the proof step `rfl)`. Establish `hc₀ : ∀ j, c₀ ≫ P j = (u j).1` using `fun j => Over.OverMorphism.ext (hP j)`. Use `⟨τ', _, P, fun a b h => u.injective (Subtype.ext ?_), fun j => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc₀, ← hc₀, h]`. Use `GlobalTheory.TorsionRat.comp_injective (algebraMap L F) c₀ rfl ?_` and prove the remaining obligations. Rewrite using `[MonObj.comp_pow, hc₀, (u j).2, MonObj.comp_one]`. Rewrite using `[hτ']`. Conclude with `hc`.
-/
theorem exists_points {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (dG : SmoothOfRelativeDimension g G.hom) (K : Type) [Field K] [CharZero K] (x : Sp K ⟶ S)
    (τ : TorusExtension ((Over.pullback x).obj G)) :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), FiniteDimensional K K' ∧
      ∀ y : Sp K' ⟶ S, y = spMap (algebraMap K K') ≫ x →
        ∃ (τ' : TorusExtension ((Over.pullback y).obj G)) (m : ℕ) (P : Fin m → (Over.mk y ⟶ G)),
          Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ m * 2 ^ rk τ' = 2 ^ (2 * g) := by
  let F := AlgebraicClosure K
  haveI := hG.smooth
  obtain ⟨τF, hτF⟩ := exists_ext G x τ (algebraMap K F)
  have hc := card_point G hG g dG F (by exact_mod_cast (two_ne_zero : (2 : F) ≠ 0)) _ τF
  rw [hτF] at hc
  have hne : Nat.card {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc
    exact (pow_ne_zero _ two_ne_zero) hc.symm
  haveI := Nat.finite_of_card_ne_zero hne
  let u := (Finite.equivFin {p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G // p ^ 2 = 1}).symm
  choose T hT using fun j => GlobalTheory.TorsionRat.exists_finset_over G x (u j).1
  let s : Set F := ⋃ j, (T j : Set F)
  haveI : Finite s := (Set.finite_iUnion fun j => (T j).finite_toSet).to_subtype
  let L := IntermediateField.adjoin K s
  refine ⟨L, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  rintro y rfl
  obtain ⟨τ', hτ'⟩ := exists_ext G x τ (algebraMap K L)
  choose P hP using fun j =>
    hT j L ((Set.subset_iUnion (fun j => (T j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))
  let c₀ : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ Over.mk (spMap (algebraMap K L) ≫ x) :=
    Over.homMk (spMap (algebraMap L F)) (by
      change spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x = spMap (algebraMap K F) ≫ x
      rw [← Category.assoc, GlobalTheory.TorsionRat.sp_comp]
      rfl)
  have hc₀ : ∀ j, c₀ ≫ P j = (u j).1 := fun j => Over.OverMorphism.ext (hP j)
  refine ⟨τ', _, P, fun a b h => u.injective (Subtype.ext ?_), fun j => ?_, ?_⟩
  · rw [← hc₀, ← hc₀, h]
  · refine GlobalTheory.TorsionRat.comp_injective (algebraMap L F) c₀ rfl ?_
    rw [MonObj.comp_pow, hc₀, (u j).2, MonObj.comp_one]
  · rw [hτ']
    exact hc

end PositivityTheory.Xgn.StratumGenericTorsion

open PositivityTheory.Xgn.StratumGenericTorsion in
/- English proof (translation)
Introduce `S G _ hG g dG L _ _ z`. Take `⟨L₁, _, _, h₁, ⟨τ₁⟩⟩` from `exists_finite_torusExtension_fibre S G hG L z`. Use `haveI : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap L L₁).injective`. Take `⟨K, _, _, h₂, H⟩` from `exists_points G hG g dG L₁ _ τ₁`. Use `letI : Algebra L K := ((algebraMap L₁ K).comp (algebraMap L L₁)).toAlgebra`.

Use `haveI : IsScalarTower L L₁ K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `⟨K, inferInstance, inferInstance, Module.Finite.trans L₁ K, ?_⟩` and prove the remaining obligations. Conclude with `H _ (by rw [← Category.assoc, GlobalTheory.TorsionRat.sp_comp])`.
-/
theorem PositivityTheory.Xgn.stratum_generic_torsion_points : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S), ∃ (L' : Type) (_ : Field L') (_ : Algebra L L'), FiniteDimensional L L' ∧ ∃ (τ : TorusExtension ((Over.pullback (spMap (algebraMap L L') ≫ z)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (spMap (algebraMap L L') ≫ z) ⟶ G)), Function.Injective P ∧ (∀ i, P i ^ 2 = 1) ∧ (letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) := by
  intro S G _ hG g dG L _ _ z
  obtain ⟨L₁, _, _, h₁, ⟨τ₁⟩⟩ := exists_finite_torusExtension_fibre S G hG L z
  haveI : CharZero L₁ := charZero_of_injective_algebraMap (algebraMap L L₁).injective
  obtain ⟨K, _, _, h₂, H⟩ := exists_points G hG g dG L₁ _ τ₁
  letI : Algebra L K := ((algebraMap L₁ K).comp (algebraMap L L₁)).toAlgebra
  haveI : IsScalarTower L L₁ K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨K, inferInstance, inferInstance, Module.Finite.trans L₁ K, ?_⟩
  exact H _ (by rw [← Category.assoc, GlobalTheory.TorsionRat.sp_comp])
