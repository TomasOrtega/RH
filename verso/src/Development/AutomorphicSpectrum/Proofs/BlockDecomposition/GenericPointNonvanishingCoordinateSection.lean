import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoheightEqOneOfDimClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DimOfIsArithVar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldMapPtCoordSndM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog IsRelevant IsMultiProjPrime divSupp multAt geoNum charOf)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ GlobalTheory GlobalTheory.ProjBlowup

namespace GlobalTheory.CompanionTheory.MixZ.VertGen

/- English proof (translation)
Unfold `GlobalTheory.ProjBlowup.pullForm GlobalTheory.ProjSpace.pullRatio GlobalTheory.ProjSpace.formOn GlobalTheory.ProjSpace.ratio GlobalTheory.ProjSpace.ratioOn`. Use `congr 1`. Use `congr 1`. Conclude with `pow_one _`.
-/
private theorem pullForm_X_eq_pullRatio {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace ℤ N) (W : Y.Opens)
    (i : Fin (N + 1)) (hi : W ≤ (Opens.map φ.base).obj (GlobalTheory.ProjSpace.chart ℤ N i)) (l : Fin (N + 1))
    (h : (MvPolynomial.X l : MvPolynomial (Fin (N + 1)) ℤ).IsHomogeneous 1) :
    GlobalTheory.ProjBlowup.pullForm φ W i hi 1 (MvPolynomial.X l) h = GlobalTheory.ProjSpace.pullRatio φ W i hi l := by
  unfold GlobalTheory.ProjBlowup.pullForm GlobalTheory.ProjSpace.pullRatio GlobalTheory.ProjSpace.formOn GlobalTheory.ProjSpace.ratio
    GlobalTheory.ProjSpace.ratioOn
  congr 1
  congr 1
  exact pow_one _

/- English proof (translation)
Introduce `m n Z _ f _ k l hX`. Establish `hxj` using `GlobalTheory.CompanionTheory.MPDict.mem_ptChart (f (genericPoint Z)) k`. Establish `hne : GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩ ≠ 0`. Introduce `h0`. Apply `hX` to reduce the goal to its premises.

Use `show (MvPolynomial.X ⟨k, l⟩ : Pol n) ∈ RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z))))`. Rewrite using `[RingHom.mem_ker]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h0]`. Set `j : (pullO (f ≫ prB n k) 1).ι` to `(GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k : Fin (n k + 1))`. Establish `hξ : genericPoint Z ∈ (pullO (f ≫ prB n k) 1).U j` using `hxj`.

Apply `GlobalTheory.basicOpen_le_nonzeroLocus _ j` to reduce the goal to its premises. Use `(Scheme.evaluation_ne_zero_iff_mem_basicOpen Z (genericPoint Z) hξ _).mp ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.ProjBlowup.pullFormSec]`. Establish `hle : (pullO (f ≫ prB n k) 1).U j ≤ (Opens.map (f ≫ prB n k).base).obj (GlobalTheory.ProjSpace.chart ℤ (n k) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k))` using `le_rfl`. Establish `e` using `pullForm_X_eq_pullRatio (f ≫ prB n k) ((pullO (f ≫ prB n k) 1).U j) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hle l (isHomogeneous_X ℤ l)`.

Establish `key` using `GlobalTheory.CompanionTheory.MPDict.FnDeg.eval_pullRatio_comp f (prB n k) (genericPoint Z) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hxj l`. Establish `h2 : (CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap f (genericPoint Z))) (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩) ≠ 0` using `(map_ne_zero _).mpr hne`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use `Eq.trans ?_ key.symm` and prove the remaining obligations. Conclude with `congrArg (ConcreteCategory.hom (Z.evaluation _ (genericPoint Z) hξ)) e`.
-/
theorem genericPoint_mem_nonzeroLocus : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ MP ℤ m n) [IsClosedImmersion f] (k : Fin (m + 1)) (l : Bk n k), (X ⟨k, l⟩ : Pol n) ∉ ptIdeal (f (genericPoint Z)) → genericPoint Z ∈ Out.nonzeroLocus (pullFormSec (f ≫ prB n k) (X l) (isHomogeneous_X ℤ l)) := by
  intro m n Z _ f _ k l hX
  have hxj := GlobalTheory.CompanionTheory.MPDict.mem_ptChart (f (genericPoint Z)) k
  have hne : GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩ ≠ 0 := by
    intro h0
    apply hX
    show (MvPolynomial.X ⟨k, l⟩ : Pol n) ∈
      RingHom.ker (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z))))
    rw [RingHom.mem_ker]
    simp [ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, h0]
  let j : (pullO (f ≫ prB n k) 1).ι := (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k : Fin (n k + 1))
  have hξ : genericPoint Z ∈ (pullO (f ≫ prB n k) 1).U j := hxj
  apply GlobalTheory.basicOpen_le_nonzeroLocus _ j
  refine (Scheme.evaluation_ne_zero_iff_mem_basicOpen Z (genericPoint Z) hξ _).mp ?_
  dsimp only [GlobalTheory.ProjBlowup.pullFormSec]
  have hle : (pullO (f ≫ prB n k) 1).U j ≤
      (Opens.map (f ≫ prB n k).base).obj (GlobalTheory.ProjSpace.chart ℤ (n k) (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k)) :=
    le_rfl
  have e := pullForm_X_eq_pullRatio (f ≫ prB n k) ((pullO (f ≫ prB n k) 1).U j)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hle l (isHomogeneous_X ℤ l)
  have key := GlobalTheory.CompanionTheory.MPDict.FnDeg.eval_pullRatio_comp f (prB n k) (genericPoint Z)
    (GlobalTheory.CompanionTheory.MPDict.ptChart (f (genericPoint Z)) k) hxj l
  have h2 : (CommRingCat.Hom.hom (Scheme.Hom.residueFieldMap f (genericPoint Z)))
      (GlobalTheory.CompanionTheory.MPDict.ptCoord (f (genericPoint Z)) ⟨k, l⟩) ≠ 0 := (map_ne_zero _).mpr hne
  convert h2 using 1
  refine Eq.trans ?_ key.symm
  exact congrArg (ConcreteCategory.hom (Z.evaluation _ (genericPoint Z) hξ)) e

end GlobalTheory.CompanionTheory.MixZ.VertGen
