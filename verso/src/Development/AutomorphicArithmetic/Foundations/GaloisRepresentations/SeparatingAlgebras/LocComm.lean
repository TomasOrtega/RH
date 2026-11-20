import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `E _ _ _ a w₀ x g hx hg`. Take `⟨hxf, hxa⟩` from `(GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx`. Establish `hxi : cInf x = 1` using `hxf`. Use `Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cInf (x * g) = cInf (g * x)`.

Rewrite using `[map_mul, map_mul, hxi, one_mul, mul_one]`. Express the relevant statement in the definitionally equal form `cLoc u (x * g) = cLoc u (g * x)`. Rewrite using `[map_mul, map_mul]`. Distinguish the cases in `hu : Apart u w₀`. Rewrite using `[hxa u hu, one_mul, mul_one]`.

Rewrite using `[hg u hu, one_mul, mul_one]`.
-/
theorem UpperTheory.Gal.Gen.locComm_pf :
    UpperTheory.Gal.Gen.LocComm := by
  intro E _ _ _ a w₀ x g hx hg
  obtain ⟨hxf, hxa⟩ := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  have hxi : cInf x = 1 := hxf
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
  · change cInf (x * g) = cInf (g * x)
    rw [map_mul, map_mul, hxi, one_mul, mul_one]
  · change cLoc u (x * g) = cLoc u (g * x)
    rw [map_mul, map_mul]
    by_cases hu : Apart u w₀
    · rw [hxa u hu, one_mul, mul_one]
    · rw [hg u hu, one_mul, mul_one]
