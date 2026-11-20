import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianUniformizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundleStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.ProjOverC

/- English proof (translation)
Introduce `F _ _ 𝔠 X c hc`. Establish `hL : (X.diag c).IsLB` using `LB.isLB_pull (X.isLB c) _`. Establish `hq : IsQProjOver (X.A.hom ≫ 𝟙 (Sp ℂ))` using `GlobalTheory.RelAmpleQProj.isQProjOver_of_relAmple ℂ (Sp ℂ) (𝟙 _) X.A (X.diag c) (GlobalTheory.ZM.OnePoint.isQProjOver_id ℂ) hL (X.pos c hc)`. Rewrite `hq` using `[Category.comp_id]`. Establish `hp : IsProper X.A.hom` using `X.ab.proper`.

Establish `: IsProper (𝟙 X.A.left ≫ X.A.hom)` using `by rw [Category.id_comp]; exact hp`. Establish `h` using `GlobalTheory.isProjOver_of_isProper_of_isImmersion (𝟙 X.A.left) hq`. Rewrite `h` using `[Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem isProjOver_A : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → IsProjOver X.A.hom := by
  intro F _ _ 𝔠 X c hc
  have hL : (X.diag c).IsLB := LB.isLB_pull (X.isLB c) _
  have hq : IsQProjOver (X.A.hom ≫ 𝟙 (Sp ℂ)) :=
    GlobalTheory.RelAmpleQProj.isQProjOver_of_relAmple ℂ (Sp ℂ) (𝟙 _) X.A (X.diag c)
      (GlobalTheory.ZM.OnePoint.isQProjOver_id ℂ) hL (X.pos c hc)
  rw [Category.comp_id] at hq
  have hp : IsProper X.A.hom := X.ab.proper
  have : IsProper (𝟙 X.A.left ≫ X.A.hom) := by rw [Category.id_comp]; exact hp
  have h := GlobalTheory.isProjOver_of_isProper_of_isImmersion (𝟙 X.A.left) hq
  rwa [Category.id_comp] at h

/- English proof (translation)
The claim follows from `isProjOver_A`.
-/
example : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → IsProjOver X.A.hom := isProjOver_A

end GlobalTheory.RealMult.ProjOverC
