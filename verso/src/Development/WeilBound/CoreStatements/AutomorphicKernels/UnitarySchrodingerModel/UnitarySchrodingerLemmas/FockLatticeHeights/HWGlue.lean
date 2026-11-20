import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `D n H hH θ hθ nb hnb w hw`. Use `⟨lstd D.host.F D.host.E n, (hL D.host.F D.host.E n).1, fun d bs => (hL D.host.F D.host.E n).2 d bs, ?_⟩` and prove the remaining obligations. Introduce `lam hlam b`. Take `⟨p, hp, k, hk, hpk⟩` from `GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb b)`. Take `⟨a, ha⟩` from `GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp`.

Establish `hH' : H (w * nb b) = absA D (Matrix.GeneralLinearGroup.det a)`. Rewrite using `[hpk]`. Conclude with `hH p hp a ha k hk`. Establish `hX : ((H (w * nb b) : ℝ≥0) : ℝ) = ((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w' (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) * ∏ᶠ v, ((GlobalTheory.Doubling.absEv D.host.F D.host …`. Rewrite using `[hH']`.

Express the relevant statement in the definitionally equal form `((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ≥0) : ℝ) = _`. Rewrite using `[GlobalTheory.Doubling.absE_apply, NNReal.coe_mul]`. Use `congr 1`. Conclude with `MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _`. Establish `h1` using `hI D n θ hθ w hw nb hnb b p k hp hk hpk a ha`.

Establish `h2` using `fun v => hF D n w hw nb hnb b p k hp hk hpk a ha v (lam v) (hlam v)`. Rewrite using `[hX, PositivityTheory.SiegelWeilFormula.Gen.nuA, finprod_congr h2, finprod_inv_distrib, mul_inv]`. Use `congr 1`. Conclude with `(eq_inv_of_mul_eq_one_right h1).symm`.
-/
theorem heightWN_of (hF : HWFin) (hI : HWInf) (hL : LstdStd) : PositivityTheory.PfSWUS.SwMatch.HeightWN := by
  intro D n H hH θ hθ nb hnb w hw
  refine ⟨lstd D.host.F D.host.E n, (hL D.host.F D.host.E n).1, fun d bs => (hL D.host.F D.host.E n).2 d bs, ?_⟩
  intro lam hlam b
  obtain ⟨p, hp, k, hk, hpk⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n (w * nb b)
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  have hH' : H (w * nb b) = absA D (Matrix.GeneralLinearGroup.det a) := by
    rw [hpk]; exact hH p hp a ha k hk
  have hX : ((H (w * nb b) : ℝ≥0) : ℝ) =
      ((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) *
      ∏ᶠ v, ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ) := by
    rw [hH']
    change ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ≥0) : ℝ) = _
    rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul]
    congr 1
    exact MonoidHom.map_finprod_of_injective NNReal.toRealHom.toMonoidHom NNReal.coe_injective _
  have h1 := hI D n θ hθ w hw nb hnb b p k hp hk hpk a ha
  have h2 := fun v => hF D n w hw nb hnb b p k hp hk hpk a ha v (lam v) (hlam v)
  rw [hX, PositivityTheory.SiegelWeilFormula.Gen.nuA, finprod_congr h2, finprod_inv_distrib, mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right h1).symm

end PositivityTheory.PfSWUS.SwFockk

end
