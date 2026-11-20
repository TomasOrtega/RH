import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParameterOfLocalLanglands
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
set_option maxHeartbeats 4000000 in
/- English proof (translation)
Take `⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩` from `nt`. Substitute `eq` using the available equality. Establish `e1 : Rw.locR = A.row.locR` using `eq_of_heq hRw`. Introduce `i σ w`. Rewrite using `[e1]`.

Conclude with `Au.locW i σ w`.
-/
theorem locW_of_nTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    ∀ i σ w, D'.naut.locW i σ w = Rw.locR σ w := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  intro i σ w
  rw [e1]
  exact Au.locW i σ w
end GlobalTheory.GalLoc.RowParamAt
end
