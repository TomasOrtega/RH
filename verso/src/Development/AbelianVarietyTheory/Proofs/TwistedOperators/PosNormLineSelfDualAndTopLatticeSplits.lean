import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthAtSumLatO
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCOfGramOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowShape

variable {D : D7}

/- English proof (translation)
Rewrite using `[pLine_gram]`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using `[antiDiagonalSignGramMatrix]`.

Both sides reduce to the same expression.
-/
theorem pLine_gram_eq_one : (pLine D).gram = 1 := by
  rw [pLine_gram]
  ext i j
  fin_cases i; fin_cases j
  simp [antiDiagonalSignGramMatrix]
  rfl

/- English proof (translation)
Simplify using `only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]`. Use `show _ ↔ ∀ k, IsIntegral ℤ (z k)`. Use `forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨b, hb⟩`. Rewrite using `[← hb]`.

Conclude with `b.2`.
-/
theorem mem_topL_iff (z : Fin (pLine D).rank → D.host.E) : z ∈ topL D ↔ z ∈ GlobalTheory.AdForm.intVec D (pLine D).rank := by
  simp only [topL, latPi, Submodule.mem_pi, Set.mem_univ, true_implies, FractionalIdeal.coe_one, Submodule.mem_one]
  show _ ↔ ∀ k, IsIntegral ℤ (z k)
  refine forall_congr' fun k => ⟨?_, fun h => ⟨⟨z k, h⟩, rfl⟩⟩
  rintro ⟨b, hb⟩
  rw [← hb]
  exact b.2

/- English proof (translation)
The claim follows from `GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff`.
-/
theorem isSelfDualC_topL : IsSelfDualC (pLine D) (topL D) :=
  GlobalTheory.LocMod.IntFrameStd.isSelfDualC_of_gram_one pLine_gram_eq_one _ mem_topL_iff

variable {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Establish `e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1)` using `G.sp.topLat`. Rewrite using `[e]`. Use extensionality with `x`. Rewrite using `[GlobalTheory.Core.Rk.SumBox.mem_sumLatO]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, u, hu, rfl⟩`. Conclude with `⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩`. Introduce and unpack `⟨y, hy, u, hu, rfl⟩`. Conclude with `⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩`.
-/
theorem topLat_eq_sumLatO (G : GridData L sc) :
    G.Λ (.top D.R.m) = GlobalTheory.Core.Rk.SumBox.sumLatO (topOrth G) (G.Λ (.grid D.R.m D.R.m)) (topL D) := by
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  rw [e]
  ext x
  rw [GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  constructor
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, Submodule.mem_pi.2 fun p _ => hu p, rfl⟩
  · rintro ⟨y, hy, u, hu, rfl⟩
    exact ⟨y, hy, u, fun p => Submodule.mem_pi.1 hu p (Set.mem_univ _), rfl⟩

/- English proof (translation)
Rewrite using `[topLat_eq_sumLatO G]`. Conclude with `GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v`.
-/
theorem topLat_orthAt (G : GridData L sc) (v : Pl D) :
    OrthAt (topOrth G) (G.Λ (.top D.R.m)) (G.Λ (.grid D.R.m D.R.m)) (topL D) v := by
  rw [topLat_eq_sumLatO G]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ (topOrth G) _ _ v

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩`.
-/
theorem topL_selfDual_orthAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.topL D) ∧
    ∀ v, GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) (GlobalTheory.RowShape.topL D) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ =>
    ⟨isSelfDualC_topL, fun v => topLat_orthAt ch.G v⟩⟩⟩

end GlobalTheory.RowShape
end
