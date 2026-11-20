import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceAtIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExOneEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ColAtPart

/- English proof (translation)
Unfold `Big`. Use `⟨0, fun _ _ _ => ⟨0, ?_⟩⟩` and prove the remaining obligations. Use `intros`. Use `beta_reduce`. Introduce `t w eL e' hL he u`.

Establish `hw` using `(GlobalTheory.FunObj.Comparison₂.cpt_idemSum hL).2.1 w.1 (Finset.mem_singleton_self _)`. Establish `h1` using `congrArg (fun a => cpt w.1 (toEAf _ a)) he`. Simplify using `only [map_mul, hw, mul_one] at h1`. Use function extensionality and compare the values at `j`. Simplify using `only [GridChoice.colAt]`.

Use `split_ifs with hj`. Use `congr 1`. Use `congr 1`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.comp_apply, map_mul, h1, one_mul]`. Both sides reduce to the same expression.
-/
theorem colAt_smul_of_mul_idem : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (w : locPl ch.G t) (eL e' : AE D), IsIdemSum eL {w.1} → e' * eL = eL → ∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), ch.S.colAt t w.1 (fun j => e' • u j) = ch.S.colAt t w.1 u := by
  unfold Big
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  beta_reduce
  intro t w eL e' hL he u
  have hw := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum hL).2.1 w.1 (Finset.mem_singleton_self _)

  have h1 := congrArg (fun a => cpt w.1 (toEAf _ a)) he
  simp only [map_mul, hw, mul_one] at h1
  funext j
  simp only [GridChoice.colAt]
  split_ifs with hj
  · congr 1
    congr 1
    congr 1
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.comp_apply, map_mul, h1, one_mul]
  · rfl

end GlobalTheory.ColAtPart
