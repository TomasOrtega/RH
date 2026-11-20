import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TiltUnique

/- English proof (translation)
Introduce `D T L sc G j hj δ δ' h h'`. Break down `Nat.even_or_odd j with he | ho` into its components or cases. Rewrite using `[h.2.1 he, h'.2.1 he]`. Take `⟨a, ha⟩` from `D.R.m_even`. Take `⟨b, hb⟩` from `ho`.

Establish `h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2)` using `by omega`. Take `⟨x1, x2, x3⟩` from `h.2.2 _ hj h₂`. Take `⟨y1, y2, y3⟩` from `h'.2.2 _ hj h₂`. Establish `k` using `(rowJac G j hj _ h₂).sum_eq_one`. Establish `e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0` using `x1.trans y1.symm`.

Establish `eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX` using `x2.trans y2.symm`. Establish `eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY` using `x3.trans y3.symm`. Establish `hm : mt _ δ = mt _ δ'`. Rewrite using `[← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]`. Rewrite using `[← k]`.

Simplify using `only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]`. Conclude with `Subtype.ext (Units.ext hm)`.
-/
theorem tilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  intro D T L sc G j hj δ δ' h h'
  rcases Nat.even_or_odd j with he | ho
  · rw [h.2.1 he, h'.2.1 he]
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := ho
    have h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨x1, x2, x3⟩ := h.2.2 _ hj h₂
    obtain ⟨y1, y2, y3⟩ := h'.2.2 _ hj h₂
    have k := (rowJac G j hj _ h₂).sum_eq_one
    have e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0 := x1.trans y1.symm
    have eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX := x2.trans y2.symm
    have eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY := x3.trans y3.symm
    have hm : mt _ δ = mt _ δ' := by
      rw [← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]
      rw [← k]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.TiltUnique
