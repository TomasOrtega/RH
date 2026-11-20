import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSignatureOfGramEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRankSize

/- English proof (translation)
Establish `hk` using `D.R.k_even`. Establish `hm` using `D.R.m_even`. Establish `ht` using `D.R.t_odd`. Establish `h3` using `D.R.m_add_three_le_k`. Establish `h2` using `D.R.two_le_m`.

Rewrite `hk`, `hm` using `[Nat.even_iff]`. Rewrite `ht` using `[Nat.odd_iff]`. Simplify using `only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]`. Establish `e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t` using `by ring`. Establish `e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6)` using `by ring`.

Rewrite using `[e1, e2]`. Generalize the expression as in `j * D.R.t = A`. Generalize the expression as in `i * (D.R.k + D.R.m - 1 + 6) = B`. Rewrite using `[Nat.even_iff]`. Use linear arithmetic over natural numbers and integers.
-/
theorem bot_arith (D : D7) (i j : ℕ) :
    Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧
      1 < SqNum.botSmall D i j := by
  have hk := D.R.k_even
  have hm := D.R.m_even
  have ht := D.R.t_odd
  have h3 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  rw [Nat.even_iff] at hk hm
  rw [Nat.odd_iff] at ht
  simp only [SqNum.botBig, SqNum.botSmall, rankV, sLen, Formalism.BasicNotions.Ranks.r]
  have e1 : (j + 1) * D.R.t = j * D.R.t + D.R.t := by ring
  have e2 : (i + 1) * (D.R.k + D.R.m - 1 + 6) = i * (D.R.k + D.R.m - 1 + 6) + (D.R.k + D.R.m - 1 + 6) := by ring
  rw [e1, e2]
  generalize j * D.R.t = A
  generalize i * (D.R.k + D.R.m - 1 + 6) = B
  rw [Nat.even_iff]
  omega

/- English proof (translation)
Use `⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩` and prove the remaining obligations. Introduce `i j`. Conclude with `bot_arith D i j`.
-/
theorem bottom_ranks : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ i j : Fin D.R.m, Even (SqNum.botBig D i j + SqNum.botSmall D i j) ∧ SqNum.botSmall D i j + 2 < SqNum.botBig D i j ∧ 1 < SqNum.botSmall D i j := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro i j
  exact bot_arith D i j

end GlobalTheory.BotRankSize

end
