import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Split into cases according to the possible forms of the given data.

Split into cases according to the possible forms of the given data. Simplify by unfolding definitions. Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem trEasy : TrEasy := by
  intro X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ
  obtain ⟨⟨hpre, -, -, hC, hbase, hxi, hQ, -⟩, hg, -, hs⟩ := h
  obtain ⟨B, C, Wr, V, Sg, N, Gj⟩ := X
  obtain ⟨B', C', Wr', V', Sg', N', Gj'⟩ := X'
  cases B
  cases B'
  dsimp only at hpre
  subst hpre
  obtain ⟨f, f', hff, hLC, hLC'⟩ := hC
  have hf : f' = f := eq_of_heq hff
  subst hf
  have hv0 : G'.pl.v0 = G.pl.v0 := eq_of_heq hg.v0
  have hw : G'.pl.w = G.pl.w := eq_of_heq hg.w
  have hchi : G'.ch.chiH = G.ch.chiH := eq_of_heq hg.chiH
  have hxi' : ∀ t, L'.xiH t = L.xiH (ι t) := fun t => eq_of_heq (hxi t)
  have hQ' : ∀ t, L'.Q t = L.Q (ι t) := fun t => eq_of_heq (hQ t)
  have hPA : S'.PA = S.PA := eq_of_heq hs.PA
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
    rfl
  have hloc : ∀ t, locPl G' t = locPl G (ι t) := fun t => by
    unfold locPl
    rw [hW0, hQ' t]
    rfl
  have hdep : ∀ w, depthAt G' w = depthAt G w := fun w => by
    unfold depthAt cosExp Places.depth
    rw [hW0, hv0]
    rfl
  refine ⟨fun hch => ?_, fun hr => ?_, fun hr => ?_⟩
  · refine ⟨fun j => ?_, fun t => ?_, fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · have := hch.mu0 j
      rw [hLC] at this
      rw [hLC']
      exact this
    · rw [hxi' t]
      exact hch.xi (ι t)
    · rw [hchi]
      exact hch.chi i h1 h2
    · have := hch.eta
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.chiPsi
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del
      rw [hLC] at this
      rw [hLC']
      exact this
    · have := hch.del'
      rw [hLC] at this
      rw [hLC']
      exact this
  · refine ⟨hr.1, fun t w hwt => ?_, fun w hw' => ?_⟩
    · rw [hdep]
      rw [hloc] at hwt
      exact hr.2.1 (ι t) w hwt
    · rcases hw' with hw' | ⟨t, hw'⟩
      · rw [hPA] at hw'
        exact hr.2.2 w (Or.inl hw')
      · rw [hloc] at hw'
        exact hr.2.2 w (Or.inr ⟨ι t, hw'⟩)
  · intro i j t Λ Λ₀ h1 h2 s hs1 hs2 hΛ
    have hν : ∀ t, SqNum.nuH G' t i j = SqNum.nuH G (ι t) i j := fun t => by
      unfold SqNum.nuH
      rw [hLC', hLC, hxi' t, hchi]
      rfl
    rw [hν] at h1
    rw [hν, hbase] at h2
    exact hr i j (ι t) Λ Λ₀ h1 h2 s hs1 hs2 hΛ

end GlobalTheory.RowEx
