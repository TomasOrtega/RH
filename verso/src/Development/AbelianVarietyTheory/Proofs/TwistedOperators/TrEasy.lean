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
Introduce `X X' T T' L L' sc G G' W W' S S' μ₀ μ₀' ι h M σ`. Take `⟨⟨hpre, -, -, hC, hbase, hxi, hQ, -⟩, hg, -, hs⟩` from `h`. Take `⟨B, C, Wr, V, Sg, N, Gj⟩` from `X`. Take `⟨B', C', Wr', V', Sg', N', Gj'⟩` from `X'`. Consider the cases of `B`.

Consider the cases of `B'`. Simplify using `only at hpre`. Substitute `hpre` using the available equality. Take `⟨f, f', hff, hLC, hLC'⟩` from `hC`. Establish `hf : f' = f` using `eq_of_heq hff`.

Substitute `hf` using the available equality. Establish `hv0 : G'.pl.v0 = G.pl.v0` using `eq_of_heq hg.v0`. Establish `hw : G'.pl.w = G.pl.w` using `eq_of_heq hg.w`. Establish `hchi : G'.ch.chiH = G.ch.chiH` using `eq_of_heq hg.chiH`. Establish `hxi' : ∀ t, L'.xiH t = L.xiH (ι t)` using `fun t => eq_of_heq (hxi t)`.

Establish `hQ' : ∀ t, L'.Q t = L.Q (ι t)` using `fun t => eq_of_heq (hQ t)`. Establish `hPA : S'.PA = S.PA` using `eq_of_heq hs.PA`. Establish `hW0 : G'.pl.W0 = G.pl.W0`. Unfold `Places.W0 Places.S0`. Rewrite using `[hv0, hw]`.

Both sides reduce to the same expression. Establish `hloc : ∀ t, locPl G' t = locPl G (ι t)` using `fun t => by`. Unfold `locPl`. Rewrite using `[hW0, hQ' t]`. Both sides reduce to the same expression.

Establish `hdep : ∀ w, depthAt G' w = depthAt G w` using `fun w => by`. Unfold `depthAt cosExp Places.depth`. Rewrite using `[hW0, hv0]`. Both sides reduce to the same expression. Use `⟨fun hch => ?_, fun hr => ?_, fun hr => ?_⟩` and prove the remaining obligations.

Use `⟨fun j => ?_, fun t => ?_, fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hch.mu0 j` as an intermediate fact. Rewrite `this` using `[hLC]`. Rewrite using `[hLC']`. Conclude with `this`.

Rewrite using `[hxi' t]`. Conclude with `hch.xi (ι t)`. Rewrite using `[hchi]`. Conclude with `hch.chi i h1 h2`. Use `hch.eta` as an intermediate fact.

Rewrite `this` using `[hLC]`. Rewrite using `[hLC']`. Conclude with `this`. Use `hch.chiPsi` as an intermediate fact. Rewrite `this` using `[hLC]`.

Rewrite using `[hLC']`. Conclude with `this`. Use `hch.del` as an intermediate fact. Rewrite `this` using `[hLC]`. Rewrite using `[hLC']`.

Conclude with `this`. Use `hch.del'` as an intermediate fact. Rewrite `this` using `[hLC]`. Rewrite using `[hLC']`. Conclude with `this`.

Use `⟨hr.1, fun t w hwt => ?_, fun w hw' => ?_⟩` and prove the remaining obligations. Rewrite using `[hdep]`. Rewrite `hwt` using `[hloc]`. Conclude with `hr.2.1 (ι t) w hwt`. Break down `hw' with hw' | ⟨t, hw'⟩` into its components or cases.

Rewrite `hw'` using `[hPA]`. Conclude with `hr.2.2 w (Or.inl hw')`. Rewrite `hw'` using `[hloc]`. Conclude with `hr.2.2 w (Or.inr ⟨ι t, hw'⟩)`. Introduce `i j t Λ Λ₀ h1 h2 s hs1 hs2 hΛ`.

Establish `hν : ∀ t, SqNum.nuH G' t i j = SqNum.nuH G (ι t) i j` using `fun t => by`. Unfold `SqNum.nuH`. Rewrite using `[hLC', hLC, hxi' t, hchi]`. Both sides reduce to the same expression. Rewrite `h1` using `[hν]`.

Rewrite `h2` using `[hν, hbase]`. Conclude with `hr i j (ι t) Λ Λ₀ h1 h2 s hs1 hs2 hΛ`.
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
