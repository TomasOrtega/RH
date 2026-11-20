import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.OriginChart

/- English proof (translation)
Introduce `K'' _ P N`. Take `⟨y⟩ : Nonempty (PrimeSpectrum K'')` from `inferInstance`. Establish `hy : (eSec P.A) y ∈ ⨆ i, P.L.U i` using `by rw [P.isLB.cover]; trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Use `⟨fun _ => i, fun w _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.Cartier.lbPow_U]`. Establish `hw : w = y` using `Subsingleton.elim (α := PrimeSpectrum K'') _ _`. Rewrite using `[hw]`. Conclude with `hi`.
-/
theorem exists_chart_lbPow_eSec : ∀ (K'' : Type) [Field K''] (P : Out.PolAV (Sp K'')) (N : ℕ),
    ∃ i₀ : (lbPow P.L N).ι, ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ := by
  intro K'' _ P N
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum K'') := inferInstance
  have hy : (eSec P.A) y ∈ ⨆ i, P.L.U i := by rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨fun _ => i, fun w _ => ?_⟩
  rw [GlobalTheory.Cartier.lbPow_U]
  have hw : w = y := Subsingleton.elim (α := PrimeSpectrum K'') _ _
  rw [hw]
  exact hi

end GlobalTheory.OriginChart
