import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAboveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundNefPlusAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSLowerTwist

/- English proof (translation)
Introduce `hC hHS k _ X _ p D hX P b s t hG c hgen hreg hnef hsemi a ha ε hε`. Take `⟨α, hα, hlim⟩` from `GlobalTheory.SelfInterGrowth.main hC k X p D hX P.L P.A a ha`. Establish `hε3 : 0 < ε / 3` using `by positivity`. Establish `h1` using `GlobalTheory.T.smallSectionCount_log_twist_continuity_above k X p D hX P b s t hG c hgen hreg (ε / 3) hε3`. Establish `h2 : ∀ᶠ n : ℕ in atTop, a / ((D + 1).factorial : ℝ) - ε / 3 < α n / (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)` using `(hlim.div_const ((D + 1).factorial : ℝ)).eventually (lt_mem_nhds (by linarith))`.

Take `⟨n, ⟨hn1, hn2⟩, hn0⟩` from `((h1.and h2).and (eventually_gt_atTop 0)).exists`. Establish `h3` using `GlobalTheory.T.arithHilbertSamuel_lowerBound_nef_plus_ample hC hHS k X p D hX P c n (α n) hn0 hnef hsemi hG.ample hG.nef.semiPos (hα n) (ε / 3) hε3`. Use `filter_upwards [hn1, h3] with M hM1 hM3`. Establish `hM : (0 : ℝ) ≤ (M : ℝ) ^ (D + 1)` using `by positivity`. Rewrite `hM3` using `[div_right_comm]`.

Establish `h4` using `mul_le_mul_of_nonneg_right hn2.le hM`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c → Regime P D → NefFib P.L → P.L.SemiPos D → ∀ a : ℝ, P.L.IsSelfInter a → ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop, (a / (D + 1).factorial - ε) * (M : ℝ) ^ (D + 1) ≤ P.lc M (-c) 1 := by
  intro hC hHS k _ X _ p D hX P b s t hG c hgen hreg hnef hsemi a ha ε hε
  obtain ⟨α, hα, hlim⟩ := GlobalTheory.SelfInterGrowth.main hC k X p D hX P.L P.A a ha
  have hε3 : 0 < ε / 3 := by positivity
  have h1 := GlobalTheory.T.smallSectionCount_log_twist_continuity_above k X p D hX P b s t hG c hgen hreg (ε / 3) hε3
  have h2 : ∀ᶠ n : ℕ in atTop, a / ((D + 1).factorial : ℝ) - ε / 3 <
      α n / (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
    (hlim.div_const ((D + 1).factorial : ℝ)).eventually (lt_mem_nhds (by linarith))
  obtain ⟨n, ⟨hn1, hn2⟩, hn0⟩ := ((h1.and h2).and (eventually_gt_atTop 0)).exists
  have h3 := GlobalTheory.T.arithHilbertSamuel_lowerBound_nef_plus_ample hC hHS k X p D hX P c n (α n) hn0 hnef hsemi hG.ample hG.nef.semiPos (hα n) (ε / 3) hε3
  filter_upwards [hn1, h3] with M hM1 hM3
  have hM : (0 : ℝ) ≤ (M : ℝ) ^ (D + 1) := by positivity
  rw [div_right_comm] at hM3
  have h4 := mul_le_mul_of_nonneg_right hn2.le hM
  nlinarith

end GlobalTheory.HSLowerTwist
