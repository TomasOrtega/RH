import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

/- English proof (translation)
Introduce `D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ h`. Take `⟨Q, _, hS, -, -⟩` from `h.page`. Establish `h1` using `host_f_sq_le_rd Q`. Rewrite `h1` using `[hostSize_f, hostSize_rd]`. Use `⟨h1, ?_⟩` and prove the remaining obligations.

Establish `hm4` using `host_m_pow_four_le_f hS`. Rewrite `hm4` using `[hostSize_f]`. Establish `hm2` using `D.R.two_le_m`. Establish `h16 : 16 ≤ D.R.f`. Establish `: 2 ^ 4 ≤ D.R.m ^ 4` using `Nat.pow_le_pow_left hm2 4`.

Use linear arithmetic over natural numbers and integers. Establish `h2` using `D.R.f_le_k`. Unfold `Ranks.f Ranks.n at *`. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem pageRun_sq_le_rd_and_eight_le_rank : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ h
  obtain ⟨Q, _, hS, -, -⟩ := h.page
  have h1 := host_f_sq_le_rd Q
  rw [hostSize_f, hostSize_rd] at h1
  refine ⟨h1, ?_⟩
  have hm4 := host_m_pow_four_le_f hS
  rw [hostSize_f] at hm4
  have hm2 := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    omega
  have h2 := D.R.f_le_k
  unfold Ranks.f Ranks.n at *
  unfold Ranks.r
  omega

end GlobalTheory.FinalJoin
