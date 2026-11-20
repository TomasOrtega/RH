import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.HcVOfCentralChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapQdet
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.InfCharData
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TopCap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Introduce `ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy`. Take `⟨hg, hnpq, h8, -⟩` from `gapCentral n ε lam h hgap`. Establish `hlam : S7.IsHCParam lam` using `⟨hanti, hint⟩`. Take `⟨T⟩` from `HW.kType_exists ε lam hlam`. Take `⟨μ, hμ⟩` from `S7.exists_mu hlam`.

Establish `hq0 : 1 ≤ S7.q0 ε` using `le_min hp hq`. Establish `hP` using `(S7.isPsiFor_psiM ε lam h T μ hlam hμ hg hq0 (by unfold S7.q0; push_cast; exact h8)).1`. Establish `hstd : StdGap ε lam` using `⟨hanti, h, hg, hnpq⟩`. Establish `hV0 : V ≠ ⊥`. Take `⟨w, hw, hw0, -⟩` from `hV.2.2.2`.

Introduce `hb`. Rewrite `hw` using `[hb]`. Conclude with `hw0 ((Submodule.mem_bot ℂ).1 hw)`. Establish `key` using `capelli_data hstd hσ hD hV hcas hVK hV0 hP (fun Y g hg' => S7.psiCapelli (n := n) ε lam T μ hμ Y g hg') (ω - ((n : ℂ) - 1) / 2) y hy`. Rewrite `key` using `[sub_add_cancel]`.

Rewrite using `[capelliQdet.1 (Module.End ℂ D) n E ω, key, capelliQdet.{0}.2]`.
-/
theorem centralChar (n : ℕ) : CentralCharStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hcas hVK hint hanti hgap hp hq ω y hy
  obtain ⟨hg, hnpq, h8, -⟩ := gapCentral n ε lam h hgap
  have hlam : S7.IsHCParam lam := ⟨hanti, hint⟩
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨μ, hμ⟩ := S7.exists_mu hlam
  have hq0 : 1 ≤ S7.q0 ε := le_min hp hq
  have hP := (S7.isPsiFor_psiM ε lam h T μ hlam hμ hg hq0
    (by unfold S7.q0; push_cast; exact h8)).1
  have hstd : StdGap ε lam := ⟨hanti, h, hg, hnpq⟩
  have hV0 : V ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hV.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have key := capelli_data hstd hσ hD hV hcas hVK hV0 hP
    (fun Y g hg' => S7.psiCapelli (n := n) ε lam T μ hμ Y g hg') (ω - ((n : ℂ) - 1) / 2) y hy
  rw [sub_add_cancel] at key
  rw [capelliQdet.1 (Module.End ℂ D) n E ω, key, capelliQdet.{0}.2]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
