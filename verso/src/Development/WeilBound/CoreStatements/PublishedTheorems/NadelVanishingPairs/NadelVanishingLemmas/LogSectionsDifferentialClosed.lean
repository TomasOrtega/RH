import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.CechFam
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ChartFormsDifferentialClosed
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogFormsEqChartForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoundedTwistLocalEquationChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.Cartier

namespace GlobalTheory.LogDR

/- English proof (translation)
Introduce `p _ X _ _ C _ E n ι _ 𝒜 G r hr q W η hη`. Simplify using `only [logSec, latSec, AddSubgroup.mem_iInf] at hη ⊢`. Introduce `y hy`. Establish `hcov : y ∈ (⨆ i, 𝒜.U i)` using `by rw [𝒜.cover]; trivial`. Take `⟨i, hi⟩` from `(Opens.mem_iSup).1 hcov`.

Take `⟨t, ht⟩` from `G.exists_isEqn y`. Take `⟨-, hloc⟩` from `GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr`. Take `⟨ρ, -, hρ⟩` from `hloc i`. Establish `heq` using `hρ y hi t ht`. Establish `hstalk` using `GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) (p • G + ∑ c, r c • E c) y (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j)`.

Establish `h1` using `hη y hy`. Rewrite `h1` using `[hstalk q (𝒜.chart i) hi heq]`. Rewrite using `[hstalk (q + 1) (𝒜.chart i) hi heq]`. Conclude with `GlobalTheory.T.chart_forms_differential_closed X.functionField p (locRing y) n (𝒜.x i) (𝒜.J i) t ρ ((𝒜.chart i).chart y hi) q η h1`.
-/
theorem extD_mem_logSec_roundedTwist : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] {C : Type} [Fintype C] {E : C → CartierDiv X} {n : ℕ} {ι : Type} [LinearOrder ι] (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (r : C → ℕ), (∀ c, r c < p) → ∀ (q : ℕ) (W : X.Opens) (η : abelian₂ X.functionField), η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) q W → extD _ η ∈ logSec (suppAll E) (p • G + ∑ c, r c • E c) (q + 1) W := by
  intro p _ X _ _ C _ E n ι _ 𝒜 G r hr q W η hη
  simp only [logSec, latSec, AddSubgroup.mem_iInf] at hη ⊢
  intro y hy
  have hcov : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
  obtain ⟨i, hi⟩ := (Opens.mem_iSup).1 hcov
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨-, hloc⟩ := GlobalTheory.T.roundedTwist_localEquation_chart p 𝒜 G r hr
  obtain ⟨ρ, -, hρ⟩ := hloc i
  have heq := hρ y hi t ht
  have hstalk := GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) (p • G + ∑ c, r c • E c) y
    (t ^ p * ∏ j ∈ 𝒜.J i, 𝒜.x i j ^ ρ j)
  have h1 := hη y hy
  rw [hstalk q (𝒜.chart i) hi heq] at h1
  rw [hstalk (q + 1) (𝒜.chart i) hi heq]
  exact GlobalTheory.T.chart_forms_differential_closed X.functionField p (locRing y) n (𝒜.x i) (𝒜.J i) t ρ
    ((𝒜.chart i).chart y hi) q η h1

end GlobalTheory.LogDR
