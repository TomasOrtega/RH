import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinNormEisensteinLeRadiusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. A detailed English derivation is pending.
-/
theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
