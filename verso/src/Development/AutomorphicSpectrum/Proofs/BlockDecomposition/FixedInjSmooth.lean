import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

namespace GlobalTheory.CompanionTheory.DepthZeroJac

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
open GlobalTheory.DepthZeroJac GlobalTheory.StepData GlobalTheory.IwahoriInj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem fixed_inj_smooth (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsSmooth π) :
    ∀ v ∈ fixed π (Gx k e),
      (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = 0 → v = 0 := by
  intro v hv h0
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  have h1 : v ∈ twKer π (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h0
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  exact claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v hv hM

end GlobalTheory.CompanionTheory.DepthZeroJac
