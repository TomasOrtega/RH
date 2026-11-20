import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finsupp.WellFounded

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.Alg.gordan_dickson (σ : Type) [Finite σ] (S : Set (σ →₀ ℕ)) :
    ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, m ∈ S) ∧ ∀ n ∈ S, ∃ m ∈ μ, m ≤ n := by
  classical
  haveI := Fintype.ofFinite σ
  have hfin : {m : σ →₀ ℕ | Minimal (· ∈ S) m}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOf_minimal_antichain _)
  refine ⟨hfin.toFinset, fun m hm => ((Set.Finite.mem_toFinset hfin).1 hm).1, fun n hn => ?_⟩
  obtain ⟨b, hb, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE S).exists_le_minimal hn
  exact ⟨b, (Set.Finite.mem_toFinset hfin).2 hmin, hb⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Alg.gordan :
    ∀ (σ : Type) [Finite σ] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (wt : σ → X), ∃ g : Finset (σ →₀ ℕ), (∀ n ∈ g, n ≠ 0 ∧ Finsupp.weight wt n = 0) ∧
      (∀ n, Finsupp.weight wt n = 0 → n ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ))) ∧
      ∀ j, ∃ μ : Finset (σ →₀ ℕ), (∀ m ∈ μ, Finsupp.weight wt m = j) ∧ ∀ n, Finsupp.weight wt n = j → ∃ m ∈ μ, m ≤ n := by
  intro σ _ X _ _ _ wt
  classical
  obtain ⟨g, hgS, hg⟩ := gordan_dickson σ {n | n ≠ 0 ∧ Finsupp.weight wt n = 0}
  refine ⟨g, hgS, ?_, fun j => ?_⟩
  · intro n
    induction n using WellFoundedLT.induction with
    | _ n ih =>
      intro hn
      by_cases h0 : n = 0
      · rw [h0]
        exact zero_mem _
      · obtain ⟨m, hm, hmn⟩ := hg n ⟨h0, hn⟩
        have hm' := hgS m hm
        have hsplit : n = m + (n - m) := (add_tsub_cancel_of_le hmn).symm
        have hw : Finsupp.weight wt (n - m) = 0 := by
          have h1 := hn
          rw [hsplit, map_add, hm'.2, zero_add] at h1
          exact h1
        have hlt : n - m < n := by
          refine lt_of_le_of_ne tsub_le_self fun h => hm'.1 ?_
          have h2 : m + (n - m) = n := add_tsub_cancel_of_le hmn
          rw [h] at h2
          simpa using h2
        rw [hsplit]
        exact add_mem (AddSubmonoid.subset_closure hm) (ih _ hlt hw)
  · obtain ⟨μ, hμS, hμ⟩ := gordan_dickson σ {n | Finsupp.weight wt n = j}
    exact ⟨μ, hμS, hμ⟩
