import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinProj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinFub

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem toL2_eq_zero_of_eq_zero_on_UJset {n : ℕ} (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ g ∈ UJset ε, F g = 0) : toL2 ε F = 0 := by
  have h0 : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun _ => 0 := by
    funext g; exact hF _ (unitary_matrix_mem_set ε g)
  have hm : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
    rw [h0]; exact MemLp.zero
  rw [toL2_eq_memLp_toLp ε hm]
  simp only [h0]
  exact MemLp.toLp_zero _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem finStep : FinStatement := by
  intro hIS k r ε u lam' h z c Vp _ _ _ π μW μN P hP hB hp hq hgap hlam hgl ξ Wf W' hWf hW' hirr hcas hK hinj
  obtain ⟨w, hwW, hw0, -⟩ := hirr.2.2.2
  obtain ⟨F, hF, hwF⟩ := (hW' w).1 hwW
  have hne : ∃ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := toL2_eq_zero_of_eq_zero_on_UJset ε F (hinj F hF hcon)
    apply hw0
    apply Subtype.ext
    rw [hwF, h0]
    rfl
  obtain ⟨x, hx, hxne⟩ := hne
  obtain ⟨T', μ', v₁, v₂, hμ, hrep⟩ :=
    finProj k r ε lam' h hp hq hgap hlam hgl Wf W' hWf hW' hirr hcas hK F hF ⟨w, hwW, hw0, hwF⟩
  obtain ⟨hFc, C, hFb⟩ := hWf F hF
  obtain ⟨x₀, hx₀, hne0⟩ := finFub hIS k r ε u lam' h z c Vp π μW μN P hP hB hp hq hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C
    hFc hFb hrep x hx hxne
  exact ⟨T', μ', P, z, c, Vp, inferInstance, inferInstance, inferInstance, π, μW, μN, hμ, hP, hB,
    v₁, v₂, ξ, x₀, x, hx₀, hx, hne0⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
