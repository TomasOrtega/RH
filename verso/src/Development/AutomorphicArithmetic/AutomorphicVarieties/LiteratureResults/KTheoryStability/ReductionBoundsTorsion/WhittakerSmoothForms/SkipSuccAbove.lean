import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth

noncomputable section

open Set Filter Topology

namespace PositivityTheory.KB.WhittakerCocycle

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem skip_zero_cons (γ : Γ) (σ : ℕ → Γ) : skip 0 (cons γ σ) = σ := by
  funext n; simp [skip, cons]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.
-/
theorem skip_succ_cons (i : ℕ) (γ : Γ) (σ : ℕ → Γ) : skip (i + 1) (cons γ σ) = cons γ (skip i σ) := by
  funext n
  cases n with
  | zero => simp [skip, cons]
  | succ m => simp [skip, cons]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem delG_cons (n : ℕ) {X : Type} [AddCommGroup X] [Module ℝ X] (β : (ℕ → Γ) → X) (γ : Γ)
    (σ : ℕ → Γ) : delG (n + 1) β (cons γ σ) = β σ - delG n (fun τ => β (cons γ τ)) σ := by
  simp only [delG]
  rw [Finset.sum_range_succ', skip_zero_cons]
  simp only [skip_succ_cons, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    pow_zero, one_smul]
  abel

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem skip_succAbove {m : ℕ} (σ : ℕ → Γ) (i : Fin (m + 2)) (l : Fin (m + 1)) :
    skip (i : ℕ) σ (l : ℕ) = σ ((i.succAbove l : Fin (m + 2)) : ℕ) := by
  rw [skip]
  rcases lt_or_ge (l : ℕ) (i : ℕ) with hl | hl
  · rw [if_pos hl, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using hl)]
    simp
  · rw [if_neg (not_lt.mpr hl), Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using hl)]
    simp

variable (U : Set V) (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem pLoc : PLoc U A φ := by
  intro H h hh
  obtain ⟨t, ht, hfin⟩ := H.locFin ⟨h, hh⟩
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype U ⟨h, hh⟩ t).mp ht
  refine ⟨hfin.toFinset, u ∩ U, inter_mem hu (H.isOpen.mem_nhds hh), inter_subset_right, ?_⟩
  intro γ hγ x hx
  by_contra hne
  apply hγ
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨x, hx.2⟩, hne, hut hx.1⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem finsum_psi (hL : PLoc U A φ) (H : Hyp U A φ) {h : V} (hh : h ∈ U) :
    ∃ s : Finset Γ, ∃ W ∈ 𝓝 h, W ⊆ U ∧ ∀ x ∈ W, (∑ γ ∈ s, psi A φ γ x = 1) ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℝ M] (F : Γ → M),
        ∑ᶠ γ, psi A φ γ x • F γ = ∑ γ ∈ s, psi A φ γ x • F γ := by
  obtain ⟨s, W, hW, hWU, hs⟩ := hL H h hh
  refine ⟨s, W, hW, hWU, fun x hx => ⟨?_, ?_⟩⟩
  · have h1 := H.sum_one x (hWU hx)
    rw [finsum_eq_sum_of_support_subset (s := s)] at h1
    · exact h1
    · intro γ hγ
      by_contra hγs
      exact hγ (hs γ hγs x hx)
  · intro M _ _ F
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    by_contra hγs
    apply hγ
    simp [hs γ hγs x hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.
-/
theorem pHom (hL : PLoc U A φ) : PHom U A φ := by
  intro H q n β σ h hh
  obtain ⟨s, W, hW, hWU, hs⟩ := finsum_psi U A φ hL H hh
  obtain ⟨h1, hF⟩ := hs h (mem_of_mem_nhds hW)
  have hK : ∀ (β' : (ℕ → Γ) → V → V [⋀^Fin q]→L[ℝ] ℝ) τ,
      Kf A φ β' τ h = ∑ γ ∈ s, psi A φ γ h • β' (cons γ τ) h :=
    fun β' τ => hF (fun γ => β' (cons γ τ) h)
  rw [hK (delG (n + 1) β)]
  simp only [delG_cons, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1,
    one_smul, sub_sub_cancel]
  simp only [delG, Finset.sum_apply, Pi.smul_apply, hK, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun i _ => smul_comm _ _ _

end PositivityTheory.KB.WhittakerCocycle

end
