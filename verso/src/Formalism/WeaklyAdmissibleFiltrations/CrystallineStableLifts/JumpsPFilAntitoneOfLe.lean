import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

namespace FilPhi

variable {LL : Type} [Field LL] {D : Type} [AddCommGroup D] [Module LL D]
  {n : ℕ} {Emb : Type} [Fintype Emb]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem fil_le_fil_of_le (F : FilPhi LL D n Emb) (τ : Emb) {b a : ℤ} (hba : b ≤ a) :
    F.Fil τ a ≤ F.Fil τ b := by
  induction a, hba using Int.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (F.Fil_anti τ k).trans ih

end FilPhi

open FilPhi

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem jumpsIcc : JumpsIcc := by
  intro LL _ D _ _ n Emb _ F τ l h
  constructor
  · intro hJ
    have hno : ∀ a, a ∉ Set.Icc l h → F.Fil τ (a + 1) = F.Fil τ a := by
      intro a ha
      by_contra hne
      exact ha (hJ a hne)
    constructor
    ·
      have key : ∀ k : ℕ, F.Fil τ (l - k) = F.Fil τ l := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (l - ((k + 1 : ℕ) : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.1; push_cast at this; omega
          have e := hno _ hk
          have : l - ((k + 1 : ℕ) : ℤ) + 1 = l - (k : ℤ) := by push_cast; ring
          rw [this] at e
          rw [← e, ih]
      have hlo := F.Fil_lo τ (l - ((l - min F.lo l).toNat : ℕ)) (by omega)
      rw [key] at hlo
      exact hlo
    ·
      have key : ∀ k : ℕ, F.Fil τ (h + 1 + k) = F.Fil τ (h + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hk : (h + 1 + (k : ℤ)) ∉ Set.Icc l h := by
            intro hm; have := hm.2; omega
          have e := hno _ hk
          have : h + 1 + ((k + 1 : ℕ) : ℤ) = h + 1 + (k : ℤ) + 1 := by push_cast; ring
          rw [this, e, ih]
      have hhi := F.Fil_hi τ (h + 1 + ((F.hi - (h + 1)).toNat : ℕ)) (by omega)
      rw [key] at hhi
      exact hhi
  · rintro ⟨hl, hh⟩ a ha
    by_contra hm
    apply ha
    rcases (not_and_or.mp hm) with hal | hah
    · have hal : a + 1 ≤ l := by omega
      apply le_antisymm (F.Fil_anti τ a)
      calc F.Fil τ a ≤ F.Dl (F.letter τ) := F.Fil_le τ a
        _ = F.Fil τ l := hl.symm
        _ ≤ F.Fil τ (a + 1) := F.fil_le_fil_of_le τ hal
    · have hah : h + 1 ≤ a := by omega
      have h1 : F.Fil τ a = ⊥ := le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ hah)
      have h2 : F.Fil τ (a + 1) = ⊥ :=
        le_bot_iff.mp (hh ▸ F.fil_le_fil_of_le τ (by omega : h + 1 ≤ a + 1))
      rw [h1, h2]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem subTopBot : SubTopBot := by
  intro LL _ D _ _ n Emb _ F
  constructor
  · refine ⟨fun x _ => Submodule.mem_top, ?_⟩
    simp only [top_inf_eq]
    exact F.internal.submodule_iSup_eq_top.symm
  · refine ⟨fun x hx => ?_, ?_⟩
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    · simp

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem jumpsIcc_and_subTopBot : JumpsIcc ∧ SubTopBot := ⟨jumpsIcc, subTopBot⟩

end Formalism.WeaklyAdmissibleFiltrations
