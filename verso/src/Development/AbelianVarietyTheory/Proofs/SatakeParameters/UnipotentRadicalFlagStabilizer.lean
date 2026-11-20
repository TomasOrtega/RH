import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLowerBlockFlag
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.UnipFlag

open Matrix

variable {k : Type} [Field k] {a s : ℕ} {d : Fin s → ℕ}

def lowSpan (e : (Σ i, Fin (d i)) ≃ Fin a) (c : Fin s) : Submodule k (Fin a → k) :=
  GlobalTheory.LowerBlockFlag.f0 e c

/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_sub (k : Type) [Field k] (a s : ℕ) (d : Fin s → ℕ) (e : (Σ i, Fin (d i)) ≃ Fin a)
    (hne : GlobalTheory.SmGL.unipRad k e ≠ ⊥) :
    ∃ W : Submodule k (Fin a → k), W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ g : GL (Fin a) k,
      (∀ v, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v ∈ W) →
      (∀ v ∈ W, ((g : Matrix (Fin a) (Fin a) k) - 1).mulVec v = 0) → g ∈ GlobalTheory.SmGL.unipRad k e := by
  have hex : ∃ u ∈ GlobalTheory.SmGL.unipRad k e, u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne ((Subgroup.eq_bot_iff_forall _).2 h)
  obtain ⟨u, hu, hu1⟩ := hex
  have hij : ∃ i j, (u : Matrix (Fin a) (Fin a) k) i j ≠ (1 : Matrix (Fin a) (Fin a) k) i j := by
    by_contra h
    push_neg at h
    exact hu1 (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hij
  obtain ⟨hp, hd⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
  have hlt : GlobalTheory.SmGL.blk e i < GlobalTheory.SmGL.blk e j := by
    rcases lt_trichotomy (GlobalTheory.SmGL.blk e i) (GlobalTheory.SmGL.blk e j) with h | h | h
    · exact h
    · exfalso
      obtain ⟨⟨b, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b', j'⟩, rfl⟩ := e.surjective j
      simp only [GlobalTheory.SmGL.blk_apply] at h
      subst h
      apply hij
      rw [hd]
      simp [Matrix.one_apply]
    · exfalso
      apply hij
      rw [GlobalTheory.SmGL.mem_parab.1 hp i j h, one_apply_ne (by rintro rfl; exact lt_irrefl _ h)]
  refine ⟨lowSpan e (GlobalTheory.SmGL.blk e i), ?_, ?_, ?_⟩
  · intro hb
    have hm : Pi.single i (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := fun p hp' =>
      Pi.single_eq_of_ne (by rintro rfl; exact lt_irrefl _ hp') _
    rw [hb] at hm
    simpa using congrFun ((Submodule.mem_bot k).1 hm) i
  · intro ht
    have hm : Pi.single j (1 : k) ∈ lowSpan e (GlobalTheory.SmGL.blk e i) := ht ▸ Submodule.mem_top
    have := hm j hlt
    simp at this
  · intro g h1 h2
    have key : ∀ p q, ¬ (GlobalTheory.SmGL.blk e p < GlobalTheory.SmGL.blk e q) →
        ((g : Matrix (Fin a) (Fin a) k) - 1) p q = 0 := by
      intro p q hpq
      have hcol : ((g : Matrix (Fin a) (Fin a) k) - 1) p q =
          (((g : Matrix (Fin a) (Fin a) k) - 1) *ᵥ Pi.single q 1) p := by
        simp [Matrix.mulVec_single_one]
      rw [hcol]
      by_cases hq : GlobalTheory.SmGL.blk e q ≤ GlobalTheory.SmGL.blk e i
      · rw [h2 _ (fun r hr => Pi.single_eq_of_ne (by rintro rfl; exact absurd hq (not_le.2 hr)) _)]
        rfl
      · exact h1 _ p (lt_of_lt_of_le (not_le.1 hq) (not_lt.1 hpq))
    have hg : ∀ p q, (g : Matrix (Fin a) (Fin a) k) p q =
        (1 : Matrix (Fin a) (Fin a) k) p q + ((g : Matrix (Fin a) (Fin a) k) - 1) p q := by
      intro p q
      simp
    refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun p q hqp => ?_, fun b p q => ?_⟩
    · rw [hg, key p q (not_lt.2 hqp.le), one_apply_ne (by rintro rfl; exact lt_irrefl _ hqp), add_zero]
    · rw [hg, key _ _ (by simp), add_zero]
      simp [Matrix.one_apply]

end GlobalTheory.UnipFlag
