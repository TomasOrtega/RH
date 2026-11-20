import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur

open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem adj_sub_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) : adj (x - y) = adj x - adj y := by
  ext T
  simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  noncomm_ring

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem adj_zero_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] : adj (0 : A) = 0 := by
  ext T
  simp [adj]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem adj_commutator_of_adjBdd {A : Type} [Ring A] [Algebra ℚ A] (x y : A) :
    adj x * adj y - adj y * adj x = adj (x * y - y * x) := by
  ext T
  simp only [adj, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    map_sub]
  noncomm_ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem adjBdd_holds : AdjBdd := by
  intro V _ _ N K e hrel hbdd hspan
  constructor
  · intro a b c d ha hb hc hd
    rw [adj_commutator_of_adjBdd, hrel a b c d ha hb hc hd, adj_sub_of_adjBdd]
    split_ifs <;> simp [adj_zero_of_adjBdd]
  · intro a ha b hb n T hT hn
    have hw : ∀ x ∈ {x : V | ∃ μ : ℕ → ℤ, IsWt N e μ x}, T x = (0 : Module.End ℚ V) x := by
      rintro x ⟨μ, hμ⟩
      simp only [LinearMap.zero_apply]
      by_cases hx : x = 0
      · simp [hx]
      have h1 : μ b - μ a ≤ K := by
        by_contra hlt
        push_neg at hlt
        apply hx
        apply hbdd b hb a ha (μ b - μ a) x _ hlt
        rw [hμ b hb, hμ a ha]
        push_cast
        rw [sub_smul]
      apply hbdd a ha b hb (μ a - μ b + n) (T x) _ (by push_cast at hn h1 ⊢; omega)
      have eq := LinearMap.congr_fun hT x
      simp only [adj, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Module.End.mul_apply, LinearMap.smul_apply, hμ a ha, hμ b hb, map_smul] at eq
      push_cast
      rw [add_smul, sub_smul, ← eq]
      abel
    exact LinearMap.ext_on hspan hw

end GlobalTheory.LeviCut
