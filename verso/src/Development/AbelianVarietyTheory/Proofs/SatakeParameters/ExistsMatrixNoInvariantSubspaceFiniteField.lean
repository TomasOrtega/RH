import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
open GlobalTheory.Cong

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Prove the first alternative. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem exists_matrix_no_invariant_subspace :
    ∀ (κ : Type) [Field κ] [Finite κ] (a : ℕ), 1 ≤ a → ∃ B : Matrix (Fin a) (Fin a) κ,
      ∀ W : Submodule κ (Fin a → κ), (∀ v ∈ W, B.mulVec v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro κ _ _ a ha
  obtain ⟨p, hp⟩ := CharP.exists κ
  haveI : Fact p.Prime := ⟨CharP.char_is_prime κ p⟩
  haveI : NeZero a := ⟨by omega⟩
  let L := FiniteField.Extension κ p a
  let b : Module.Basis (Fin a) κ L :=
    Module.finBasisOfFinrankEq κ L (FiniteField.finrank_extension κ p a)
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Lˣ)
  let β : L := (g : L)
  refine ⟨LinearMap.toMatrix b b (Algebra.lmul κ L β), fun W hW => ?_⟩

  let e := b.equivFun
  have key : ∀ x : L, (LinearMap.toMatrix b b (Algebra.lmul κ L β)).mulVec (e x) = e (β * x) := by
    intro x
    simpa [e, Module.Basis.equivFun_apply] using LinearMap.toMatrix_mulVec_repr b b (Algebra.lmul κ L β) x

  have stepβ : ∀ x : L, e x ∈ W → e (β * x) ∈ W := fun x hx => key x ▸ hW _ hx
  have stepPow : ∀ n : ℕ, ∀ x : L, e x ∈ W → e (β ^ n * x) ∈ W := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := stepβ _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have stepAll : ∀ y x : L, e x ∈ W → e (y * x) ∈ W := by
    intro y x hx
    by_cases hy : y = 0
    · subst hy; simpa using W.zero_mem
    · obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hg (Units.mk0 y hy))
      have : β ^ n = y := by
        have := congrArg (fun u : Lˣ => (u : L)) hn
        simpa [β] using this
      rw [← this]; exact stepPow n x hx
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hx0 : e.symm v ≠ 0 := by
      intro h0; apply hv0; simpa using congrArg e h0
    have hxW : e (e.symm v) ∈ W := by simpa using hvW
    rw [eq_top_iff]
    intro u _
    have := stepAll (e.symm u * (e.symm v)⁻¹) (e.symm v) hxW
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    simpa using this

end GlobalTheory
