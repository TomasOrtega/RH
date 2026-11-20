import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.PerIndex

variable {k : Type} [Field k] [ValuativeRel k] {n : Type}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem col_add (n' : Type) {c : ℕ}
    (e f : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    UnfoldShape.col (n' := n') (e + f) i
      = UnfoldShape.col (n' := n') e i + UnfoldShape.col (n' := n') f i := by
  funext r
  simp only [UnfoldShape.col, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem relIndex_perLat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type)
    [Fintype n'] [DecidableEq n'] (c : ℕ) (ϖ : 𝒪[k]) (hϖ : (ϖ : k) ≠ 0)
    (L : Submodule 𝒪[k] (n → k)) :
    (perLat ϖ n' c L).relIndex (perLat ϖ n' c (stdLat k n))
      = (L.toAddSubgroup.relIndex (stdLat k n).toAddSubgroup) ^ c := by
  classical
  let φ : perLat ϖ n' c (stdLat k n) →+ (Fin c → (stdLat k n).toAddSubgroup) :=
    AddMonoidHom.mk' (fun e i => ⟨fun r => ((ϖ : k) ^ ((i : ℕ) + 1) •
      UnfoldShape.col (n' := n') e.1 i) (Sum.inl r), (mem_chainLat.1 (mem_perLat.1 e.2 i)).1⟩)
      (by
        intro e f
        funext i
        apply Subtype.ext
        funext r
        simp only [AddSubgroup.coe_add, Pi.add_apply, col_add, smul_add])
  have hφ : Function.Surjective φ := by
    intro v
    have hY : ∀ i : Fin c, ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1
        ∈ Yle k n c ((i : ℕ) + 1) := by
      intro i
      rw [mem_Yle]
      intro l _
      simp [inX_apply]
    have hc := col_uncol (n' := n') hY
    have hs : ∀ i : Fin c, (ϖ : k) ^ ((i : ℕ) + 1) • UnfoldShape.col (n' := n')
        (uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1) i
        = inX k n c (v i).1 := by
      intro i
      rw [hc, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hϖ), one_smul]
    refine ⟨⟨uncol n' fun i : Fin c => ((ϖ : k) ^ ((i : ℕ) + 1))⁻¹ • inX k n c (v i).1, ?_⟩, ?_⟩
    · rw [mem_perLat]
      intro i
      rw [hs, mem_chainLat]
      refine ⟨?_, fun l => ⟨0, ?_⟩⟩
      · simpa [inX_apply] using (v i).2
      · simp [inX_apply]
    · funext i
      apply Subtype.ext
      funext r
      exact congrFun (hs i) (Sum.inl r)
  have hcomap : (perLat ϖ n' c L).addSubgroupOf (perLat ϖ n' c (stdLat k n))
      = (AddSubgroup.pi Set.univ fun _ : Fin c =>
          L.toAddSubgroup.addSubgroupOf (stdLat k n).toAddSubgroup).comap φ := by
    ext e
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi, mem_perLat]
    constructor
    · intro h i _
      exact (mem_chainLat.1 (h i)).1
    · intro h i
      exact mem_chainLat.2 ⟨h i trivial, (mem_chainLat.1 (mem_perLat.1 e.2 i)).2⟩
  rw [AddSubgroup.relIndex, hcomap, AddSubgroup.index_comap_of_surjective _ hφ,
    AddSubgroup.index_pi]
  simp [AddSubgroup.relIndex]

end GlobalTheory.RootEx.PerIndex
