import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory.SmGL.Segment

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mem_carrier_nu {Δ : Segment k} {s : ℂ} {x : IrrGL k} :
    x ∈ (Δ.nu s).carrier ↔ ∃ a : ℕ, a < Δ.len ∧ Δ.first.nu (s + a) = x := by
  rw [mem_carrier]
  show (∃ a : ℕ, a < Δ.len ∧ (Δ.first.nu s).nu a = x) ↔ _
  simp only [IrrGL.nu_nu]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Prove the second alternative.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem linked_nu_nu_sub_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ) :
    (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  have hd : 0 < Δ.first.1 := Δ.isCusp_first.1
  have inj : ∀ r s : ℝ, Δ.first.nu (r : ℂ) = Δ.first.nu (s : ℂ) → r = s :=
    fun r s h => (IrrGL.nu_ofReal_inj hd).1 h
  refine ⟨⟨ofFirst (Δ.first.nu ((t - 1 : ℝ) : ℂ)) (Δ.isCusp_first.nu _) (Δ.len + 1) (Nat.succ_pos _), ?_⟩, ?_, ?_⟩
  · ext x
    rw [Set.mem_union, mem_carrier_nu, mem_carrier_nu, mem_carrier]
    simp only [first_ofFirst, len_ofFirst, IrrGL.nu_nu]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ha with h | h
      · exact Or.inr ⟨a, h, rfl⟩
      · refine Or.inl ⟨a - 1, by have := Δ.len_pos; omega, ?_⟩
        congr 1
        have h1 : ((a - 1 : ℕ) : ℂ) = (a : ℂ) - 1 := by
          rw [Nat.cast_sub (by have := Δ.len_pos; omega)]; simp
        rw [h1]; push_cast; ring
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · refine ⟨a + 1, by omega, ?_⟩
        congr 1; push_cast; ring
      · exact ⟨a, by omega, rfl⟩
  · intro hsub
    have hm : Δ.first.nu ((t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ)) ∈ (Δ.nu (t : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨Δ.len - 1, by have := Δ.len_pos; omega, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : ((t - 1 : ℝ) : ℂ) + (a : ℂ) = ((t - 1 + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : (t : ℂ) + ((Δ.len - 1 : ℕ) : ℂ) = ((t + ((Δ.len - 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (a : ℝ) = ((Δ.len - 1 : ℕ) : ℝ) + 1 := by linarith
    have h5 : a = Δ.len - 1 + 1 := by exact_mod_cast h4
    have := Δ.len_pos
    omega
  · intro hsub
    have hm : Δ.first.nu (((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ)) ∈ (Δ.nu ((t - 1 : ℝ) : ℂ)).carrier :=
      mem_carrier_nu.2 ⟨0, Δ.len_pos, rfl⟩
    obtain ⟨a, ha, he⟩ := mem_carrier_nu.1 (hsub hm)
    have e1 : (t : ℂ) + (a : ℂ) = ((t + a : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((t - 1 : ℝ) : ℂ) + ((0 : ℕ) : ℂ) = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2] at he
    have h3 := inj _ _ he
    have h4 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith

end GlobalTheory.SmGL.Segment
