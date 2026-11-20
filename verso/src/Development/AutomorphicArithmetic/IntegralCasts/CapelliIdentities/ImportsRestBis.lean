import Mathlib

namespace CommutingFamilyCommonEigenvector

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
private lemma key {E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
    (T : I → Module.End ℂ E) (hc : ∀ (a b : I), Commute (T a) (T b))
    (W : Submodule ℂ E) (hW : W ≠ ⊥) (hinv : ∀ i, ∀ x ∈ W, T i x ∈ W)
    (hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W')
    (i : I) (w : E) (hw : w ∈ W) : ∃ μ : ℂ, T i w = μ • w := by
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
  let f : Module.End ℂ W := (T i).restrict (fun x hx => hinv i x hx)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨μ, ?_⟩
  let W' : Submodule ℂ E := W ⊓ (T i).eigenspace μ
  have hW'le : W' ≤ W := inf_le_left
  have hvW' : (v : E) ∈ W' := by
    refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
    rw [Module.End.mem_eigenspace_iff]
    have := hv.apply_eq_smul
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  have hvne : (v : E) ≠ 0 := by
    intro h; apply hv.2; exact Subtype.ext h
  have hW'ne : W' ≠ ⊥ := by
    intro h; rw [h] at hvW'; exact hvne ((Submodule.mem_bot ℂ).mp hvW')
  have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
    intro j x hx
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hinv j x hx'.1, ?_⟩
    have hx2 : T i x = μ • x := Module.End.mem_eigenspace_iff.mp hx'.2
    rw [Module.End.mem_eigenspace_iff]
    have hcom : T i (T j x) = T j (T i x) := by
      have := hc i j
      exact congrArg (fun g : Module.End ℂ E => g x) this.eq
    rw [hcom, hx2, map_smul]
  have heq : W' = W :=
    Submodule.eq_of_le_of_finrank_le hW'le (hmin W' hW'ne hW'inv)
  have : w ∈ W' := heq ▸ hw
  exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp this).2

end CommutingFamilyCommonEigenvector

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.Ygb8.main :
    ∀ (d : ℕ) (E : Type) [inst : AddCommGroup E] [inst_1 : _root_.Module ℂ E] [FiniteDimensional ℂ E] {I : Type}
      (T : I → Module.End ℂ E),
      (∀ (a b : I), Commute (T a) (T b)) →
        Module.finrank ℂ E = d → (0 : ℕ) < d → ∃ (w : E), w ≠ (0 : E) ∧ ∃ (c : I → ℂ), ∀ (i : I), (T i : E → E) w = c i • w := by
  intro d E _ _ _ I T hc hd hpos
  classical
  let P : ℕ → Prop := fun n => ∃ W : Submodule ℂ E, W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, T i x ∈ W) ∧
    Module.finrank ℂ W = n
  have hex : ∃ n, P n := by
    refine ⟨Module.finrank ℂ (⊤ : Submodule ℂ E), ⊤, ?_, fun i x _ => Submodule.mem_top, rfl⟩
    intro h
    have : Module.finrank ℂ (⊤ : Submodule ℂ E) = 0 := by rw [h]; simp
    rw [finrank_top] at this
    omega
  obtain ⟨W, hW, hinv, hWr⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ E, W' ≠ ⊥ → (∀ i, ∀ x ∈ W', T i x ∈ W') →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWr]
    exact Nat.find_min' hex ⟨W', h1, h2, rfl⟩
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨w, hw0, fun i => Classical.choose (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW), ?_⟩
  intro i
  exact Classical.choose_spec (CommutingFamilyCommonEigenvector.key T hc W hW hinv hmin i w hwW)
