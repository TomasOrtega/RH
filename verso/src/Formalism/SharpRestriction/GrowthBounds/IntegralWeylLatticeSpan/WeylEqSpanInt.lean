import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Lemmata.GeneralBFactLeftSide.Imports

open MvPolynomial Matrix Formalism.GradedWeylDivisibility

noncomputable section

namespace Formalism.L2.G.RelativeIndexFlags.Core

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem prodSpan {O A I : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype I] [DecidableEq I]
    {B : I → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module O (B i)] (ε : ∀ i, B i →ₗ[O] A) (T : ∀ i, Set (B i)) :
    Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ Submodule.span O (T i)) ∧ X = ∏ i, ε i (F i)} =
      Submodule.span O {X | ∃ F : ∀ i, B i, (∀ i, F i ∈ T i) ∧ X = ∏ i, ε i (F i)} := by
  first | exact Bl.general_b_fact_left'''''.goal1 .. | (apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left'''''.goal1 <;> assumption) | (apply @Bl.general_b_fact_left'''''.goal1 <;> first | assumption | infer_instance)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (F : MvPolynomial (Fin r × Fin n) R) :
    MvPolynomial.map φ (rowAct R g F) = rowAct S (g.map φ) (MvPolynomial.map φ F) := by
  have h : (MvPolynomial.map φ).comp (rowAct R (n := n) g).toRingHom =
      (rowAct S (n := n) (g.map φ)).toRingHom.comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [rowAct]
    · intro x
      simp [rowAct]
  exact RingHom.congr_fun h F

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem rowAct_one {R : Type} [CommRing R] {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) R) :
    rowAct R (1 : Matrix (Fin r) (Fin r) R) F = F := by
  have e : rowAct R (n := n) (1 : Matrix (Fin r) (Fin r) R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [rowAct, aeval_X, AlgHom.id_apply]
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e]; rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem rowAct_cancel {R : Type} [CommRing R] {r n : ℕ} (g gi : Matrix (Fin r) (Fin r) R) (h : gi * g = 1)
    (F : MvPolynomial (Fin r × Fin n) R) : rowAct R g (rowAct R gi F) = F := by
  have h1 := rowActMul R r n g gi
  rw [h] at h1
  have h2 := congrArg (fun f => f F) h1
  simp only [AlgHom.comp_apply] at h2
  rw [h2, rowAct_one]

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result.

Supply the required witnesses or components. Treat this case separately. Treat this case separately. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_mem_weyl {O : Type} [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℤ) (hf : f ∈ weyl ℤ r n hn ν) :
    MvPolynomial.map (Int.castRingHom O) f ∈ weyl O r n hn ν := by
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨w, by rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e1 : MvPolynomial.map (Int.castRingHom O) (c • x) = (c : O) • MvPolynomial.map (Int.castRingHom O) x := by
      rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]; rfl
    rw [e1]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem weyl_eq_span_int (O : Type) [CommRing O] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    weyl O r n hn ν = Submodule.span O ((fun f => MvPolynomial.map (Int.castRingHom O) f) ''
      (weyl ℤ r n hn ν : Set (MvPolynomial (Fin r × Fin n) ℤ))) := by
  apply le_antisymm
  · show Submodule.span O (Set.range fun w : List (Fin r × Fin r × ℕ) => applyWord O w (hw O hn ν)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    apply Submodule.subset_span
    exact ⟨applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, by
      show MvPolynomial.map (Int.castRingHom O) (applyWord ℤ w (hw ℤ hn ν)) = _
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact map_mem_weyl hn ν f hf

end Formalism.L2.G.RelativeIndexFlags.Core
