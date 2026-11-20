import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory

noncomputable def LowerGen.offDiagSupport {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ M p.1 p.2 ≠ 0

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem LowerGen.lowerTriangular_elim_step {n : ℕ} (L : Matrix (Fin n) (Fin n) ℂ)
    (hL : L.BlockTriangular OrderDual.toDual) (i j : Fin n) (hij : j < i)
    (hjj : L j j ≠ 0)
    (hmin : ∀ a b : Fin n, b < j → a ≠ b → L a b = 0) (a b : Fin n) :
    (transvection i j (-L i j / L j j) * L) a b = if a = i ∧ b = j then 0 else L a b := by
  by_cases ha : a = i
  · subst ha
    rw [transvection_mul_apply_same]
    have hrow : L j b = if b = j then L j j else 0 := by
      rcases lt_trichotomy b j with h | h | h
      · rw [if_neg h.ne]; exact hmin j b h (Ne.symm h.ne)
      · subst h; simp
      · rw [if_neg h.ne']; exact hL (by simpa using h)
    rw [hrow]
    by_cases hb : b = j
    · subst hb; simp; field_simp; ring
    · simp [hb]
  · rw [transvection_mul_apply_of_ne _ _ _ _ ha]; simp [ha]

end GlobalTheory

open GlobalTheory GlobalTheory.LowerGen in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Consider separately whether the proposition holds or fails. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Substitute using the available equality. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. The claim follows by propositional logic. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem GlobalTheory.lowerTriangular_GL_induction : ∀ {n : ℕ} (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
    (∀ D : GL (Fin n) ℂ, D.val.IsDiag → P D) →
    (∀ (i j : Fin n) (s : ℂ) (T : GL (Fin n) ℂ), j < i → T.val = transvection i j s → P T) →
    ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual → P L := by
  intro n P _h1 hmul hdiag htr
  suffices H : ∀ m : ℕ, ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      (LowerGen.offDiagSupport L.val).card = m → P L by
    intro L hL; exact H _ L hL rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro L hL hm

  have hdet : L.val.det ≠ 0 := by
    have h := congrArg Matrix.det L.mul_inv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdiag0 : ∀ k, L.val k k ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular _ hL] at hdet
    exact fun k => (Finset.prod_ne_zero_iff.mp hdet) k (Finset.mem_univ _)
  by_cases hS : (LowerGen.offDiagSupport L.val) = ∅
  · apply hdiag
    intro a b hab
    by_contra hne
    have : (a, b) ∈ LowerGen.offDiagSupport L.val := by simp [LowerGen.offDiagSupport, hab, hne]
    rw [hS] at this; simp at this
  ·
    have hne : (LowerGen.offDiagSupport L.val).Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    let cols := (LowerGen.offDiagSupport L.val).image Prod.snd
    have hcols : cols.Nonempty := hne.image _
    set j := cols.min' hcols with hjdef
    have hjmem : j ∈ cols := Finset.min'_mem _ _
    obtain ⟨⟨i, jj⟩, hp, hj'⟩ := Finset.mem_image.mp hjmem
    simp only at hj'
    subst hj'
    simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hij, hLij⟩ := hp
    have hlt : j < i := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact absurd (hL (by simpa using h)) hLij
      · exact h
    have hmin : ∀ a b : Fin n, b < j → a ≠ b → L.val a b = 0 := by
      intro a b hb hab
      by_contra hne'
      have hbm : b ∈ cols := Finset.mem_image.mpr
        ⟨(a, b), by simp [LowerGen.offDiagSupport, hab, hne'], rfl⟩
      have := Finset.min'_le cols b hbm
      rw [← hjdef] at this
      exact absurd hb (not_lt.mpr this)
    set c : ℂ := -L.val i j / L.val j j with hc
    have hijne : i ≠ j := hij
    let U : GL (Fin n) ℂ := ⟨transvection i j c, transvection i j (-c),
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    let V : GL (Fin n) ℂ := ⟨transvection i j (-c), transvection i j c,
      by rw [transvection_mul_transvection_same _ _ hij]; simp,
      by rw [transvection_mul_transvection_same _ _ hij]; simp⟩
    have hentry := LowerGen.lowerTriangular_elim_step L.val hL i j hlt (hdiag0 j) hmin
    have hUL : ∀ a b, (U * L).val a b = if a = i ∧ b = j then 0 else L.val a b := by
      intro a b; exact hentry a b
    have hlowUL : (U * L).val.BlockTriangular OrderDual.toDual := by
      intro a b hab
      rw [hUL]
      split_ifs with h
      · rfl
      · exact hL hab
    have hsupp : LowerGen.offDiagSupport (U * L).val = (LowerGen.offDiagSupport L.val).erase (i, j) := by
      ext ⟨a, b⟩
      simp only [LowerGen.offDiagSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, hUL, ne_eq, Prod.mk.injEq]
      by_cases h : a = i ∧ b = j
      · simp [h]
      · simp only [h, if_false]; tauto
    have hcard : (LowerGen.offDiagSupport (U * L).val).card < m := by
      rw [hsupp, ← hm]
      apply Finset.card_erase_lt_of_mem
      simp [LowerGen.offDiagSupport, hij, hLij]
    have hPUL : P (U * L) := ih _ hcard _ hlowUL rfl
    have hPV : P V := htr i j (-c) V hlt rfl
    have hVUL : V * (U * L) = L := by
      rw [← mul_assoc]
      have : V * U = 1 := by
        ext : 1
        show transvection i j (-c) * transvection i j c = 1
        rw [transvection_mul_transvection_same _ _ hij]; simp
      rw [this, one_mul]
    rw [← hVUL]
    exact hmul _ _ hPV hPUL
