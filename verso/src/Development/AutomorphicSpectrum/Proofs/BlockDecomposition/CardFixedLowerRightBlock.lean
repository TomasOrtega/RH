import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntHalf

variable {k : Type} [Field k] {n : ℕ}

def lowH (g : GL (Ix n) k) : Matrix (Fin n) (Ix n) k := g.1.submatrix Sum.inr id

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma lowH_eq (g : GL (Ix n) k) : lowH g = fromCols (lowerLeftBlock g) (dBlk g) := by
  ext i (j | j) <;> simp [lowH, lowerLeftBlock, dBlk, toBlocks₂₁, toBlocks₂₂]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
lemma lowH_mul (g h : GL (Ix n) k) : lowH (g * h) = lowH g * h.1 := by
  ext i j
  simp [lowH, Matrix.mul_apply]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
lemma lowH_one : lowH (1 : GL (Ix n) k) = fromCols 0 1 := by
  ext i (j | j) <;> simp [lowH, Matrix.one_apply]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma rank_lowH (g : GL (Ix n) k) : (lowH g).rank = n := by
  have h : LinearIndependent k g.1.row := Matrix.linearIndependent_rows_of_isUnit g.isUnit
  have h2 : LinearIndependent k (lowH g).row := h.comp Sum.inr Sum.inr_injective
  simpa using h2.rank_matrix

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
lemma exists_lowH (M : Matrix (Fin n) (Ix n) k) (hM : M.rank = n) : ∃ g : GL (Ix n) k, lowH g = M := by
  have hli : LinearIndependent k M.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← M.rank_eq_finrank_span_row, hM]
    simp
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range M.row))
  have hfr : Module.finrank k W' = n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := M.rank_eq_finrank_span_row
    simp at h1
    omega
  let b := Module.finBasisOfFinrankEq k W' hfr
  let w : Fin n → (Ix n → k) := fun i => (b i : Ix n → k)
  have hw : LinearIndependent k w := b.linearIndependent.map' W'.subtype (Submodule.ker_subtype _)
  have hspan : Submodule.span k (Set.range w) ≤ W' := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  have hall : LinearIndependent k (Sum.elim w M.row) :=
    LinearIndependent.sum_type hw hli (Disjoint.mono_left hspan hW'.disjoint.symm)
  let A : Matrix (Ix n) (Ix n) k := Matrix.of (Sum.elim w M.row)
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hall
  refine ⟨hA.unit, ?_⟩
  ext i j
  rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma card_fibre (g₀ : GL (Ix n) k) :
    Nat.card {g : GL (Ix n) k // lowH g = lowH g₀} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight g₀⁻¹) ?_)
  intro g
  have hone : lowH g₀ * (g₀⁻¹).1 = fromCols 0 1 := by
    rw [← lowH_mul, mul_inv_cancel, lowH_one]
  have hcd : (lowerLeftBlock (g * g₀⁻¹) = 0 ∧ dBlk (g * g₀⁻¹) = 1) ↔ lowH (g * g₀⁻¹) = fromCols 0 1 := by
    rw [lowH_eq, Matrix.fromCols_inj.eq_iff]
  simp only [Equiv.coe_mulRight]
  rw [hcd, lowH_mul, ← hone]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (· * g₀.1) h
    simpa [Matrix.mul_assoc, ← Units.val_mul] using this

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_lowerRightBlock_eq_fibre_formula (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k) :
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  classical
  haveI : Fintype {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := Fintype.ofFinite _
  let f : {g : GL (Ix n) k // dBlk g = D} → {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} :=
    fun g => ⟨lowerLeftBlock g.1, by have h := rank_lowH g.1; rw [lowH_eq, g.2] at h; exact h⟩
  have hfib : ∀ C, Nat.card {x // f x = C} = Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
    intro C
    obtain ⟨g₀, hg₀⟩ := exists_lowH (Matrix.fromCols C.1 D) C.2
    rw [← card_fibre g₀]
    have hy : ∀ y : {g : GL (Ix n) k // lowH g = lowH g₀},
        Matrix.fromCols (lowerLeftBlock y.1) (dBlk y.1) = Matrix.fromCols C.1 D := by
      intro y
      rw [← lowH_eq, ← hg₀]
      exact y.2
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [hg₀, lowH_eq, x.1.2, show lowerLeftBlock x.1.1 = C.1 from congrArg Subtype.val x.2]
    · exact (Matrix.fromCols_inj (hy y)).2
    · exact Subtype.ext (Matrix.fromCols_inj (hy y)).1
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma,
    Finset.sum_congr rfl (fun C _ => hfib C), Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, mul_comm]

end GlobalTheory.CompanionTheory.Jp.CntHalf
