import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Disc

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem eq_zero_of_lt_one {L : Type} [Field L] [NumberField L] (a : 𝓞 L)
    (h : ∀ w : InfinitePlace L, w (a : L) < 1) : a = 0 := by
  classical
  by_contra ha
  have hn : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ a : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs hn
    exact_mod_cast this
  have h2 := prod_eq_abs_norm (a : L)
  rw [← Algebra.coe_norm_int] at h2
  have h3 : ∏ w : InfinitePlace L, w (a : L) ^ w.mult < 1 := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)]
    have hp : ∏ w ∈ Finset.univ.erase w0, w (a : L) ^ w.mult ≤ 1 :=
      Finset.prod_le_one (fun w _ => pow_nonneg (apply_nonneg _ _) _)
        (fun w _ => pow_le_one₀ (apply_nonneg _ _) (h w).le)
    have hw0 : w0 (a : L) ^ w0.mult < 1 :=
      pow_lt_one₀ (apply_nonneg _ _) (h w0) InfinitePlace.mult_pos.ne'
    calc _ ≤ w0 (a : L) ^ w0.mult * 1 :=
          mul_le_mul_of_nonneg_left hp (pow_nonneg (apply_nonneg _ _) _)
      _ < 1 := by rw [mul_one]; exact hw0
  rw [h2] at h3
  push_cast at h3
  linarith

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_entry {L : Type} [Field L] [NumberField L] {N : ℕ} (w : InfinitePlace L) (i j : Fin N) :
    Continuous fun x : Sp L N => mt x w i j := by
  fun_prop

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_latS {L : Type} [Field L] [NumberField L] {N : ℕ} (σ : SpecialLinearGroup (Fin N) (𝓞 L))
    (w : InfinitePlace L) (i j : Fin N) :
    mt ((MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w)) σ) w i j =
      w.embedding (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j : 𝓞 L) : L) := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countable_O (L : Type) [Field L] [NumberField L] : Countable (𝓞 L) :=
  (RingOfIntegers.basis L).equivFun.injective.countable

end PositivityTheory.KB.MomentRationality.Disc

namespace PositivityTheory.KB

open MomentRationality MomentRationality.Disc

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Substitute using the available equality.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem discrete_specialLinearGroup_ringOfIntegers : SDisc := by
  intro L _ _ N
  refine ⟨?_, ?_⟩
  · rw [discreteTopology_iff_isOpen_singleton_one]
    let U : Set (Sp L N) :=
      {x | ∀ w i j, ‖mt x w i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j‖ < 1}
    have hU : IsOpen U := by
      simp only [U, Set.setOf_forall]
      exact isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun i =>
        isOpen_iInter_of_finite fun j =>
          isOpen_lt ((continuous_entry w i j).sub continuous_const).norm continuous_const
    refine isOpen_induced_iff.2 ⟨U, hU, ?_⟩
    ext ⟨γ, hγ⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγU
      obtain ⟨σ, rfl⟩ := hγ
      have hσ : σ = 1 := by
        refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
        have h0 := eq_zero_of_lt_one
          (((σ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) - (1 : Matrix (Fin N) (Fin N) (𝓞 L)) i j) (fun w => ?_)
        · simpa using sub_eq_zero.1 h0
        · have h1 := hγU w i j
          rw [mt_latS] at h1
          rw [← norm_embedding_eq]
          convert h1 using 2
          by_cases hij : i = j
          · subst hij
            simp
          · simp [Matrix.one_apply, hij]
      subst hσ
      apply Subtype.ext
      simp
    · intro h
      have h' : γ = 1 := congrArg Subtype.val h
      subst h'
      intro w i j
      have hone : mt (1 : Sp L N) w = 1 := rfl
      rw [hone, sub_self, norm_zero]
      exact one_pos
  · haveI := countable_O L
    haveI : Countable (Matrix (Fin N) (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable (Fin N → Fin N → 𝓞 L))
    haveI : Countable (SpecialLinearGroup (Fin N) (𝓞 L)) :=
      inferInstanceAs (Countable {A : Matrix (Fin N) (Fin N) (𝓞 L) // A.det = 1})
    exact (MonoidHom.rangeRestrict_surjective
      (MonoidHom.pi fun w : InfinitePlace L => SpecialLinearGroup.map (n := Fin N) (embO w))).countable

end PositivityTheory.KB

end
