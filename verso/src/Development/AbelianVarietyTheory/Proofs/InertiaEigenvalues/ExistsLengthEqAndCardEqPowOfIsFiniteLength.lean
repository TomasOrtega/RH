import Mathlib

namespace GlobalTheory

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
private lemma card_eq_card_residueField_of_isSimpleModule' (O : Type) [CommRing O]
    [IsLocalRing O] (S : Type) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨0, ?_, ?_⟩
    · simpa using (Module.length_eq_zero_iff (R := O) (M := M)).mpr ‹_›
    · simp [Nat.card_of_subsingleton (0 : M)]
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hl, hc⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]
      push_cast
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [card_eq_card_residueField_of_isSimpleModule' O (M ⧸ N), hc, pow_succ, mul_comm]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end GlobalTheory
