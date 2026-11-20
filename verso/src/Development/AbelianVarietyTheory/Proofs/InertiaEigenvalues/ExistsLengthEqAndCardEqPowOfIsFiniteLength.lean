import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨I, hI, ⟨e⟩⟩` from `(isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›`. Establish `hI' : I = IsLocalRing.maximalIdeal O` using `IsLocalRing.eq_maximalIdeal hI`. Substitute `hI'` using the available equality. Conclude with `Nat.card_congr e.toEquiv`.
-/
private lemma card_eq_card_residueField_of_isSimpleModule' (O : Type) [CommRing O]
    [IsLocalRing O] (S : Type) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `@of_subsingleton M _ _ _`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using (Module.length_eq_zero_iff (R := O) (M := M)).mpr ‹_›`. Simplify using `[Nat.card_of_subsingleton (0 : M)]`.

Consider the case `@of_simple_quotient M _ _ N _ _ ih`. Take `⟨n, hl, hc⟩` from `ih`. Use `⟨n + 1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]`. Express the relevant statement in the definitionally equal form `Nat.card (M ⧸ N) * Nat.card N = _`. Rewrite using `[card_eq_card_residueField_of_isSimpleModule' O (M ⧸ N), hc, pow_succ, mul_comm]`.
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
The claim follows from `_root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)`.
-/
theorem _root_.GlobalTheory.exists_length_eq_and_card_eq_pow (O : Type) [CommRing O] [IsLocalRing O]
    (M : Type) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  _root_.GlobalTheory.exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end GlobalTheory
