import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FfHSelfOfSnd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdInertClosed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensFFS

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem keySplit (x : ℝ) (hx : x ≠ 0) (n : ℕ) :
    (x ^ 2) ^ (n + 1) - (2 * x ^ (n + 1) - 1) - (x - 1) * (x ^ (2 * n + 1) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) =
      x ^ (2 * n + 1) * ((1 - x ^ (-(n : ℤ))) * (1 - x ^ (-((n + 1 : ℕ) : ℤ)))) := by
  rw [_root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast]
  have hxn : x ^ n ≠ 0 := pow_ne_zero _ hx
  have hxn1 : x ^ (n + 1) ≠ 0 := pow_ne_zero _ hx
  field_simp
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Prove the second alternative. Prove the first alternative. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Supply the required witnesses or components. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem dcount_split {k : Type} [Field k] [Finite k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k)) {a' : ℕ}
    (haM : a' ≤ M) (T0 : Matrix (Fin a') (Fin a') (k × k)) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → k × k) (hY : ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J Y = T0) :
    Nat.card {x : Fin M → k × k // (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0} + 1 =
      2 * Nat.card k ^ (M - a') := by
  classical
  have := Fintype.ofFinite k
  have hk0 : 0 < Nat.card k := Nat.card_pos
  have e2 : Nat.card k ^ M = Nat.card k ^ (M - a') * Nat.card k ^ a' := by
    rw [← pow_add, Nat.sub_add_cancel haM]
  have h1 := card_half_snd J T0 hu Y hY
  have h2 := card_half_fst J T0 hu Y hY
  rw [e2] at h1 h2
  have c1 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h1
  have c2 := Nat.eq_of_mul_eq_mul_right (pow_pos hk0 _) h2
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at c1 c2 ⊢
  set s1 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).2 = 0)
  set s2 := Finset.univ.filter (fun x : Fin M → k × k =>
    (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧ ∀ l, (x l).1 = 0)
  have hs : Finset.univ.filter (fun x : Fin M → k × k =>
      (∀ j, ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J (Y j) x = 0) ∧
      ffH (RingEquiv.prodComm (R := k) (S := k)).toRingHom J x x = 0 ∧ ¬ ∀ c : k × k, c • x = 0 → c = 0) =
      s1 ∪ s2 := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
    rw [notFree_iff]
    constructor
    · rintro ⟨hP, _, h | h⟩
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl ⟨hP, h⟩
    · rintro (⟨hP, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, ffH_self_of_snd J x h, Or.inr h⟩
      · exact ⟨hP, ffH_self_of_fst J x h, Or.inl h⟩
  have hi : s1 ∩ s2 = {0} := by
    ext x
    simp only [s1, s2, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h2⟩, ⟨_, h1⟩⟩
      funext l; exact Prod.ext (h1 l) (h2 l)
    · rintro rfl
      exact ⟨⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩, ⟨fun j => ffH_zero_right _ _ _, fun l => rfl⟩⟩
  have hu2 := Finset.card_union_add_card_inter s1 s2
  rw [hi, Finset.card_singleton, c1, c2] at hu2
  rw [hs, hu2]
  ring

end PI.OmVe
