import Mathlib

namespace GlobalTheory.IntSmulMemSubmodule

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hdc⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hdc⟩
    have h : (d * a) • (c • x) = r • (a • x) := by
      have h1 : r • (a • x) = (d • c) • (a • x) := rfl
      rw [h1, smul_assoc, mul_smul, smul_comm a c x]
    rw [h]
    exact L.smul_mem r hax

end GlobalTheory.IntSmulMemSubmodule
