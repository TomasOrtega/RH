import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

namespace GlobalTheory.BSP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_ringHom_comp_of_isCompl : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C]
    (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsAdicComplete JC C →
    ∀ g : L →+* C, J.map g ≤ JC → ∃ h : Q →+* C, h.comp i = g := by
  intro L _ Q _ C _ i J JC hi hC g hg
  haveI := hC

  let ψ : (n : ℕ) → L →+* Q ⧸ (J ^ n).map i := fun n => (Ideal.Quotient.mk _).comp i
  have hψ : ∀ n, Function.Surjective (ψ n) := by
    intro n y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hi.surj x n
    exact ⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩
  have hker : ∀ n, RingHom.ker (ψ n) ≤ RingHom.ker ((Ideal.Quotient.mk (JC ^ n)).comp g) := by
    intro n a ha
    have h1 : a ∈ J ^ n := hi.ker a n (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    have h2 : g a ∈ (J ^ n).map g := Ideal.mem_map_of_mem g h1
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono hg n h2
  let F : (n : ℕ) → Q ⧸ (J ^ n).map i →+* C ⧸ JC ^ n := fun n =>
    (Ideal.Quotient.lift (RingHom.ker (ψ n)) ((Ideal.Quotient.mk (JC ^ n)).comp g) (hker n)).comp
      (RingHom.quotientKerEquivOfSurjective (hψ n)).symm.toRingHom
  have hF : ∀ n a, F n (ψ n a) = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n a
    have : (RingHom.quotientKerEquivOfSurjective (hψ n)).symm (ψ n a) = Ideal.Quotient.mk _ a := by
      rw [RingEquiv.symm_apply_eq]; rfl
    simp only [F, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this,
      Ideal.Quotient.lift_mk]
    rfl
  let f : (n : ℕ) → Q →+* C ⧸ JC ^ n := fun n => (F n).comp (Ideal.Quotient.mk _)
  have hfa : ∀ n x a, x - i a ∈ (J ^ n).map i → f n x = Ideal.Quotient.mk (JC ^ n) (g a) := by
    intro n x a h
    have : Ideal.Quotient.mk ((J ^ n).map i) x = ψ n a := Ideal.Quotient.eq.mpr h
    simp only [f, RingHom.comp_apply, this, hF]
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow JC hle).comp (f n) = f m := by
    intro m n hle
    refine RingHom.ext fun x => ?_
    obtain ⟨a, ha⟩ := hi.surj x n
    have ha' : x - i a ∈ (J ^ m).map i := Ideal.map_mono (Ideal.pow_le_pow_right hle) ha
    rw [RingHom.comp_apply, hfa n x a ha, hfa m x a ha']
    rfl
  refine ⟨IsAdicComplete.liftRingHom JC f hf, RingHom.ext fun a => ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero]
  refine IsHausdorff.haus' (I := JC) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom,
    hfa n (i a) a (by simp)]

end GlobalTheory.BSP
