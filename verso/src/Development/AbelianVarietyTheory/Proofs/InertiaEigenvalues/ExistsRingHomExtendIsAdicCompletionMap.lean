import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `L _ Q _ C _ i J JC hi hC g hg`. Use `haveI := hC`. Set `ψ : (n : ℕ) → L →+* Q ⧸ (J ^ n).map i` to `fun n => (Ideal.Quotient.mk _).comp i`. Establish `hψ : ∀ n, Function.Surjective (ψ n)`. Introduce `n y`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Take `⟨a, ha⟩` from `hi.surj x n`. Conclude with `⟨a, (Ideal.Quotient.eq.mpr ha).symm⟩`. Establish `hker : ∀ n, RingHom.ker (ψ n) ≤ RingHom.ker ((Ideal.Quotient.mk (JC ^ n)).comp g)`. Introduce `n a ha`.

Establish `h1 : a ∈ J ^ n` using `hi.ker a n (Ideal.Quotient.eq_zero_iff_mem.mp ha)`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h2 : g a ∈ (J ^ n).map g` using `Ideal.mem_map_of_mem g h1`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hg n h2`.

Set `F : (n : ℕ) → Q ⧸ (J ^ n).map i →+* C ⧸ JC ^ n` to `fun n => (Ideal.Quotient.lift (RingHom.ker (ψ n)) ((Ideal.Quotient.mk (JC ^ n)).comp g) (hker n)).comp (RingHom.quotientKerEquivOfSurjective (hψ n)).symm.toRingHom`. Establish `hF : ∀ n a, F n (ψ n a) = Ideal.Quotient.mk (JC ^ n) (g a)`. Introduce `n a`. Establish `: (RingHom.quotientKerEquivOfSurjective (hψ n)).symm (ψ n a) = Ideal.Quotient.mk _ a`. Rewrite using `[RingEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `only [F, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this, Ideal.Quotient.lift_mk]`. Both sides reduce to the same expression. Set `f : (n : ℕ) → Q →+* C ⧸ JC ^ n` to `fun n => (F n).comp (Ideal.Quotient.mk _)`. Establish `hfa : ∀ n x a, x - i a ∈ (J ^ n).map i → f n x = Ideal.Quotient.mk (JC ^ n) (g a)`.

Introduce `n x a h`. Establish `: Ideal.Quotient.mk ((J ^ n).map i) x = ψ n a` using `Ideal.Quotient.eq.mpr h`. Simplify using `only [f, RingHom.comp_apply, this, hF]`. Establish `hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow JC hle).comp (f n) = f m`. Introduce `m n hle`.

Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hi.surj x n`. Establish `ha' : x - i a ∈ (J ^ m).map i` using `Ideal.map_mono (Ideal.pow_le_pow_right hle) ha`. Rewrite using `[RingHom.comp_apply, hfa n x a ha, hfa m x a ha']`. Both sides reduce to the same expression.

Use `⟨IsAdicComplete.liftRingHom JC f hf, RingHom.ext fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← sub_eq_zero]`. Use `IsHausdorff.haus' (I := JC) _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, IsAdicComplete.mk_liftRingHom, hfa n (i a) a (by simp)]`.
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
