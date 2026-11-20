import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf

noncomputable section
open Classical Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

/- English proof (translation)
Introduce `h`. Establish `h2 : (1 : E) - t * s = 0`. Use `congrArg star h` as an intermediate fact. Simplify `this` using `[hs, sub_eq_add_neg]`. Establish `h3 : (2 : E) = 0` using `by linear_combination h + h2`.

Conclude with `two_ne_zero h3`.
-/
theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have h2 : (1 : E) - t * s = 0 := by
    have := congrArg star h
    simpa [hs, sub_eq_add_neg] using this
  have h3 : (2 : E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

/- English proof (translation)
Use `one_add_ne (-s) (by rw [star_neg, hs]) t` as an intermediate fact. Simplify `this` using `[sub_eq_add_neg]`.
-/
theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  have := one_add_ne (-s) (by rw [star_neg, hs]) t
  simpa [sub_eq_add_neg] using this

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

/- English proof (translation)
Establish `h1` using `one_add_ne s hs t`. Establish `h2` using `one_sub_ne s hs t`. Establish `: star (cay s t) = (1 - t * s) / (1 + t * s)`. Unfold `cay`. Rewrite using `[star_div₀]`.

Simplify using `[hs, sub_eq_add_neg]`. Rewrite using `[this]`. Unfold `cay`. Clear the denominators using the available nonvanishing facts.
-/
theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have : star (cay s t) = (1 - t * s) / (1 + t * s) := by
    unfold cay
    rw [star_div₀]
    simp [hs, sub_eq_add_neg]
  rw [this]
  unfold cay
  field_simp

/- English proof (translation)
Introduce `t u h`. Unfold `cay at h`. Rewrite `h` using `[div_eq_div_iff (one_sub_ne s hs t) (one_sub_ne s hs u)]`. Establish `h2 : (2 : E) * s * ((t : E) - u) = 0` using `by linear_combination h`. Establish `h3 : (t : E) - u = 0`.

Break down `mul_eq_zero.mp h2 with h4 | h4` into its components or cases. Conclude with `absurd h4 (mul_ne_zero two_ne_zero hs0)`. Conclude with `h4`. Conclude with `sub_eq_zero.mp h3` after adjusting the coercions.
-/
theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro t u h
  unfold cay at h
  rw [div_eq_div_iff (one_sub_ne s hs t) (one_sub_ne s hs u)] at h
  have h2 : (2 : E) * s * ((t : E) - u) = 0 := by linear_combination h
  have h3 : (t : E) - u = 0 := by
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exact absurd h4 (mul_ne_zero two_ne_zero hs0)
    · exact h4
  exact_mod_cast sub_eq_zero.mp h3

/- English proof (translation)
Establish `hinf` using `Set.infinite_range_of_injective (cay_inj s hs hs0)`. Take `⟨z, ⟨t, rfl⟩, hz⟩` from `hinf.exists_notMem_finset (p.roots.toFinset ∪ {1})`. Rewrite `hz` using `[Finset.mem_union, not_or, Multiset.mem_toFinset, Finset.mem_singleton, mem_roots hp]`. Conclude with `⟨_, cay_norm s hs t, hz.2, hz.1⟩`.
-/
theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  have hinf := Set.infinite_range_of_injective (cay_inj s hs hs0)
  obtain ⟨z, ⟨t, rfl⟩, hz⟩ := hinf.exists_notMem_finset (p.roots.toFinset ∪ {1})
  rw [Finset.mem_union, not_or, Multiset.mem_toFinset, Finset.mem_singleton, mem_roots hp] at hz
  exact ⟨_, cay_norm s hs t, hz.2, hz.1⟩

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, apply_ite]`. Conclude with `mul_comm _ _`.
-/
theorem eval_charpolyRev' {n : ℕ} (M : Matrix (Fin n) (Fin n) E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite]
  exact mul_comm _ _

/- English proof (translation)
Establish `hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0`. Introduce `h`. Use `Matrix.eval_charpolyRev (M := (γ : Matrix (Fin n) (Fin n) E))` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.

Take `⟨z, hz, hz1, hzp⟩` from `exists_norm_one s hs hs0 _ hp`. Establish `hz' : z * star z = 1` using `by rw [mul_comm]; exact hz`. Establish `hu : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1` using `Matrix.mem_unitaryGroup_iff.mp γ.2`. Establish `m1 : z • (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E`. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu, hz', one_smul]`.

Establish `m2 : star z • (1 : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E`. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, star_one, Matrix.mul_one, hz, one_smul]`. Use `⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show (γ : Matrix (Fin n) (Fin n) E) = z • (γ : Matrix (Fin n) (Fin n) E) * star z • (1 : Matrix (Fin n) (Fin n) E)` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hz', one_smul]`.

Use `show (1 - z • (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0`. Rewrite using `[← eval_charpolyRev']`. Conclude with `hzp`. Use `show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0`. Establish `: (1 - star z • (1 : Matrix (Fin n) (Fin n) E)) = (1 - star z) • (1 : Matrix (Fin n) (Fin n) E)`.

Rewrite using `[sub_smul, one_smul]`. Rewrite using `[this, Matrix.det_smul, Matrix.det_one, mul_one]`. Use `pow_ne_zero _ (sub_ne_zero.mpr fun h => hz1 ?_)` and prove the remaining obligations. Use `congrArg star h` as an intermediate fact. Rewrite `this` using `[star_one, star_star]`.

Conclude with `this.symm`.
-/
theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := (γ : Matrix (Fin n) (Fin n) E))
    rw [h] at this
    simp at this
  obtain ⟨z, hz, hz1, hzp⟩ := exists_norm_one s hs hs0 _ hp
  have hz' : z * star z = 1 := by rw [mul_comm]; exact hz
  have hu : (γ : Matrix (Fin n) (Fin n) E) * star (γ : Matrix (Fin n) (Fin n) E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have m1 : z • (γ : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu, hz', one_smul]
  have m2 : star z • (1 : Matrix (Fin n) (Fin n) E) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_star, star_one,
      Matrix.mul_one, hz, one_smul]
  refine ⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = z • (γ : Matrix (Fin n) (Fin n) E) * star z • (1 : Matrix (Fin n) (Fin n) E)
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hz', one_smul]
  · show (1 - z • (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rw [← eval_charpolyRev']; exact hzp
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have : (1 - star z • (1 : Matrix (Fin n) (Fin n) E)) = (1 - star z) • (1 : Matrix (Fin n) (Fin n) E) := by
      rw [sub_smul, one_smul]
    rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
    refine pow_ne_zero _ (sub_ne_zero.mpr fun h => hz1 ?_)
    have := congrArg star h
    rw [star_one, star_star] at this
    exact this.symm

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `haveI := D.host.isCMField_hostE`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Apply `NumberField.IsCMField.complexConj_ne_one D.host.E` to reduce the goal to its premises.

Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Establish `h` using `hno (x - star x) (by rw [star_sub, star_star]; ring)`. Conclude with `(sub_eq_zero.mp h).symm`.
-/
theorem exists_skew (D : D7) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

/- English proof (translation)
Use `letI := D.host.cmStar`. Introduce `γ`. Take `⟨s, hs, hs0⟩` from `exists_skew D`. Conclude with `split_unitary s hs hs0 γ`.
-/
theorem split_host (D : D7) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.PairingIndexBounds.Eq.J
