import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.MemSmulLat

noncomputable section
open Classical Polynomial

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J

open Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

section Abstract

variable {E : Type} [Field E] [CharZero E] [StarRing E]

/- English proof (translation)
Introduce `h`. Establish `e : star ((1:E) + t * s) = 1 - t * s`. Rewrite using `[star_add, star_one, star_mul, hs, star_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (1:E) - t * s = 0` using `by rw [← e, h, star_zero]`.

Establish `h3 : (2:E) = 0` using `by linear_combination h + h2`. Conclude with `two_ne_zero h3`.
-/
theorem one_add_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) + t * s ≠ 0 := by
  intro h
  have e : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) - t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

/- English proof (translation)
Introduce `h`. Establish `e : star ((1:E) - t * s) = 1 + t * s`. Rewrite using `[star_sub, star_one, star_mul, hs, star_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (1:E) + t * s = 0` using `by rw [← e, h, star_zero]`.

Establish `h3 : (2:E) = 0` using `by linear_combination h + h2`. Conclude with `two_ne_zero h3`.
-/
theorem one_sub_ne (s : E) (hs : star s = -s) (t : ℕ) : (1 : E) - t * s ≠ 0 := by
  intro h
  have e : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  have h2 : (1:E) + t * s = 0 := by rw [← e, h, star_zero]
  have h3 : (2:E) = 0 := by linear_combination h + h2
  exact two_ne_zero h3

def cay (s : E) (t : ℕ) : E := (1 + t * s) / (1 - t * s)

/- English proof (translation)
Unfold `cay`. Establish `h1` using `one_add_ne s hs t`. Establish `h2` using `one_sub_ne s hs t`. Establish `e1 : star ((1:E) + t * s) = 1 - t * s`. Rewrite using `[star_add, star_one, star_mul, hs, star_natCast]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : star ((1:E) - t * s) = 1 + t * s`. Rewrite using `[star_sub, star_one, star_mul, hs, star_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[star_div₀, e1, e2, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1 h2)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cay_norm (s : E) (hs : star s = -s) (t : ℕ) : star (cay s t) * cay s t = 1 := by
  unfold cay
  have h1 := one_add_ne s hs t
  have h2 := one_sub_ne s hs t
  have e1 : star ((1:E) + t * s) = 1 - t * s := by
    rw [star_add, star_one, star_mul, hs, star_natCast]; ring
  have e2 : star ((1:E) - t * s) = 1 + t * s := by
    rw [star_sub, star_one, star_mul, hs, star_natCast]; ring
  rw [star_div₀, e1, e2, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  ring

/- English proof (translation)
Introduce `a b hab`. Unfold `cay at hab`. Establish `ha1` using `one_sub_ne s hs a`. Establish `hb1` using `one_sub_ne s hs b`. Rewrite `hab` using `[div_eq_div_iff ha1 hb1]`.

Establish `h0 : ((a:E) - b) * s * 2 = 0` using `by linear_combination hab`. Establish `hab' : ((a:E) - b) = 0`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hs0`. Conclude with `absurd h two_ne_zero`. Conclude with `sub_eq_zero.mp hab'` after adjusting the coercions.
-/
theorem cay_inj (s : E) (hs : star s = -s) (hs0 : s ≠ 0) : Function.Injective (cay s) := by
  intro a b hab
  unfold cay at hab
  have ha1 := one_sub_ne s hs a
  have hb1 := one_sub_ne s hs b
  rw [div_eq_div_iff ha1 hb1] at hab
  have h0 : ((a:E) - b) * s * 2 = 0 := by linear_combination hab
  have hab' : ((a:E) - b) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hs0
    · exact absurd h two_ne_zero
  exact_mod_cast sub_eq_zero.mp hab'

/- English proof (translation)
Set `S : Finset E` to `insert 1 p.roots.toFinset`. Establish `hfin : (cay s ⁻¹' (S : Set E)).Finite` using `S.finite_toSet.preimage (cay_inj s hs hs0).injOn`. Take `⟨t, ht⟩` from `hfin.infinite_compl.nonempty`. Simplify using `only [Set.mem_compl_iff] at ht`. Use `⟨cay s t, cay_norm s hs t, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Apply `ht` to reduce the goal to its premises. Simplify using `[S, h]`. Introduce `h`. Apply `ht` to reduce the goal to its premises.

Simplify using `[S, Polynomial.mem_roots', hp, h]`.
-/
theorem exists_norm_one (s : E) (hs : star s = -s) (hs0 : s ≠ 0) (p : E[X]) (hp : p ≠ 0) :
    ∃ z : E, star z * z = 1 ∧ z ≠ 1 ∧ p.eval z ≠ 0 := by
  classical
  let S : Finset E := insert 1 p.roots.toFinset
  have hfin : (cay s ⁻¹' (S : Set E)).Finite :=
    S.finite_toSet.preimage (cay_inj s hs hs0).injOn
  obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff] at ht
  refine ⟨cay s t, cay_norm s hs t, ?_, ?_⟩
  · intro h
    apply ht
    simp [S, h]
  · intro h
    apply ht
    simp [S, Polynomial.mem_roots', hp, h]

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
Establish `hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0`. Introduce `h`. Establish `h0` using `congrArg (Polynomial.eval 0) h`. Rewrite `h0` using `[eval_charpolyRev', zero_smul, sub_zero, Matrix.det_one, eval_zero]`. Conclude with `one_ne_zero h0`.

Take `⟨z, hz, hz1, hev⟩` from `exists_norm_one s hs hs0 _ hp`. Rewrite `hev` using `[eval_charpolyRev']`. Establish `hu : (z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E`. Rewrite using `[Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, one_mul, mul_comm z, hz, one_smul]`. Establish `hv : (star z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E`.

Rewrite using `[Matrix.mem_unitaryGroup_iff, star_smul, star_one, star_star, smul_mul_smul_comm, one_mul, hz, one_smul]`. Set `u : Matrix.unitaryGroup (Fin n) E` to `⟨_, hu⟩`. Set `v : Matrix.unitaryGroup (Fin n) E` to `⟨_, hv⟩`. Use `⟨v, u * γ, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext show (γ : Matrix (Fin n) (Fin n) E) = (star z • 1) * ((z • 1) * (γ : Matrix (Fin n) (Fin n) E))` to reduce the goal to its premises.

Rewrite using `[← mul_assoc, smul_mul_smul_comm, one_mul, hz, one_smul, one_mul]`. Use `show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0`. Establish `e : (1 : Matrix (Fin n) (Fin n) E) - star z • 1 = (1 - star z) • 1`. Rewrite using `[sub_smul, one_smul]`. Rewrite using `[e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`.

Apply `pow_ne_zero` to reduce the goal to its premises. Introduce `h`. Apply `hz1` to reduce the goal to its premises. Establish `h' : star z = 1` using `(sub_eq_zero.mp h).symm`. Simplify using `using congrArg star h'`.

Use `show (1 - (z • 1) * (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0`. Rewrite using `[smul_mul_assoc, one_mul]` and apply the resulting hypothesis.
-/
theorem split_unitary (s : E) (hs : star s = -s) (hs0 : s ≠ 0) {n : ℕ} (γ : Matrix.unitaryGroup (Fin n) E) :
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) E)).det ≠ 0 := by
  classical
  have hp : (γ : Matrix (Fin n) (Fin n) E).charpolyRev ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    rw [eval_charpolyRev', zero_smul, sub_zero, Matrix.det_one, eval_zero] at h0
    exact one_ne_zero h0
  obtain ⟨z, hz, hz1, hev⟩ := exists_norm_one s hs hs0 _ hp
  rw [eval_charpolyRev'] at hev
  have hu : (z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, smul_mul_smul_comm, one_mul,
      mul_comm z, hz, one_smul]
  have hv : (star z • (1 : Matrix (Fin n) (Fin n) E)) ∈ Matrix.unitaryGroup (Fin n) E := by
    rw [Matrix.mem_unitaryGroup_iff, star_smul, star_one, star_star, smul_mul_smul_comm, one_mul,
      hz, one_smul]
  let u : Matrix.unitaryGroup (Fin n) E := ⟨_, hu⟩
  let v : Matrix.unitaryGroup (Fin n) E := ⟨_, hv⟩
  refine ⟨v, u * γ, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (γ : Matrix (Fin n) (Fin n) E) = (star z • 1) * ((z • 1) * (γ : Matrix (Fin n) (Fin n) E))
    rw [← mul_assoc, smul_mul_smul_comm, one_mul, hz, one_smul, one_mul]
  · show (1 - star z • (1 : Matrix (Fin n) (Fin n) E)).det ≠ 0
    have e : (1 : Matrix (Fin n) (Fin n) E) - star z • 1 = (1 - star z) • 1 := by
      rw [sub_smul, one_smul]
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    apply pow_ne_zero
    intro h
    apply hz1
    have h' : star z = 1 := (sub_eq_zero.mp h).symm
    simpa using congrArg star h'
  · show (1 - (z • 1) * (γ : Matrix (Fin n) (Fin n) E)).det ≠ 0
    rwa [smul_mul_assoc, one_mul]

end Abstract

open Formalism.BasicNotions Formalism.MainNotions NumberField

/- English proof (translation)
Use `letI := D.host.cmStar`. Use `haveI := D.host.isCMField_hostE`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Apply `NumberField.IsCMField.complexConj_ne_one D.host.E` to reduce the goal to its premises.

Use `AlgEquiv.ext fun x => ?_` and prove the remaining obligations. Establish `h` using `hno (x - star x) (by rw [star_sub, star_star]; ring)`. Conclude with `(sub_eq_zero.mp h).symm`.
-/
theorem exists_skew (D : Car) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
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
theorem split_host (D : Car) {n : ℕ} :
    letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
    ∃ γ₁ γ₂ : Matrix.unitaryGroup (Fin n) D.host.E, γ = γ₁ * γ₂ ∧
      (1 - (γ₁ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 ∧ (1 - (γ₂ : Matrix (Fin n) (Fin n) D.host.E)).det ≠ 0 := by
  letI := D.host.cmStar
  intro γ
  obtain ⟨s, hs, hs0⟩ := exists_skew D
  exact split_unitary s hs hs0 γ

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.J
