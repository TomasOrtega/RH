import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section

open PowerSeries

namespace GlobalTheory.Col

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace b, Matrix.trace]`. Establish `hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0`. Introduce `j`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]`. Distinguish the cases in `h : (i : ℕ) + j < p`.

Rewrite using `[← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]`. Distinguish the cases in `hi : (i : ℕ) = 0`. Rewrite using `[if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]`. Rewrite using `[if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]`. Establish `e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩`.

Rewrite using `[hb, Algebra.smul_def, ← hx, ← pow_add]`. Use `congr 1`. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Matrix.diag, hd]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem trace_basis_pow {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (i : Fin p) :
    Algebra.trace B A (b i) = if (i : ℕ) = 0 then (p : B) else 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0 := by
    intro j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]
    by_cases h : (i : ℕ) + j < p
    · rw [← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]
      · rw [if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]
    · have e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩ := by
        rw [hb, Algebra.smul_def, ← hx, ← pow_add]
        congr 1
        simp only [Fin.val_mk]
        omega
      rw [e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]
      · omega
      · simp only [Fin.ext_iff]
        omega
  simp only [Matrix.diag, hd]
  split_ifs <;> simp

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr s]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single ⟨0, hp⟩]`. Simplify using `[mul_comm]`.

Introduce `j _ hj`. Rewrite using `[if_neg, mul_zero]`. Introduce `h0`. Conclude with `hj (Fin.ext h0)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem trace_eq_p_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) :
    Algebra.trace B A s = (p : B) * b.repr s ⟨0, hp⟩ := by
  conv_lhs => rw [← b.sum_repr s]
  rw [map_sum]
  simp only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp [mul_comm]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro h0
    exact hj (Fin.ext h0)
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `e : (p : A) ^ k * s = ((p : B) ^ k) • s`. Rewrite using `[Algebra.smul_def, map_pow, map_natCast]`. Rewrite using `[e, Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul, ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Use `⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) • (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_one_add_pow_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : B, Algebra.norm B (1 + (p : A) ^ k * s) = 1 + (p : B) ^ (k + 1) * t := by
  have e : (p : A) ^ k * s = ((p : B) ^ k) • s := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul, Matrix.det_one_add_smul,
    ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) •
    (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩
  ring

/- English proof (translation)
Use `letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra`. Establish `hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X)`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Conclude with `(phi_one_add_X (R := R) p hp.out.pos).symm`. Establish `hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z` using `fun z => rfl`.

Take `⟨u, rfl⟩` from `hu`. Establish `h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r))`. Establish `hui` using `u.mul_inv`. Take the linear combination `he - ((p : PowerSeries R) ^ k * r) * hui`. Take `⟨t, ht⟩` from `@norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X) hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk`.

Use `⟨normOp p (u : PowerSeries R) * t, ?_⟩` and prove the remaining obligations. Rewrite using `[h1, hN, hN, map_mul, ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normOp_congr_of_basis (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule))
    (hb : ∀ i, b i = (1 + X : PowerSeries R) ^ (i : ℕ))
    (h₁ h₂ r : PowerSeries R) (k : ℕ) (hk : 1 ≤ k) (hu : IsUnit h₂)
    (he : h₁ = h₂ + (p : PowerSeries R) ^ k * r) :
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  have hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (phi_one_add_X (R := R) p hp.out.pos).symm
  have hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z := fun z => rfl
  obtain ⟨u, rfl⟩ := hu
  have h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r)) := by
    have hui := u.mul_inv
    linear_combination he - ((p : PowerSeries R) ^ k * r) * hui
  obtain ⟨t, ht⟩ := @norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X)
    hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk
  refine ⟨normOp p (u : PowerSeries R) * t, ?_⟩
  rw [h1, hN, hN, map_mul, ht]
  ring

end GlobalTheory.Col
