import Development.EtaleCohomology.EtaleSheaves.HensIdemCut

noncomputable section
open Polynomial

namespace LateralTheory.E.LMonicPf

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[coeff_map, coeff_X_pow]`. Use `split_ifs with hi`. Substitute `hi` using the available equality. Rewrite using `[hp.coeff_natDegree, map_one]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (h i hi)`.
-/
theorem map_mk_eq_X_pow {A : Type} [CommRing A] (I : Ideal A) (p : A[X]) (hp : p.Monic)
    (h : ∀ i ≠ p.natDegree, p.coeff i ∈ I) :
    p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
  ext i
  rw [coeff_map, coeff_X_pow]
  split_ifs with hi
  · subst hi; rw [hp.coeff_natDegree, map_one]
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i hi)

/- English proof (translation)
Introduce `A _ I B _ φ hφ b hb`. Consider the cases of `subsingleton_or_nontrivial A`. Establish `: Subsingleton B`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_one x, ← mul_one y, ← map_one φ, Subsingleton.elim (1 : A) 0, map_zero, mul_zero, mul_zero]`.

Conclude with `⟨0, 1, monic_one, Subsingleton.elim _ _, by simp⟩`. Set `` to `φ.toAlgebra`. Establish `: Algebra.IsIntegral A B` using `⟨hφ⟩`. Take `⟨p, hpm, hp0, hpI⟩` from `exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B) (I := I) (x := b * b - b) hb`. Establish `hqe : ((X : A[X]) * X - X) = X ^ 2 - X` using `by rw [sq]`.

Establish `hq : ((X : A[X]) * X - X).Monic`. Rewrite using `[hqe]`. Conclude with `monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))`. Establish `hqd : ((X : A[X]) * X - X).natDegree ≠ 0`. Introduce `h`.

Establish `h1` using `congrArg (eval 0) ((Polynomial.Monic.natDegree_eq_zero hq).mp h)`. Simplify using `at h1`. Use `⟨p.natDegree, p.comp (X * X - X), hpm.comp hq hqd, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_comp]`. Simplify using `only [eval₂_mul, eval₂_sub, eval₂_X]`.

Rewrite `hp0` using `[aeval_def]`. Conclude with `hp0`. Rewrite using `[Polynomial.map_comp, map_mk_eq_X_pow I p hpm hpI, X_pow_comp, ← mul_pow]`. Use `congr 1`. Simplify using `[C_1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem LMonic_of : LateralTheory.E.HensIdemCut.LMonic := by
  intro A _ I B _ φ hφ b hb
  cases subsingleton_or_nontrivial A
  · have : Subsingleton B := by
      refine ⟨fun x y => ?_⟩
      rw [← mul_one x, ← mul_one y, ← map_one φ, Subsingleton.elim (1 : A) 0, map_zero,
        mul_zero, mul_zero]
    exact ⟨0, 1, monic_one, Subsingleton.elim _ _, by simp⟩
  let := φ.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hφ⟩
  obtain ⟨p, hpm, hp0, hpI⟩ :=
    exists_monic_aeval_eq_zero_forall_mem_of_mem_map (R := A) (S := B) (I := I) (x := b * b - b) hb
  have hqe : ((X : A[X]) * X - X) = X ^ 2 - X := by rw [sq]
  have hq : ((X : A[X]) * X - X).Monic := by
    rw [hqe]
    exact monic_X_pow_sub (degree_X_le.trans_lt (by norm_num))
  have hqd : ((X : A[X]) * X - X).natDegree ≠ 0 := by
    intro h
    have h1 := congrArg (eval 0) ((Polynomial.Monic.natDegree_eq_zero hq).mp h)
    simp at h1
  refine ⟨p.natDegree, p.comp (X * X - X), hpm.comp hq hqd, ?_, ?_⟩
  · rw [eval₂_comp]
    simp only [eval₂_mul, eval₂_sub, eval₂_X]
    rw [aeval_def] at hp0
    exact hp0
  · rw [Polynomial.map_comp, map_mk_eq_X_pow I p hpm hpI, X_pow_comp, ← mul_pow]
    congr 1
    simp [C_1]
    ring
end LateralTheory.E.LMonicPf
