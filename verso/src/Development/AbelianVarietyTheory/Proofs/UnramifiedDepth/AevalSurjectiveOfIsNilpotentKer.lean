import Mathlib

universe u_1 u_2

namespace GlobalTheory.NilpotentKernelSurjective

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `y _`. Take `⟨s, hs, hys⟩` from `h0 y`. Conclude with `⟨s, hs, by simp, by simpa using hys⟩`.

Consider the case `succ n ih`. Introduce `y hy`. Establish `e1 : I ^ n * I ^ 2 = I ^ (n + 1 + 1)` using `by rw [← pow_add]`. Establish `e2 : I ^ (n + 1) * I = I ^ (n + 1 + 1)` using `by rw [← pow_succ]`. Establish `e3 : I ^ (n + 1) * I ^ 2 ≤ I ^ (n + 1 + 1)`.

Rewrite using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega)`. Rewrite `hy` using `[pow_succ]`. Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`.

Take `⟨s, hsS, hsI, hse⟩` from `ih a ha`. Take `⟨t, htS, htI, htf⟩` from `h1 b hb`. Use `⟨s * t, S.mul_mem hsS htS, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hsI htI`.

Establish `hsplit : a * b - s * t = s * (b - t) + (a - s) * t + (a - s) * (b - t)` using `by ring`. Rewrite using `[hsplit]`. Use `Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Rewrite using `[← e1]`. Conclude with `Ideal.mul_mem_mul hsI htf`.

Rewrite using `[← e2]`. Conclude with `Ideal.mul_mem_mul hse htI`. Conclude with `e3 (Ideal.mul_mem_mul hse htf)`. Introduce and unpack `u v ⟨s, hsS, hsI, hsu⟩ ⟨t, htS, htI, htv⟩`. Use `⟨s + t, S.add_mem hsS htS, Ideal.add_mem _ hsI htI, ?_⟩` and prove the remaining obligations.

Establish `hsplit : u + v - (s + t) = (u - s) + (v - t)` using `by ring`. Rewrite using `[hsplit]`. Conclude with `Ideal.add_mem _ hsu htv`.
-/
theorem pow_approx {R : Type u_1} {A : Type u_2} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal A) (S : Subalgebra R A)
    (h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ I)
    (h1 : ∀ y ∈ I, ∃ s ∈ S, s ∈ I ∧ y - s ∈ I ^ 2) (n : ℕ) :
    ∀ y ∈ I ^ n, ∃ s ∈ S, s ∈ I ^ n ∧ y - s ∈ I ^ (n + 1) := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨s, hs, hys⟩ := h0 y
    exact ⟨s, hs, by simp, by simpa using hys⟩
  | succ n ih =>
    intro y hy

    have e1 : I ^ n * I ^ 2 = I ^ (n + 1 + 1) := by rw [← pow_add]
    have e2 : I ^ (n + 1) * I = I ^ (n + 1 + 1) := by rw [← pow_succ]
    have e3 : I ^ (n + 1) * I ^ 2 ≤ I ^ (n + 1 + 1) := by
      rw [← pow_add]
      exact Ideal.pow_le_pow_right (by omega)
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨s, hsS, hsI, hse⟩ := ih a ha
      obtain ⟨t, htS, htI, htf⟩ := h1 b hb
      refine ⟨s * t, S.mul_mem hsS htS, ?_, ?_⟩
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hsI htI
      ·
        have hsplit : a * b - s * t = s * (b - t) + (a - s) * t + (a - s) * (b - t) := by ring
        rw [hsplit]
        refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
        · rw [← e1]
          exact Ideal.mul_mem_mul hsI htf
        · rw [← e2]
          exact Ideal.mul_mem_mul hse htI
        · exact e3 (Ideal.mul_mem_mul hse htf)
    · rintro u v ⟨s, hsS, hsI, hsu⟩ ⟨t, htS, htI, htv⟩
      refine ⟨s + t, S.add_mem hsS htS, Ideal.add_mem _ hsI htI, ?_⟩
      have hsplit : u + v - (s + t) = (u - s) + (v - t) := by ring
      rw [hsplit]
      exact Ideal.add_mem _ hsu htv

/- English proof (translation)
Introduce `R A _ _ _ ε hnil d x hx hspan`. Use `set K : Ideal A := RingHom.ker ε with hK`. Use `set S : Subalgebra R A := (MvPolynomial.aeval x).range with hS`. Establish `hxS : ∀ i, x i ∈ S` using `fun i => ⟨MvPolynomial.X i, MvPolynomial.aeval_X x i⟩`. Establish `h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ K`.

Introduce `y`. Use `⟨algebraMap R A (ε y), S.algebraMap_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[hK, RingHom.mem_ker]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ y ∈ K, ∃ s ∈ S, s ∈ K ∧ y - s ∈ K ^ 2`.

Introduce `y hy`. Take `⟨l, hl⟩` from `hspan y hy`. Use `⟨∑ i : Fin d, l i • x i, S.sum_mem fun i _ => S.smul_mem (hxS i) _, K.sum_mem fun i _ => K.smul_of_tower_mem _ (hx i), hl⟩` and prove the remaining obligations. Establish `hall : ∀ k : ℕ, ∀ y : A, ∃ s ∈ S, y - s ∈ K ^ k`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => intro y; exact ⟨0, S.zero_mem, by simp⟩`. Consider the case `succ k ih`. Introduce `y`. Take `⟨s, hsS, hs⟩` from `ih y`.

Take `⟨t, htS, -, ht⟩` from `pow_approx K S h0 h1 k (y - s) hs`. Use `⟨s + t, S.add_mem hsS htS, ?_⟩` and prove the remaining obligations. Establish `hsplit : y - (s + t) = y - s - t` using `by ring`. Rewrite using `[hsplit]`. Conclude with `ht`.

Take `⟨m, hm⟩` from `hnil`. Introduce `y`. Take `⟨s, hsS, hs⟩` from `hall m y`. Rewrite `hs` using `[hm, Submodule.zero_eq_bot, Ideal.mem_bot, sub_eq_zero]`. Take `⟨p, hp⟩` from `hsS`.

Conclude with `⟨p, hp.trans hs.symm⟩`.
-/
theorem aeval_surjective_of_isNilpotent_ker :
    ∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A]
      [inst_2 : Algebra R A] (ε : A →ₐ[R] R), IsNilpotent (RingHom.ker ε) →
      ∀ {d : ℕ} (x : Fin d → A), (∀ (i : Fin d), x i ∈ RingHom.ker ε) →
      (∀ y ∈ RingHom.ker ε, ∃ (l : Fin d → R),
        y - ∑ i : Fin d, l i • x i ∈ RingHom.ker ε ^ (2 : ℕ)) →
      Function.Surjective (⇑(MvPolynomial.aeval x) : MvPolynomial (Fin d) R → A) := by
  intro R A _ _ _ ε hnil d x hx hspan
  set K : Ideal A := RingHom.ker ε with hK
  set S : Subalgebra R A := (MvPolynomial.aeval x).range with hS
  have hxS : ∀ i, x i ∈ S := fun i => ⟨MvPolynomial.X i, MvPolynomial.aeval_X x i⟩

  have h0 : ∀ y : A, ∃ s ∈ S, y - s ∈ K := by
    intro y
    refine ⟨algebraMap R A (ε y), S.algebraMap_mem _, ?_⟩
    rw [hK, RingHom.mem_ker]
    simp

  have h1 : ∀ y ∈ K, ∃ s ∈ S, s ∈ K ∧ y - s ∈ K ^ 2 := by
    intro y hy
    obtain ⟨l, hl⟩ := hspan y hy
    refine ⟨∑ i : Fin d, l i • x i, S.sum_mem fun i _ => S.smul_mem (hxS i) _,
      K.sum_mem fun i _ => K.smul_of_tower_mem _ (hx i), hl⟩

  have hall : ∀ k : ℕ, ∀ y : A, ∃ s ∈ S, y - s ∈ K ^ k := by
    intro k
    induction k with
    | zero => intro y; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro y
      obtain ⟨s, hsS, hs⟩ := ih y
      obtain ⟨t, htS, -, ht⟩ := pow_approx K S h0 h1 k (y - s) hs
      refine ⟨s + t, S.add_mem hsS htS, ?_⟩
      have hsplit : y - (s + t) = y - s - t := by ring
      rw [hsplit]
      exact ht
  obtain ⟨m, hm⟩ := hnil
  intro y
  obtain ⟨s, hsS, hs⟩ := hall m y
  rw [hm, Submodule.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at hs
  obtain ⟨p, hp⟩ := hsS
  exact ⟨p, hp.trans hs.symm⟩

end GlobalTheory.NilpotentKernelSurjective
