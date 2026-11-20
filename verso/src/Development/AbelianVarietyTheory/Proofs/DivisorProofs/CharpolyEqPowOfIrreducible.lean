import Mathlib

open Polynomial

namespace GlobalTheory.CharpolyPowIrred

/- English proof (translation)
Distinguish the cases in `h0 : G = 0`. Substitute `h0` using the available equality. Break down `Nat.eq_zero_or_pos (Fintype.card ι) with h | h` into its components or cases. Establish `: M.charpoly = 1`. Apply `Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic` to reduce the goal to its premises.

Rewrite using `[Matrix.charpoly_natDegree_eq_dim, h]`. Rewrite using `[this, h, pow_zero]`. Rewrite using `[zero_pow h.ne']`. Conclude with `dvd_zero _`. Set `Ω` to `AlgebraicClosure K`.

Set `f` to `algebraMap K Ω`. Rewrite using `[← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]`. Use `set N := M.map f with hNdef`. Establish `hN : aeval N (G.map f) = 0`. Rewrite using `[aeval_map_algebraMap]`.

Use `congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG` as an intermediate fact. Rewrite `this` using `[← aeval_algHom_apply, map_zero]`. Conclude with `this`. Establish `hG0 : G.map f ≠ 0` using `Polynomial.map_ne_zero h0`. Use `(IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_` and prove the remaining obligations.

Rewrite using `[roots_pow, Multiset.le_iff_count]`. Introduce `μ`. Rewrite using `[Multiset.count_nsmul]`. Distinguish the cases in `hμ : μ ∈ N.charpoly.roots`. Establish `h1 : μ ∈ spectrum Ω N`.

Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly]`. Conclude with `isRoot_of_mem_roots hμ`. Establish `h2` using `spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩`. Rewrite `h2` using `[hN]`. Establish `h3 : (G.map f).eval μ = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `(spectrum.mem_iff.1 h2) (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))`. Establish `h4 : 1 ≤ (G.map f).roots.count μ` using `Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Multiset.count_eq_zero.2 hμ]`.

Conclude with `Nat.zero_le _`.
-/
theorem charpoly_dvd_pow_of_aeval {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _

end GlobalTheory.CharpolyPowIrred
