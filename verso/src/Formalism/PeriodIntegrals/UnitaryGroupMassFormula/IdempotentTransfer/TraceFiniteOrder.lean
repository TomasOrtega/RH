import Mathlib

noncomputable section

namespace PI.Dv.Tr

open Module

/- English proof (translation)
Establish `hroot : B.charpoly.IsRoot μ` using `(Polynomial.mem_roots (Matrix.charpoly_monic B).ne_zero).mp hμ`. Rewrite `hroot` using `[Polynomial.IsRoot, Matrix.eval_charpoly]`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hroot`. Establish `hsc : Matrix.mulVec (Matrix.scalar n μ) v = μ • v`. Use extensionality with `i`.

Simplify using `[Matrix.scalar_apply, Matrix.mulVec_diagonal]`. Establish `hBv : Matrix.mulVec B v = μ • v`. Rewrite `hv` using `[Matrix.sub_mulVec, sub_eq_zero, hsc]`. Conclude with `hv.symm`. Establish `hpow : ∀ k : ℕ, Matrix.mulVec (B ^ k) v = μ ^ k • v`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]`.

Establish `h1` using `hpow m`. Rewrite `h1` using `[hB, Matrix.one_mulVec]`. Assume the negation of the conclusion as `hne`. Establish `h2 : (1 - μ ^ m) • v = 0` using `by rw [sub_smul, one_smul, ← h1, sub_self]`. Break down `smul_eq_zero.mp h2 with h | h` into its components or cases.

Conclude with `hne (by linear_combination -h)`. Conclude with `hv0 h`.
-/
lemma root_pow_eq_one {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (m : ℕ) (hB : B ^ m = 1) (μ : ℂ)
    (hμ : μ ∈ B.charpoly.roots) : μ ^ m = 1 := by
  have hroot : B.charpoly.IsRoot μ := (Polynomial.mem_roots (Matrix.charpoly_monic B).ne_zero).mp hμ
  rw [Polynomial.IsRoot, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hsc : Matrix.mulVec (Matrix.scalar n μ) v = μ • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hBv : Matrix.mulVec B v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero, hsc] at hv
    exact hv.symm
  have hpow : ∀ k : ℕ, Matrix.mulVec (B ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  have h1 := hpow m
  rw [hB, Matrix.one_mulVec] at h1
  by_contra hne
  have h2 : (1 - μ ^ m) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h | h
  · exact hne (by linear_combination -h)
  · exact hv0 h

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/- English proof (translation)
Set `b` to `Module.finBasis K W`. Use `set A := LinearMap.toMatrix b b f with hAdef`. Use `set B : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := σ.mapMatrix A with hBdef`. Establish `htr : σ (LinearMap.trace K W f) = B.trace`. Rewrite using `[LinearMap.trace_eq_matrix_trace K b, hBdef]`.

Simplify using `[Matrix.trace, map_sum, RingHom.mapMatrix_apply, hAdef]`. Establish `hApow : ∀ k : ℕ, A ^ k = LinearMap.toMatrix b b (f ^ k)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [LinearMap.toMatrix_one]`.

Consider the case `succ k ih => rw [pow_succ, ih, pow_succ, LinearMap.toMatrix_mul]`. Establish `hB : B ^ m = 1`. Rewrite using `[hBdef, ← map_pow, hApow, hf, LinearMap.toMatrix_one, map_one]`. Establish `hroots : ∀ μ ∈ B.charpoly.roots, μ ^ m = 1` using `fun μ hμ => root_pow_eq_one B m hB μ hμ`. Establish `hsum : B.trace = B.charpoly.roots.sum` using `Matrix.trace_eq_sum_roots_charpoly B`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[htr, hsum]`. Use `(norm_multiset_sum_le _).trans ?_` and prove the remaining obligations. Establish `hmap : B.charpoly.roots.map (fun μ => ‖μ‖) = B.charpoly.roots.map (fun _ => (1 : ℝ))` using `Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'`. Rewrite using `[hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]`.

Establish `hc` using `Polynomial.card_roots' B.charpoly`. Rewrite `hc` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Conclude with `hc` after adjusting the coercions. Establish `hint : IsIntegral ℤ (σ (LinearMap.trace K W f))`. Rewrite using `[htr, hsum]`.

Conclude with `IsIntegral.multiset_sum fun μ hμ => IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)`. Conclude with `(isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp hint`.
-/
lemma trace_finite_order (f : Module.End K W) (m : ℕ) (hm : 0 < m) (hf : f ^ m = 1) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K W f)‖ ≤ finrank K W ∧ IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  set A := LinearMap.toMatrix b b f with hAdef
  set B : Matrix (Fin (finrank K W)) (Fin (finrank K W)) ℂ := σ.mapMatrix A with hBdef
  have htr : σ (LinearMap.trace K W f) = B.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b, hBdef]
    simp [Matrix.trace, map_sum, RingHom.mapMatrix_apply, hAdef]
  have hApow : ∀ k : ℕ, A ^ k = LinearMap.toMatrix b b (f ^ k) := by
    intro k
    induction k with
    | zero => simp [LinearMap.toMatrix_one]
    | succ k ih => rw [pow_succ, ih, pow_succ, LinearMap.toMatrix_mul]
  have hB : B ^ m = 1 := by
    rw [hBdef, ← map_pow, hApow, hf, LinearMap.toMatrix_one, map_one]
  have hroots : ∀ μ ∈ B.charpoly.roots, μ ^ m = 1 := fun μ hμ => root_pow_eq_one B m hB μ hμ
  have hsum : B.trace = B.charpoly.roots.sum := Matrix.trace_eq_sum_roots_charpoly B
  constructor
  · rw [htr, hsum]
    refine (norm_multiset_sum_le _).trans ?_
    have hmap : B.charpoly.roots.map (fun μ => ‖μ‖) = B.charpoly.roots.map (fun _ => (1 : ℝ)) :=
      Multiset.map_congr rfl fun μ hμ => Complex.norm_eq_one_of_pow_eq_one (hroots μ hμ) hm.ne'
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
    have hc := Polynomial.card_roots' B.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hc
    exact_mod_cast hc
  · have hint : IsIntegral ℤ (σ (LinearMap.trace K W f)) := by
      rw [htr, hsum]
      exact IsIntegral.multiset_sum fun μ hμ =>
        IsIntegral.of_pow hm (by rw [hroots μ hμ]; exact isIntegral_one)
    exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).mp hint

end PI.Dv.Tr
