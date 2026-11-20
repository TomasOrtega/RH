import Mathlib

noncomputable section

open MvPolynomial

namespace PI.HwFix.UnitaryGroupMassFormula

variable {σ : Type*} {K : Type*} [Field K]

def Ge (w : σ → ℕ) (d : ℕ) : Submodule K (MvPolynomial σ K) where
  carrier := {F | ∀ m, Finsupp.weight w m < d → coeff m F = 0}
  add_mem' := by
    intro F G hF hG
    rw [Set.mem_setOf_eq] at hF hG ⊢
    intro m hm
    rw [coeff_add, hF m hm, hG m hm, add_zero]
  zero_mem' := by
    rw [Set.mem_setOf_eq]
    intro m _
    rw [coeff_zero]
  smul_mem' := by
    intro c F hF
    rw [Set.mem_setOf_eq] at hF ⊢
    intro m hm
    rw [coeff_smul, hF m hm, smul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Ge {w : σ → ℕ} {d : ℕ} {F : MvPolynomial σ K} :
    F ∈ Ge w d ↔ ∀ m, Finsupp.weight w m < d → coeff m F = 0 := Iff.rfl

/- English proof (translation)
The claim follows from `mem_Ge.2 fun m hm => mem_Ge.1 hF m (lt_of_lt_of_le hm h)`.
-/
theorem Ge_mono {w : σ → ℕ} {d e : ℕ} (h : d ≤ e) {F : MvPolynomial σ K} (hF : F ∈ Ge w e) : F ∈ Ge w d :=
  mem_Ge.2 fun m hm => mem_Ge.1 hF m (lt_of_lt_of_le hm h)

/- English proof (translation)
Rewrite `hF`, `hG`, the goal using `[mem_Ge]`. Introduce `m hm`. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Use `replace hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp`.

Establish `h : Finsupp.weight w p.1 + Finsupp.weight w p.2 = Finsupp.weight w m` using `by rw [← map_add, hp]`. Distinguish the cases in `h1 : Finsupp.weight w p.1 < a`. Rewrite using `[hF _ h1, zero_mul]`. Rewrite using `[hG _ (by omega), mul_zero]`.
-/
theorem Ge_mul {w : σ → ℕ} {a b : ℕ} {F G : MvPolynomial σ K} (hF : F ∈ Ge w a) (hG : G ∈ Ge w b) :
    F * G ∈ Ge w (a + b) := by
  classical
  rw [mem_Ge] at hF hG ⊢
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have h : Finsupp.weight w p.1 + Finsupp.weight w p.2 = Finsupp.weight w m := by rw [← map_add, hp]
  by_cases h1 : Finsupp.weight w p.1 < a
  · rw [hF _ h1, zero_mul]
  · rw [hG _ (by omega), mul_zero]

/- English proof (translation)
Rewrite using `[mem_Ge]`. Introduce `m' hm'`. Rewrite using `[coeff_monomial, if_neg]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hm'`.
-/
theorem monomial_mem_Ge (w : σ → ℕ) (m : σ →₀ ℕ) (c : K) : monomial m c ∈ Ge w (Finsupp.weight w m) := by
  classical
  rw [mem_Ge]
  intro m' hm'
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact lt_irrefl _ hm'

/- English proof (translation)
Establish `h` using `monomial_mem_Ge (K := K) w (Finsupp.single v 1) 1`. Rewrite `h` using `[Finsupp.weight_single, one_smul]`. Then use the resulting hypothesis.
-/
theorem X_mem_Ge (w : σ → ℕ) (v : σ) : (X v : MvPolynomial σ K) ∈ Ge w (w v) := by
  have h := monomial_mem_Ge (K := K) w (Finsupp.single v 1) 1
  rwa [Finsupp.weight_single, one_smul] at h

/- English proof (translation)
Establish `e : φ (A * B) - A * B = (φ A - A) * (φ B - B) + (φ A - A) * B + A * (φ B - B)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `add_mem (add_mem ?_ ?_) ?_` and prove the remaining obligations.

Conclude with `Ge_mono (by omega) (Ge_mul hA' hB')`. Conclude with `Ge_mono (by omega) (Ge_mul hA' hB)`. Conclude with `Ge_mono (by omega) (Ge_mul hA hB')`.
-/
theorem mul_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) {A B : MvPolynomial σ K} {a b : ℕ}
    (hA : A ∈ Ge w a) (hB : B ∈ Ge w b) (hA' : φ A - A ∈ Ge w (a + 1)) (hB' : φ B - B ∈ Ge w (b + 1)) :
    φ (A * B) - A * B ∈ Ge w (a + b + 1) := by
  have e : φ (A * B) - A * B = (φ A - A) * (φ B - B) + (φ A - A) * B + A * (φ B - B) := by
    rw [map_mul]; ring
  rw [e]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact Ge_mono (by omega) (Ge_mul hA' hB')
  · exact Ge_mono (by omega) (Ge_mul hA' hB)
  · exact Ge_mono (by omega) (Ge_mul hA hB')

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ]`. Establish `hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v)`.

Establish `h` using `monomial_mem_Ge (K := K) w (Finsupp.single v k) 1`. Rewrite `h` using `[Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial]`. Then use the resulting hypothesis. Establish `h` using `mul_step w φ hk (X_mem_Ge w v) ih (hφ v)`. Establish `e : (k + 1) * w v + 1 = k * w v + w v + 1` using `by ring`. Rewrite using `[e]` and apply the resulting hypothesis.
-/
theorem pow_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (v : σ) (k : ℕ) :
    φ (X v ^ k) - X v ^ k ∈ Ge w (k * w v + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v) := by
      have h := monomial_mem_Ge (K := K) w (Finsupp.single v k) 1
      rwa [Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial] at h
    have h := mul_step w φ hk (X_mem_Ge w v) ih (hφ v)
    have e : (k + 1) * w v + 1 = k * w v + w v + 1 := by ring
    rwa [e]

/- English proof (translation)
Proceed by induction on `m using Finsupp.induction with`. Consider the case `zero => simp`. Consider the case `single_add v k f _ _ ih`. Establish `e : (monomial (Finsupp.single v k + f) (1 : K)) = X v ^ k * monomial f 1`. Rewrite using `[X_pow_eq_monomial, monomial_mul, one_mul]`.

Rewrite using `[e]`. Establish `hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v)`. Establish `h` using `monomial_mem_Ge (K := K) w (Finsupp.single v k) 1`. Rewrite `h` using `[Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial]`. Then use the resulting hypothesis. Establish `h` using `mul_step w φ hk (monomial_mem_Ge w f 1) (pow_step w φ hφ v k) ih`.

Rewrite using `[map_add, Finsupp.weight_single, smul_eq_mul]` and apply the resulting hypothesis.
-/
theorem monomial_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (m : σ →₀ ℕ) :
    φ (monomial m 1) - monomial m 1 ∈ Ge w (Finsupp.weight w m + 1) := by
  induction m using Finsupp.induction with
  | zero => simp
  | single_add v k f _ _ ih =>
    have e : (monomial (Finsupp.single v k + f) (1 : K)) = X v ^ k * monomial f 1 := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [e]
    have hk : (X v : MvPolynomial σ K) ^ k ∈ Ge w (k * w v) := by
      have h := monomial_mem_Ge (K := K) w (Finsupp.single v k) 1
      rwa [Finsupp.weight_single, smul_eq_mul, ← X_pow_eq_monomial] at h
    have h := mul_step w φ hk (monomial_mem_Ge w f 1) (pow_step w φ hφ v k) ih
    rwa [map_add, Finsupp.weight_single, smul_eq_mul]

/- English proof (translation)
Establish `key : ∀ m ∈ F.support, φ (monomial m (coeff m F)) - monomial m (coeff m F) ∈ Ge w (d + 1)`. Introduce `m hm`. Establish `hd : d ≤ Finsupp.weight w m`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hm) (mem_Ge.1 hF m (by omega))`.

Establish `e : monomial m (coeff m F) = coeff m F • monomial m (1 : K)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ (Ge_mono (by omega) (monomial_step w φ hφ m))`. Establish `h` using `Submodule.sum_mem _ key`.

Rewrite `h` using `[Finset.sum_sub_distrib, ← map_sum, ← F.as_sum]`. Then use the resulting hypothesis.
-/
theorem uni_step (w : σ → ℕ) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K)
    (hφ : ∀ v, φ (X v) - X v ∈ Ge w (w v + 1)) (d : ℕ) (F : MvPolynomial σ K) (hF : F ∈ Ge w d) :
    φ F - F ∈ Ge w (d + 1) := by
  have key : ∀ m ∈ F.support, φ (monomial m (coeff m F)) - monomial m (coeff m F) ∈ Ge w (d + 1) := by
    intro m hm
    have hd : d ≤ Finsupp.weight w m := by
      by_contra h
      exact (mem_support_iff.mp hm) (mem_Ge.1 hF m (by omega))
    have e : monomial m (coeff m F) = coeff m F • monomial m (1 : K) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (Ge_mono (by omega) (monomial_step w φ hφ m))
  have h := Submodule.sum_mem _ key
  rwa [Finset.sum_sub_distrib, ← map_sum, ← F.as_sum] at h

/- English proof (translation)
Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]`. Introduce `ψ`. Set `p : Polynomial K` to `∑ j ∈ Finset.range N, Polynomial.C (ψ (Submodule.Quotient.mk (f j))) * Polynomial.X ^ j`. Establish `hp : p = 0`. Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Apply `Set.Infinite.mono _ ((Set.finite_singleton (0 : K)).infinite_compl)` to reduce the goal to its premises. Introduce `s hs`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs`. Establish `h1 : S.mkQ (∑ k ∈ Finset.range N, s ^ k • f k) = 0` using `(Submodule.Quotient.mk_eq_zero S).2 (h s hs)`. Establish `h2` using `congrArg ψ h1`.

Rewrite `h2` using `[map_sum, map_sum, map_zero]`. Simplify using `only [map_smul, Submodule.mkQ_apply, smul_eq_mul] at h2`. Use `show Polynomial.IsRoot p s`. Rewrite using `[Polynomial.IsRoot.def]`. Simplify using `only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`.

Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `h3` using `congrArg (fun q => Polynomial.coeff q k) hp`. Simplify using `only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_zero] at h3`.

Rewrite `h3` using `[Finset.sum_ite_eq]`. Simplify `h3` using `[Finset.mem_range.mpr hk]`.
-/
theorem coeffs_mem [Infinite K] {V : Type*} [AddCommGroup V] [Module K V] (S : Submodule K V) (N : ℕ) (f : ℕ → V)
    (h : ∀ s : K, s ≠ 0 → ∑ k ∈ Finset.range N, s ^ k • f k ∈ S) (k : ℕ) (hk : k < N) : f k ∈ S := by
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro ψ
  let p : Polynomial K := ∑ j ∈ Finset.range N, Polynomial.C (ψ (Submodule.Quotient.mk (f j))) * Polynomial.X ^ j
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ ((Set.finite_singleton (0 : K)).infinite_compl)
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hs
    have h1 : S.mkQ (∑ k ∈ Finset.range N, s ^ k • f k) = 0 := (Submodule.Quotient.mk_eq_zero S).2 (h s hs)
    have h2 := congrArg ψ h1
    rw [map_sum, map_sum, map_zero] at h2
    simp only [map_smul, Submodule.mkQ_apply, smul_eq_mul] at h2
    show Polynomial.IsRoot p s
    rw [Polynomial.IsRoot.def]
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
  have h3 := congrArg (fun q => Polynomial.coeff q k) hp
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one,
    mul_zero, Polynomial.coeff_zero] at h3
  rw [Finset.sum_ite_eq] at h3
  simpa [Finset.mem_range.mpr hk] using h3

def sc (w : σ → ℕ) (c : K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun v => C (c ^ w v) * X v

/- English proof (translation)
Rewrite using `[sc, aeval_monomial]`. Simplify using `only [mul_pow, Finsupp.prod_mul]`. Establish `h1 : (m.prod fun v k => (C (c ^ w v) : MvPolynomial σ K) ^ k) = C (c ^ Finsupp.weight w m)`. Simplify using `only [← C_pow, ← map_finsuppProd]`. Use `congr 1`.

Rewrite using `[Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, smul_eq_mul, mul_comm]`. Rewrite using `[monomial_eq, algebraMap_eq, C_mul, h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sc_monomial (w : σ → ℕ) (c : K) (m : σ →₀ ℕ) (a : K) :
    sc w c (monomial m a) = monomial m (c ^ Finsupp.weight w m * a) := by
  classical
  rw [sc, aeval_monomial]
  simp only [mul_pow, Finsupp.prod_mul]
  have h1 : (m.prod fun v k => (C (c ^ w v) : MvPolynomial σ K) ^ k) = C (c ^ Finsupp.weight w m) := by
    simp only [← C_pow, ← map_finsuppProd]
    congr 1
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [monomial_eq, algebraMap_eq, C_mul, h1]
  ring

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Simplify using `only [sc_monomial, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, mul_zero]`.
-/
theorem coeff_sc (w : σ → ℕ) (c : K) (F : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (sc w c F) = c ^ Finsupp.weight w m * coeff m F := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum]
  simp only [sc_monomial, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, mul_zero]

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_sc, coeff_sum]`. Simplify using `only [coeff_smul, coeff_weightedHomogeneousComponent, smul_eq_mul, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with h`.

Both sides reduce to the same expression. Distinguish the cases in `hm : m ∈ F.support`. Conclude with `absurd (Finset.mem_range.mpr (hN m hm)) h`. Rewrite using `[notMem_support_iff.mp hm, mul_zero]`.
-/
theorem sc_eq_sum (w : σ → ℕ) (c : K) (F : MvPolynomial σ K) (N : ℕ)
    (hN : ∀ m ∈ F.support, Finsupp.weight w m < N) :
    sc w c F = ∑ k ∈ Finset.range N, c ^ k • weightedHomogeneousComponent w k F := by
  classical
  ext m
  rw [coeff_sc, coeff_sum]
  simp only [coeff_smul, coeff_weightedHomogeneousComponent, smul_eq_mul, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_cases hm : m ∈ F.support
    · exact absurd (Finset.mem_range.mpr (hN m hm)) h
    · rw [notMem_support_iff.mp hm, mul_zero]

end PI.HwFix.UnitaryGroupMassFormula
