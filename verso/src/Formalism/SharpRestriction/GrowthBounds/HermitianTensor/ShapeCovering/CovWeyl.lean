import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ShapeCovering.StatementY
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering

open MvPolynomial Formalism.GradedWeylDivisibility

section general

variable {K : Type} [Field K] {r n : ℕ}

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using (dualWeylMul K r n 0 0 0 0).2`. Consider the case `succ k ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `(dualWeylMul K r n _ _ _ _).1 ih hy`.
-/
private lemma cw_pow_mem {ν : Fin n → ℕ} {y : MvPolynomial (Fin r × Fin n) K}
    (hy : y ∈ dualWeyl K r n ν) (k : ℕ) : y ^ k ∈ dualWeyl K r n (k • ν) := by
  induction k with
  | zero => simpa using (dualWeylMul K r n 0 0 0 0).2
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact (dualWeylMul K r n _ _ _ _).1 ih hy

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (dualWeylMul K r n 0 0 0 0).2`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `(dualWeylMul K r n _ _ _ _).1 (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
private lemma cw_prod_mem {ι : Type} (s : Finset ι) (μ : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (h : ∀ i ∈ s, g i ∈ dualWeyl K r n (μ i)) :
    ∏ i ∈ s, g i ∈ dualWeyl K r n (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite using `[aeval_def, eval₂_eq]`. Use `Submodule.sum_mem _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[← Algebra.smul_def]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hdeg : ∑ i ∈ d.support, d i = Q`.

Use `hf (mem_support_iff.mp hd)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`. Use `cw_prod_mem d.support (fun i => d i • ν) (fun i => y i ^ d i) (fun i _ => cw_pow_mem (hy i) _)` as an intermediate fact. Rewrite `this` using `[← Finset.sum_smul, hdeg]`. Then use the resulting hypothesis.
-/
private lemma cw_aeval_mem {σ : Type} {ν : Fin n → ℕ} (y : σ → MvPolynomial (Fin r × Fin n) K)
    (hy : ∀ i, y i ∈ dualWeyl K r n ν) (Q : ℕ) (f : MvPolynomial σ K) (hf : f.IsHomogeneous Q) :
    aeval y f ∈ dualWeyl K r n (Q • ν) := by
  rw [aeval_def, eval₂_eq]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = Q := by
    have := hf (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have := cw_prod_mem d.support (fun i => d i • ν) (fun i => y i ^ d i)
    (fun i _ => cw_pow_mem (hy i) _)
  rwa [← Finset.sum_smul, hdeg] at this

/- English proof (translation)
Use `choose f hf1 hf2 using h`. Conclude with `⟨∏ k ∈ s, f k, IsHomogeneous.prod _ _ _ (fun k _ => hf1 k), by`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => hf2 k⟩`.
-/
private lemma cw_prod_aeval {σ ι : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (s : Finset ι)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (e : ι → ℕ)
    (h : ∀ k, ∃ f : MvPolynomial σ K, f.IsHomogeneous (e k) ∧ aeval y f = g k) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous (∑ k ∈ s, e k) ∧ aeval y f = ∏ k ∈ s, g k := by
  choose f hf1 hf2 using h
  exact ⟨∏ k ∈ s, f k, IsHomogeneous.prod _ _ _ (fun k _ => hf1 k), by
    rw [map_prod]; exact Finset.prod_congr rfl fun k _ => hf2 k⟩

/- English proof (translation)
Rewrite `hF` using `[standardMonomialSpanDomain K r n ν]`. Establish `key` using `(Submodule.span_le (p := Submodule.map (aeval y).toLinearMap (homogeneousSubmodule σ K Q))).mpr (by`. Introduce and unpack `_ ⟨k, sz, hsz, I, hs, rfl⟩`. Take `⟨f, hf, hfe⟩` from `h k sz hsz I hs`. Conclude with `⟨f, hf, hfe⟩) hF`.

Take `⟨f, hf, hfe⟩` from `key`. Conclude with `⟨f, hf, hfe⟩`.
-/
private lemma cw_span_le {σ : Type} (y : σ → MvPolynomial (Fin r × Fin n) K) (Q : ℕ) (ν : Fin n → ℕ)
    (h : ∀ (k : ℕ) (sz : Fin k → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
      shapeDeg sz = ν → ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = bideterminant K sz hsz I)
    (F : MvPolynomial (Fin r × Fin n) K) (hF : F ∈ dualWeyl K r n ν) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous Q ∧ aeval y f = F := by
  rw [standardMonomialSpanDomain K r n ν] at hF
  have key := (Submodule.span_le
    (p := Submodule.map (aeval y).toLinearMap (homogeneousSubmodule σ K Q))).mpr (by
      rintro _ ⟨k, sz, hsz, I, hs, rfl⟩
      obtain ⟨f, hf, hfe⟩ := h k sz hsz I hs
      exact ⟨f, hf, hfe⟩) hF
  obtain ⟨f, hf, hfe⟩ := key
  exact ⟨f, hf, hfe⟩

/- English proof (translation)
Use `bidetMem K r n 1 (fun _ => s) (fun _ => hs) (fun _ => J)` as an intermediate fact. Establish `h1 : bideterminant K (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => J) = initMinor K J hs`. Simplify using `[bideterminant]`. Establish `h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0`. Use function extensionality and compare the values at `t`.

Apply the tactic sequence `by_cases ht : t.val < s <;> simp [shapeDeg, ht]`. Rewrite `this` using `[h1, h2]`. Then use the resulting hypothesis.
-/
private lemma cw_single_mem (s : ℕ) (hs : s ≤ n) (J : Fin s → Fin r) :
    initMinor K J hs ∈ dualWeyl K r n (fun t => if t.val < s then 1 else 0) := by
  have := bidetMem K r n 1 (fun _ => s) (fun _ => hs) (fun _ => J)
  have h1 : bideterminant K (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => J) = initMinor K J hs := by
    simp [bideterminant]
  have h2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [h1, h2] at this

/- English proof (translation)
Substitute `h` using the available equality. Simplify using `[initMinor]`.
-/
private lemma cw_minor0 (s : ℕ) (hs : s ≤ n) (h : s = 0) (J : Fin s → Fin r) :
    initMinor K J hs = 1 := by
  subst h
  simp [initMinor]

/- English proof (translation)
Assume the negation of the conclusion as `hk`. Establish `hm : j ∈ Finset.univ.filter (fun k => t.val < sz k)`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [shapeDeg, Finset.card_eq_zero] at h`.

Rewrite `hm` using `[h]`. Simplify using `at hm`.
-/
private lemma cw_le_of_shape {k : ℕ} (sz : Fin k → ℕ) (t : Fin n) (h : shapeDeg sz t = 0) (j : Fin k) :
    sz j ≤ t.val := by
  by_contra hk
  have hm : j ∈ Finset.univ.filter (fun k => t.val < sz k) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
  simp only [shapeDeg, Finset.card_eq_zero] at h
  rw [h] at hm
  simp at hm

end general

/- English proof (translation)
Simplify using `only [shapeDeg, Fin.val_zero, Finset.sum_boole, Nat.cast_id]`. Reduce the equality to equality of the corresponding arguments.
-/
private lemma cw_card {n k : ℕ} (sz : Fin k → ℕ) :
    ∑ j, (if 0 < sz j then 1 else 0) = shapeDeg sz (0 : Fin (n + 1)) := by
  simp only [shapeDeg, Fin.val_zero, Finset.sum_boole, Nat.cast_id]
  congr

/- English proof (translation)
Take `rfl : s = 1` from `by omega`. Simplify using `[initMinor]`.
-/
private lemma cw_minor1 {K : Type} [Field K] {r n : ℕ} (s : ℕ) (hs : s ≤ n + 1) (h : 0 < s) (h1 : s ≤ 1)
    (J : Fin s → Fin r) : initMinor K J hs = X (J ⟨0, h⟩, 0) := by
  obtain rfl : s = 1 := by omega
  simp [initMinor]

/- English proof (translation)
Introduce `K _ m P F hm`. Establish `hren : ∀ f : MvPolynomial (Fin (m + 1)) K, rename (fun i => (i, (0 : Fin (m + 1)))) f = aeval (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) f` using `fun f => DFunLike.congr_fun (algHom_ext fun i => by simp) f`. Simplify using `only [hren]`. Prove the components needed by the constructor for the conclusion. Use `cw_span_le _ P _ ?_ F` and prove the remaining obligations.

Introduce `k sz hsz I hs`. Establish `h0 : shapeDeg sz (0 : Fin (m + 1)) = P` using `by rw [hs]; simp`. Establish `h1 : shapeDeg sz (⟨1, by omega⟩ : Fin (m + 1)) = 0` using `by rw [hs]; simp [Fin.ext_iff]`. Establish `hle : ∀ j, sz j ≤ 1` using `cw_le_of_shape sz _ h1`. Use `cw_prod_aeval (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) Finset.univ (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_` as an intermediate fact.

Rewrite `this` using `[cw_card, h0]`. Conclude with `this`. Introduce `j`. Distinguish the cases in `hj : 0 < sz j`. Use `⟨X (I j ⟨0, hj⟩), by simpa [hj] using isHomogeneous_X K (I j ⟨0, hj⟩), ?_⟩` and prove the remaining obligations.

Rewrite using `[aeval_X, cw_minor1 _ _ hj (hle j)]`. Conclude with `⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K, by rw [map_one, cw_minor0 _ _ (by omega)]⟩`. Introduce and unpack `⟨f, hf, rfl⟩`. Use `cw_aeval_mem (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) (ν := fun t => if t.val < 1 then 1 else 0) ?_ P f hf` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t = 0`. Simplify using `[ht]`. Simplify using `[ht]`. Introduce `i`.

Use `cw_single_mem (K := K) (r := m + 1) (n := m + 1) 1 (by omega) (fun _ => i)` as an intermediate fact. Rewrite `this` using `[cw_minor1 _ _ (by omega) le_rfl]`. Then use the resulting hypothesis.
-/
theorem first_column_polynomials_characterize : FirstColumnPolynomialsSpan := by
  intro K _ m P F hm
  have hren : ∀ f : MvPolynomial (Fin (m + 1)) K, rename (fun i => (i, (0 : Fin (m + 1)))) f =
      aeval (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) f :=
    fun f => DFunLike.congr_fun (algHom_ext fun i => by simp) f
  simp only [hren]
  constructor
  · refine cw_span_le _ P _ ?_ F
    intro k sz hsz I hs
    have h0 : shapeDeg sz (0 : Fin (m + 1)) = P := by rw [hs]; simp
    have h1 : shapeDeg sz (⟨1, by omega⟩ : Fin (m + 1)) = 0 := by rw [hs]; simp [Fin.ext_iff]
    have hle : ∀ j, sz j ≤ 1 := cw_le_of_shape sz _ h1
    have := cw_prod_aeval
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) Finset.univ
      (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_
    · rw [cw_card, h0] at this
      exact this
    · intro j
      by_cases hj : 0 < sz j
      · refine ⟨X (I j ⟨0, hj⟩), by simpa [hj] using isHomogeneous_X K (I j ⟨0, hj⟩), ?_⟩
        rw [aeval_X, cw_minor1 _ _ hj (hle j)]
      · exact ⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K,
          by rw [map_one, cw_minor0 _ _ (by omega)]⟩
  · rintro ⟨f, hf, rfl⟩
    have := cw_aeval_mem
      (fun i => (X (i, (0 : Fin (m + 1))) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (ν := fun t => if t.val < 1 then 1 else 0) ?_ P f hf
    · convert this using 2
      funext t
      by_cases ht : t = 0
      · simp [ht]
      · simp [ht]
    · intro i
      have := cw_single_mem (K := K) (r := m + 1) (n := m + 1) 1 (by omega) (fun _ => i)
      rwa [cw_minor1 _ _ (by omega) le_rfl] at this

/- English proof (translation)
Distinguish the cases in `hJ : Function.Injective J`. Establish `hns : ¬ Function.Surjective J`. Introduce `hsur`. Use `Fintype.card_le_of_surjective J hsur` as an intermediate fact. Simplify using `at this`.

Simplify using `only [Function.Surjective, not_forall, not_exists] at hns`. Take `⟨i, hi⟩` from `hns`. Establish `hex : ∀ a, ∃ z, i.succAbove z = J a` using `fun a => Fin.exists_succAbove_eq (hi a)`. Use `choose σ hσ using hex`. Establish `hinj : Function.Injective σ`.

Introduce `a b hab`. Apply `hJ` to reduce the goal to its premises. Rewrite using `[← hσ a, ← hσ b, hab]`. Set `e : Equiv.Perm (Fin m)` to `Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)`. Use `set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) := fun a b => X (i.succAbove a, b.castSucc) with hN`.

Establish `hM : initMinor K J (Nat.le_succ m) = (N.submatrix e id).det`. Unfold `initMinor`. Use `congrArg Matrix.det (Matrix.ext fun a b => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X (J a, Fin.castLE _ b) = X (i.succAbove (σ a), b.castSucc)`. Rewrite using `[hσ a]`.

Both sides reduce to the same expression. Use `⟨i, ((Equiv.Perm.sign e : ℤ) : K) * (-1) ^ (i : ℕ), ?_⟩` and prove the remaining obligations. Rewrite using `[hM, Matrix.det_permute]`. Establish `h1 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Establish `h2 : covY K m i = (-1) ^ (i : ℕ) * N.det` using `rfl`. Rewrite using `[h2]`. Simplify using `only [map_mul, map_pow, map_neg, map_one, map_intCast]`. Take the linear combination `(-(((Equiv.Perm.sign e : ℤ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) * N.det) * h1`.

Simplify using `only [Function.Injective, not_forall] at hJ`. Take `⟨a, b, hab, hne⟩` from `hJ`. Use `⟨0, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_mul]`. Unfold `initMinor`.

Use `Matrix.det_zero_of_row_eq hne ?_` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `[hab]`.
-/
private lemma cw_key {K : Type} [Field K] (m : ℕ) (J : Fin m → Fin (m + 1)) :
    ∃ (i : Fin (m + 1)) (ε : K), initMinor K J (Nat.le_succ m) = C ε * covY K m i := by
  by_cases hJ : Function.Injective J
  · have hns : ¬ Function.Surjective J := by
      intro hsur
      have := Fintype.card_le_of_surjective J hsur
      simp at this
    simp only [Function.Surjective, not_forall, not_exists] at hns
    obtain ⟨i, hi⟩ := hns
    have hex : ∀ a, ∃ z, i.succAbove z = J a := fun a => Fin.exists_succAbove_eq (hi a)
    choose σ hσ using hex
    have hinj : Function.Injective σ := by
      intro a b hab
      apply hJ
      rw [← hσ a, ← hσ b, hab]
    let e : Equiv.Perm (Fin m) := Equiv.ofBijective σ (Finite.injective_iff_bijective.mp hinj)
    set N : Matrix (Fin m) (Fin m) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
      fun a b => X (i.succAbove a, b.castSucc) with hN
    have hM : initMinor K J (Nat.le_succ m) = (N.submatrix e id).det := by
      unfold initMinor
      refine congrArg Matrix.det (Matrix.ext fun a b => ?_)
      change X (J a, Fin.castLE _ b) = X (i.succAbove (σ a), b.castSucc)
      rw [hσ a]
      rfl
    refine ⟨i, ((Equiv.Perm.sign e : ℤ) : K) * (-1) ^ (i : ℕ), ?_⟩
    rw [hM, Matrix.det_permute]
    have h1 : ((-1 : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; simp
    have h2 : covY K m i = (-1) ^ (i : ℕ) * N.det := rfl
    rw [h2]
    simp only [map_mul, map_pow, map_neg, map_one, map_intCast]
    linear_combination (-(((Equiv.Perm.sign e : ℤ) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)) * N.det) * h1
  · simp only [Function.Injective, not_forall] at hJ
    obtain ⟨a, b, hab, hne⟩ := hJ
    refine ⟨0, 0, ?_⟩
    rw [map_zero, zero_mul]
    unfold initMinor
    refine Matrix.det_zero_of_row_eq hne ?_
    funext q
    simp [hab]

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `cw_key s J`.
-/
private lemma cw_key' {K : Type} [Field K] (m s : ℕ) (hs : s ≤ m + 1) (h : s = m) (J : Fin s → Fin (m + 1)) :
    ∃ (i : Fin (m + 1)) (ε : K), initMinor K J hs = C ε * covY K m i := by
  subst h
  exact cw_key s J

/- English proof (translation)
Use `cw_single_mem (K := K) (r := m + 1) (n := m + 1) m (Nat.le_succ m) i.succAbove` as an intermediate fact. Establish `h2 : covY K m i = ((-1 : K) ^ (i : ℕ)) • initMinor K i.succAbove (Nat.le_succ m)`. Rewrite using `[smul_eq_C_mul]`. Simplify using `only [map_pow, map_neg, map_one]`. Both sides reduce to the same expression.

Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ this`.
-/
private lemma cw_covY_mem {K : Type} [Field K] (m : ℕ) (i : Fin (m + 1)) :
    covY K m i ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t.val < m then 1 else 0) := by
  have := cw_single_mem (K := K) (r := m + 1) (n := m + 1) m (Nat.le_succ m) i.succAbove
  have h2 : covY K m i = ((-1 : K) ^ (i : ℕ)) • initMinor K i.succAbove (Nat.le_succ m) := by
    rw [smul_eq_C_mul]
    simp only [map_pow, map_neg, map_one]
    rfl
  rw [h2]
  exact Submodule.smul_mem _ _ this

/- English proof (translation)
Introduce `K _ m Q F hm`. Prove the components needed by the constructor for the conclusion. Use `cw_span_le _ Q _ ?_ F` and prove the remaining obligations. Introduce `k sz hsz I hs`. Establish `h0 : shapeDeg sz (0 : Fin (m + 1)) = Q`.

Rewrite using `[hs]`. Establish `: (0 : Fin (m + 1)) ≠ Fin.last m`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `[this]`. Establish `h1 : shapeDeg sz (⟨m - 1, by omega⟩ : Fin (m + 1)) = Q`. Rewrite using `[hs]`. Establish `: (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m`.

Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.

Establish `h2 : shapeDeg sz (Fin.last m) = 0` using `by rw [hs]; simp`. Establish `hle : ∀ j, sz j ≤ m` using `cw_le_of_shape sz _ h2`. Establish `hsub : Finset.univ.filter (fun j => m - 1 < sz j) ⊆ Finset.univ.filter (fun j => 0 < sz j)`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢`.

Use linear arithmetic over natural numbers and integers. Establish `heq` using `Finset.eq_of_subset_of_card_le hsub (by`. Establish `a0 : (Finset.univ.filter (fun j => 0 < sz j)).card = Q` using `h0`. Establish `a1 : (Finset.univ.filter (fun j => m - 1 < sz j)).card = Q` using `h1`. Rewrite using `[a0, a1])`.

Establish `hm' : ∀ j, 0 < sz j → sz j = m`. Introduce `j hj`. Establish `: j ∈ Finset.univ.filter (fun j => m - 1 < sz j)`. Rewrite using `[heq]`. Simplify using `using hj`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at this`. Use `hle j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `cw_prod_aeval (covY K m) Finset.univ (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_` as an intermediate fact. Rewrite `this` using `[cw_card, h0]`.

Conclude with `this`. Introduce `j`. Distinguish the cases in `hj : 0 < sz j`. Take `⟨i, ε, hi⟩` from `cw_key' (K := K) m (sz j) (hsz j) (hm' j hj) (I j)`. Use `⟨C ε * X i, by simpa [hj] using (isHomogeneous_X K i).C_mul ε, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, aeval_X, aeval_C, hi]`. Both sides reduce to the same expression. Conclude with `⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K, by rw [map_one, cw_minor0 _ _ (by omega)]⟩`. Introduce and unpack `⟨f, hf, rfl⟩`. Use `cw_aeval_mem (covY K m) (cw_covY_mem m) Q f hf` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Distinguish the cases in `ht : t = Fin.last m`. Simplify using `[ht]`. Establish `: t.val < m`.

Establish `h1` using `t.isLt`. Establish `h2 : t.val ≠ m` using `fun h => ht (Fin.ext (by simpa using h))`. Use linear arithmetic over natural numbers and integers. Simplify using `[ht, this]`.
-/
theorem signed_minor_polynomials_characterize : SignedMinorPolynomialsSpan := by
  intro K _ m Q F hm
  constructor
  · refine cw_span_le _ Q _ ?_ F
    intro k sz hsz I hs
    have h0 : shapeDeg sz (0 : Fin (m + 1)) = Q := by
      rw [hs]
      have : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    have h1 : shapeDeg sz (⟨m - 1, by omega⟩ : Fin (m + 1)) = Q := by
      rw [hs]
      have : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp [this]
    have h2 : shapeDeg sz (Fin.last m) = 0 := by rw [hs]; simp
    have hle : ∀ j, sz j ≤ m := cw_le_of_shape sz _ h2
    have hsub : Finset.univ.filter (fun j => m - 1 < sz j) ⊆ Finset.univ.filter (fun j => 0 < sz j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have a0 : (Finset.univ.filter (fun j => 0 < sz j)).card = Q := h0
      have a1 : (Finset.univ.filter (fun j => m - 1 < sz j)).card = Q := h1
      rw [a0, a1])
    have hm' : ∀ j, 0 < sz j → sz j = m := by
      intro j hj
      have : j ∈ Finset.univ.filter (fun j => m - 1 < sz j) := by
        rw [heq]; simpa using hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      have := hle j
      omega
    have := cw_prod_aeval (covY K m) Finset.univ
      (fun j => initMinor K (I j) (hsz j)) (fun j => if 0 < sz j then 1 else 0) ?_
    · rw [cw_card, h0] at this
      exact this
    · intro j
      by_cases hj : 0 < sz j
      · obtain ⟨i, ε, hi⟩ := cw_key' (K := K) m (sz j) (hsz j) (hm' j hj) (I j)
        refine ⟨C ε * X i, by simpa [hj] using (isHomogeneous_X K i).C_mul ε, ?_⟩
        rw [map_mul, aeval_X, aeval_C, hi]
        rfl
      · exact ⟨1, by simpa [hj] using isHomogeneous_one (Fin (m + 1)) K,
          by rw [map_one, cw_minor0 _ _ (by omega)]⟩
  · rintro ⟨f, hf, rfl⟩
    have := cw_aeval_mem (covY K m) (cw_covY_mem m) Q f hf
    convert this using 2
    funext t
    by_cases ht : t = Fin.last m
    · simp [ht]
    · have : t.val < m := by
        have h1 := t.isLt
        have h2 : t.val ≠ m := fun h => ht (Fin.ext (by simpa using h))
        omega
      simp [ht, this]

end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
