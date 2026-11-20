import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeXiMulDpowSuccStatement

open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatIdeal

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

/- English proof (translation)
Establish `h1 : Lat.η f ξ l M ∈ Lat.IB f ξ`. Unfold `Lat.η Lat.IB`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)`. Unfold `Lat.dpE`.

Rewrite using `[Algebra.smul_def, pow_succ]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h1)`.
-/
theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  have h1 : Lat.η f ξ l M ∈ Lat.IB f ξ := by
    unfold Lat.η Lat.IB
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  unfold Lat.dpE
  rw [Algebra.smul_def, pow_succ]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ h1)

/- English proof (translation)
Unfold `Lat.dpE`. Rewrite using `[pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]`.
-/
theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by
  unfold Lat.dpE
  rw [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/- English proof (translation)
Establish `h0 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial`. Establish `h1` using `Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)`. Rewrite `h1` using `[Nat.add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `hC : (((a + b).choose a : ℕ) : ℚ) ≠ 0`. Conclude with `(Nat.choose_pos (Nat.le_add_right a b)).ne'` after adjusting the coercions.

Establish `key : ((a.factorial : ℚ))⁻¹ * ((b.factorial : ℚ))⁻¹ = (((a + b).choose a : ℕ) : ℚ) * (((a + b).factorial : ℕ) : ℚ)⁻¹`. Rewrite using `[← h0, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]`. Establish `key' : algebraMap ℚ B ((a.factorial : ℚ))⁻¹ * algebraMap ℚ B ((b.factorial : ℚ))⁻¹ = (((a + b).choose a : ℕ) : B) * algebraMap ℚ B (((a + b).factorial : ℕ) : ℚ)⁻¹`. Rewrite using `[← map_mul, key, map_mul, map_natCast]`. Unfold `Lat.dpE`.

Rewrite using `[Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, pow_add]`. Take the linear combination `(Lat.η f ξ l M ^ a * Lat.η f ξ l M ^ b) * key'`.
-/
private theorem dpE_mul_dpE_eq_choose_mul (a b : ℕ) :
    Lat.dpE f ξ l M a * Lat.dpE f ξ l M b =
      (((a + b).choose a : ℕ) : B) * Lat.dpE f ξ l M (a + b) := by
  have h0 : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rwa [Nat.add_sub_cancel_left] at h1
  have hC : (((a + b).choose a : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right a b)).ne'
  have key : ((a.factorial : ℚ))⁻¹ * ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : ℚ) * (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← h0, Nat.cast_mul, Nat.cast_mul, mul_inv, mul_inv, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ hC, one_mul]
  have key' : algebraMap ℚ B ((a.factorial : ℚ))⁻¹ * algebraMap ℚ B ((b.factorial : ℚ))⁻¹ =
      (((a + b).choose a : ℕ) : B) * algebraMap ℚ B (((a + b).factorial : ℕ) : ℚ)⁻¹ := by
    rw [← map_mul, key, map_mul, map_natCast]
  unfold Lat.dpE
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, pow_add]
  linear_combination (Lat.η f ξ l M ^ a * Lat.η f ξ l M ^ b) * key'

/- English proof (translation)
Take `⟨w, a, rfl⟩` from `hy`. Take `⟨w', b, rfl⟩` from `hz`. Use `⟨w * w' * (((a + b).choose a : ℕ) : W), a + b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_natCast]`. Take the linear combination `(f w * f w') * dpE_mul_dpE_eq_choose_mul f ξ l M a b`.
-/
private theorem mul_mem_set_f_mul_dpE {y z : B}
    (hy : y ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  obtain ⟨w, a, rfl⟩ := hy
  obtain ⟨w', b, rfl⟩ := hz
  refine ⟨w * w' * (((a + b).choose a : ℕ) : W), a + b, ?_⟩
  rw [map_mul, map_mul, map_natCast]
  linear_combination (f w * f w') * dpE_mul_dpE_eq_choose_mul f ξ l M a b

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy'`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz' => exact AddSubgroup.subset_closure (mul_mem_set_f_mul_dpE f ξ l M hy' hz')`. Consider the case `zero => rw [mul_zero]`.

Conclude with `zero_mem _`. Consider the case `add z1 z2 _ _ h1 h2 => rw [mul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg z _ h => rw [mul_neg]`. Conclude with `neg_mem h`.

Consider the case `zero => rw [zero_mul]`. Conclude with `zero_mem _`. Consider the case `add y1 y2 _ _ h1 h2 => rw [add_mul]`. Conclude with `add_mem h1 h2`. Consider the case `neg y _ h => rw [neg_mul]`.

Conclude with `neg_mem h`.
-/
private theorem mul_mem_closure_f_mul_dpE {y z : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k})
    (hz : z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    y * z ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    induction hz using AddSubgroup.closure_induction with
    | mem z hz' => exact AddSubgroup.subset_closure (mul_mem_set_f_mul_dpE f ξ l M hy' hz')
    | zero => rw [mul_zero]; exact zero_mem _
    | add z1 z2 _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
    | neg z _ h => rw [mul_neg]; exact neg_mem h
  | zero => rw [zero_mul]; exact zero_mem _
  | add y1 y2 _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | neg y _ h => rw [neg_mul]; exact neg_mem h

/- English proof (translation)
Unfold `Lat.sub at hy`. Proceed by induction on `hy using Subring.closure_induction with`. Consider the case `mem y hy'`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Break down `hy' with ⟨w, rfl⟩ | ⟨k, rfl⟩` into its components or cases.

Conclude with `⟨w, 0, by rw [dpE_zero, mul_one]⟩`. Conclude with `⟨1, k, by rw [map_one, one_mul]⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `one => exact AddSubgroup.subset_closure ⟨1, 0, by rw [dpE_zero, map_one, mul_one]⟩`. Consider the case `add y z _ _ h1 h2 => exact add_mem h1 h2`.

Consider the case `neg y _ h => exact neg_mem h`. Consider the case `mul y z _ _ h1 h2 => exact mul_mem_closure_f_mul_dpE f ξ l M h1 h2`.
-/
private theorem mem_closure_f_mul_dpE_of_mem_sub {y : B} (hy : y ∈ Lat.sub f ξ l M) :
    y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k} := by
  unfold Lat.sub at hy
  induction hy using Subring.closure_induction with
  | mem y hy' =>
    apply AddSubgroup.subset_closure
    rcases hy' with ⟨w, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨w, 0, by rw [dpE_zero, mul_one]⟩
    · exact ⟨1, k, by rw [map_one, one_mul]⟩
  | zero => exact zero_mem _
  | one => exact AddSubgroup.subset_closure ⟨1, 0, by rw [dpE_zero, map_one, mul_one]⟩
  | add y z _ _ h1 h2 => exact add_mem h1 h2
  | neg y _ h => exact neg_mem h
  | mul y z _ _ h1 h2 => exact mul_mem_closure_f_mul_dpE f ξ l M h1 h2

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy'`. Take `⟨w, k, rfl⟩` from `hy'`. Consider the cases of `k with`. Consider the case `zero => exact ⟨w, 0, by rw [dpE_zero, mul_one, Finsupp.sum_zero_index, add_zero]⟩`.

Consider the case `succ j`. Use `⟨0, Finsupp.single j w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zero, zero_add, Finsupp.sum_single_index]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, 0, by rw [map_zero, Finsupp.sum_zero_index, add_zero]⟩`.

Consider the case `add y z _ _ h1 h2`. Take `⟨a, c, rfl⟩` from `h1`. Take `⟨b, d, rfl⟩` from `h2`. Use `⟨a + b, c + d, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum_add_index', map_add]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i`. Simplify using the standard rewrite rules. Introduce `i b1 b2`. Simplify using `[add_mul]`.

Consider the case `neg y _ h`. Take `⟨a, c, rfl⟩` from `h`. Use `⟨-a, -c, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum_neg_index, map_neg, neg_add]`. Simplify using `only [map_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]`.

Introduce `i`. Simplify using the standard rewrite rules.
-/
private theorem exists_repr_of_mem_closure_f_mul_dpE {y : B}
    (hy : y ∈ AddSubgroup.closure {y : B | ∃ (w : W) (k : ℕ), y = f w * Lat.dpE f ξ l M k}) :
    ∃ (w₀ : W) (c : ℕ →₀ W), y = f w₀ + c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨w, k, rfl⟩ := hy'
    cases k with
    | zero => exact ⟨w, 0, by rw [dpE_zero, mul_one, Finsupp.sum_zero_index, add_zero]⟩
    | succ j =>
      refine ⟨0, Finsupp.single j w, ?_⟩
      rw [map_zero, zero_add, Finsupp.sum_single_index]
      simp
  | zero => exact ⟨0, 0, by rw [map_zero, Finsupp.sum_zero_index, add_zero]⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, c, rfl⟩ := h1
    obtain ⟨b, d, rfl⟩ := h2
    refine ⟨a + b, c + d, ?_⟩
    rw [Finsupp.sum_add_index', map_add]
    · ring
    · intro i
      simp
    · intro i b1 b2
      simp [add_mul]
  | neg y _ h =>
    obtain ⟨a, c, rfl⟩ := h
    refine ⟨-a, -c, ?_⟩
    rw [Finsupp.sum_neg_index, map_neg, neg_add]
    · simp only [map_neg, neg_mul, Finsupp.sum, Finset.sum_neg_distrib]
    · intro i
      simp

/- English proof (translation)
Establish `hs : c.support ⊆ Finset.range (c.support.sup id + 1)`. Introduce `i hi`. Rewrite using `[Finset.mem_range, Nat.lt_succ_iff]`. Conclude with `Finset.le_sup (f := id) hi`. Use `⟨c.support.sup id + 1, fun i => c i, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finsupp.sum_of_support_subset c hs (fun i w => f w * Lat.dpE f ξ l M (i + 1)) (fun _ _ => by simp)]`. Conclude with `(Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M (i + 1)) _).symm`.
-/
private theorem exists_fin_sum_eq_finsupp_sum_f_mul_dpE (c : ℕ →₀ W) :
    ∃ (n : ℕ) (c' : Fin n → W), c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) =
      ∑ i : Fin n, f (c' i) * Lat.dpE f ξ l M (i + 1) := by
  have hs : c.support ⊆ Finset.range (c.support.sup id + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := id) hi
  refine ⟨c.support.sup id + 1, fun i => c i, ?_⟩
  rw [Finsupp.sum_of_support_subset c hs (fun i w => f w * Lat.dpE f ξ l M (i + 1))
    (fun _ _ => by simp)]
  exact (Fin.sum_univ_eq_sum_range (fun i => f (c i) * Lat.dpE f ξ l M (i + 1)) _).symm

/- English proof (translation)
Establish `h1 : Lat.dpE f ξ l M 1 = ((l : ℚ) ^ M)⁻¹ • f ξ`. Unfold `Lat.dpE Lat.η`. Rewrite using `[pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]`. Rewrite using `[h1, Algebra.smul_def, ← mul_assoc, map_pow, map_natCast, ← map_natCast (algebraMap ℚ B) l, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl), map_one, one_mul]`.
-/
private theorem f_xi_eq_f_pow_mul_dpE_one (hl : (l : ℚ) ≠ 0) :
    f ξ = f ((l : W) ^ M) * Lat.dpE f ξ l M 1 := by
  have h1 : Lat.dpE f ξ l M 1 = ((l : ℚ) ^ M)⁻¹ • f ξ := by
    unfold Lat.dpE Lat.η
    rw [pow_one, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  rw [h1, Algebra.smul_def, ← mul_assoc, map_pow, map_natCast,
    ← map_natCast (algebraMap ℚ B) l, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hl),
    map_one, one_mul]

/- English proof (translation)
Rewrite using `[Finsupp.sum_add_index', Finsupp.sum_single_index]`. Apply the tactic sequence `all_goals simp [add_mul]`.
-/
private theorem finsupp_sum_add_single_zero_f_mul_dpE (c : ℕ →₀ W) (v : W) :
    (c + Finsupp.single 0 v).sum (fun i w => f w * Lat.dpE f ξ l M (i + 1))
      = c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) + f v * Lat.dpE f ξ l M 1 := by
  rw [Finsupp.sum_add_index', Finsupp.sum_single_index]
  all_goals simp [add_mul]

/- English proof (translation)
Establish `hI : x ∈ Lat.I f ξ l M ↔ Lat.ι f ξ l M x ∈ Lat.IB f ξ` using `Iff.rfl`. Rewrite using `[hI]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hsub : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M` using `(x : ↥(Lat.sub f ξ l M)).2`.

Take `⟨w₀, c, hc⟩` from `exists_repr_of_mem_closure_f_mul_dpE f ξ l M (mem_closure_f_mul_dpE_of_mem_sub f ξ l M hsub)`. Establish `hS : c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) ∈ Lat.IB f ξ`. Unfold `Finsupp.sum`. Conclude with `Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M i))`. Establish `hw : f w₀ ∈ Lat.IB f ξ`.

Establish `h2` using `sub_mem hx hS`. Rewrite `h2` using `[hc, add_sub_cancel_right]`. Then use the resulting hypothesis. Unfold `Lat.IB at hw`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hw`. Take `⟨w', rfl⟩` from `H.gr 0 H.one_le w₀ b (by rw [pow_zero, mul_one, zero_add, pow_one, ← hb, mul_comm])`.

Establish `hl : (l : ℚ) ≠ 0`. Introduce `h`. Apply `H.l0` to reduce the goal to its premises. Establish `h3 : l = 0` using `by exact_mod_cast h`. Rewrite using `[h3, Nat.cast_zero]`.

Take `⟨n, c', hc'⟩` from `exists_fin_sum_eq_finsupp_sum_f_mul_dpE f ξ l M (c + Finsupp.single 0 ((l : W) ^ M * w'))`. Use `⟨n, c', ?_⟩` and prove the remaining obligations. Rewrite using `[← hc', finsupp_sum_add_single_zero_f_mul_dpE f ξ l M, hc]`. Simplify using `only [map_mul]`. Rewrite using `[f_xi_eq_f_pow_mul_dpE_one f ξ l M hl]`.

Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨n, c, hc⟩`. Rewrite using `[hc]`. Conclude with `Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M _))`.
-/
theorem mem_I_iff (m : ℕ) (H : Lat.Hyp f ξ l m) (x : Lat.A f ξ l M) :
    x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  have hI : x ∈ Lat.I f ξ l M ↔ Lat.ι f ξ l M x ∈ Lat.IB f ξ := Iff.rfl
  rw [hI]
  constructor
  · intro hx
    have hsub : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := (x : ↥(Lat.sub f ξ l M)).2
    obtain ⟨w₀, c, hc⟩ := exists_repr_of_mem_closure_f_mul_dpE f ξ l M (mem_closure_f_mul_dpE_of_mem_sub f ξ l M hsub)
    have hS : c.sum (fun i w => f w * Lat.dpE f ξ l M (i + 1)) ∈ Lat.IB f ξ :=
      by
        unfold Finsupp.sum
        exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M i))
    have hw : f w₀ ∈ Lat.IB f ξ := by
      have h2 := sub_mem hx hS
      rwa [hc, add_sub_cancel_right] at h2
    unfold Lat.IB at hw
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hw
    obtain ⟨w', rfl⟩ := H.gr 0 H.one_le w₀ b
      (by rw [pow_zero, mul_one, zero_add, pow_one, ← hb, mul_comm])
    have hl : (l : ℚ) ≠ 0 := by
      intro h
      apply H.l0
      have h3 : l = 0 := by exact_mod_cast h
      rw [h3, Nat.cast_zero]
    obtain ⟨n, c', hc'⟩ := exists_fin_sum_eq_finsupp_sum_f_mul_dpE f ξ l M (c + Finsupp.single 0 ((l : W) ^ M * w'))
    refine ⟨n, c', ?_⟩
    rw [← hc', finsupp_sum_add_single_zero_f_mul_dpE f ξ l M, hc]
    simp only [map_mul]
    rw [f_xi_eq_f_pow_mul_dpE_one f ξ l M hl]
    ring
  · rintro ⟨n, c, hc⟩
    rw [hc]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (dpE_succ_mem_IB f ξ l M _))

end

/- English proof (translation)
Introduce `W B _ _ _ f ξ l M m H x`. Conclude with `mem_I_iff f ξ l M m H x`.
-/
theorem mem_I : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x : Lat.A f ξ l M, x ∈ Lat.I f ξ l M ↔
      ∃ (n : ℕ) (c : Fin n → W), Lat.ι f ξ l M x = ∑ i, f (c i) * Lat.dpE f ξ l M (i + 1) := by
  intro W B _ _ _ f ξ l M m H x
  exact mem_I_iff f ξ l M m H x

end GlobalTheory.CompanionTheory.LatIdeal
