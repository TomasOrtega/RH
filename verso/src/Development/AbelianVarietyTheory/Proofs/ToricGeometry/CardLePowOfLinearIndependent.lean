import Mathlib

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ClassicalTheta

/- English proof (translation)
Establish `h1 : ∀ (j : Fin g) (k : ℤ) (m : Fin g → ℤ), P (m + Pi.single j (k * n)) ↔ P m`. Introduce `j k`. Proceed by induction on `k using Int.induction_on with`. Consider the case `zero => intro m`. Simplify using the standard rewrite rules.

Consider the case `succ k ih`. Introduce `m`. Establish `: m + Pi.single j (((k : ℤ) + 1) * n) = (m + Pi.single j ((k : ℤ) * n)) + Pi.single j (n : ℤ)`. Rewrite using `[add_assoc, ← Pi.single_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, hP, ih]`. Consider the case `pred k ih`. Introduce `m`. Establish `: m + Pi.single j ((-(k : ℤ)) * n) = (m + Pi.single j ((-(k : ℤ) - 1) * n)) + Pi.single j (n : ℤ)`.

Rewrite using `[add_assoc, ← Pi.single_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← ih m, this, hP]`. Establish `h2 : ∀ (k : Fin g → ℤ) (s : Finset (Fin g)) (m : Fin g → ℤ), P (m + ∑ j ∈ s, Pi.single j (k j * n)) ↔ P m`.

Introduce `k s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro m`. Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`.

Introduce `m`. Rewrite using `[Finset.sum_insert ha, add_comm (Pi.single a _), ← add_assoc, h1, ih]`. Establish `hn' : (0 : ℤ) < n` using `by exact_mod_cast hn`. Set `r : Fin g → Fin n` to `fun i => ⟨(m i % n).toNat, by`. Establish `h0` using `Int.emod_nonneg (m i) hn'.ne'`.

Establish `h1` using `Int.emod_lt_of_pos (m i) hn'`. Use the proof step `omega⟩`. Establish `hm : m = (fun i => ((r i : ℕ) : ℤ)) + ∑ j, Pi.single j (m j / n * n)`. Rewrite using `[Finset.univ_sum_single (fun j => m j / n * n)]`. Use function extensionality and compare the values at `i`.

Establish `h0` using `Int.emod_nonneg (m i) hn'.ne'`. Simplify using `only [r, Pi.add_apply, Int.toNat_of_nonneg h0]`. Use `Int.emod_add_mul_ediv (m i) n` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hm, h2]`.

Conclude with `hbox r`.
-/
theorem forall_of_box_of_translate {g n : ℕ} (hn : 1 ≤ n) (P : (Fin g → ℤ) → Prop)
    (hP : ∀ m j, P (m + Pi.single j (n : ℤ)) ↔ P m)
    (hbox : ∀ r : Fin g → Fin n, P (fun i => ((r i : ℕ) : ℤ))) (m : Fin g → ℤ) : P m := by
  have h1 : ∀ (j : Fin g) (k : ℤ) (m : Fin g → ℤ), P (m + Pi.single j (k * n)) ↔ P m := by
    intro j k
    induction k using Int.induction_on with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have : m + Pi.single j (((k : ℤ) + 1) * n) =
          (m + Pi.single j ((k : ℤ) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [this, hP, ih]
    | pred k ih =>
      intro m
      have : m + Pi.single j ((-(k : ℤ)) * n) =
          (m + Pi.single j ((-(k : ℤ) - 1) * n)) + Pi.single j (n : ℤ) := by
        rw [add_assoc, ← Pi.single_add]; congr 2; ring
      rw [← ih m, this, hP]
  have h2 : ∀ (k : Fin g → ℤ) (s : Finset (Fin g)) (m : Fin g → ℤ),
      P (m + ∑ j ∈ s, Pi.single j (k j * n)) ↔ P m := by
    intro k s
    induction s using Finset.induction_on with
    | empty => intro m; simp
    | insert a s ha ih =>
      intro m
      rw [Finset.sum_insert ha, add_comm (Pi.single a _), ← add_assoc, h1, ih]
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  let r : Fin g → Fin n := fun i => ⟨(m i % n).toNat, by
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    have h1 := Int.emod_lt_of_pos (m i) hn'
    omega⟩
  have hm : m = (fun i => ((r i : ℕ) : ℤ)) + ∑ j, Pi.single j (m j / n * n) := by
    rw [Finset.univ_sum_single (fun j => m j / n * n)]
    funext i
    have h0 := Int.emod_nonneg (m i) hn'.ne'
    simp only [r, Pi.add_apply, Int.toNat_of_nonneg h0]
    have := Int.emod_add_mul_ediv (m i) n
    linarith
  rw [hm, h2]
  exact hbox r

/- English proof (translation)
Introduce `hshift huniq g n τ b hn hb N f hf hli`. Set `c : ((Fin g → ℂ) → ℂ) → (Fin g → ℤ) → ℂ` to `fun F m => ∫ x in Set.Icc (0 : Fin g → ℝ) 1, F (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))`. Establish `key : ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ (i : Fin g) z, F (z + Pi.single i 1) = F z) → (∀ (j : Fin g) z, F (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * F z) → (∀ r : Fin g → Fin n, c F (fun i => ((r i : ℕ) : ℤ)) = 0) → F = 0`. Introduce `F hd hp hl hbox`. Use `huniq g F hd hp (forall_of_box_of_translate hn (fun m => c F m = 0) ?_ hbox)` and prove the remaining obligations.

Introduce `m j`. Establish `h` using `hshift g F hd hp m (τ.mulVec (Pi.single j 1))`. Establish `h' : (∫ x in Set.Icc (0 : Fin g → ℝ) 1, F ((fun i => (x i : ℂ)) + τ.mulVec (Pi.single j 1)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = b j ^ n * c F (m + Pi.single j (n : ℤ))`. Simplify using `only [c]`. Rewrite using `[← MeasureTheory.integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `hs : ∑ i, (((m + Pi.single j (n : ℤ) : Fin g → ℤ) i : ℤ) : ℂ) * (x i : ℂ) = n * (x j : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ)`. Simplify using `only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]`. Rewrite using `[add_comm]`.

Use `congr 1`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[Pi.single_eq_of_ne hi]`.

Simplify using the standard rewrite rules. Rewrite using `[hl, hs, mul_add, Complex.exp_add, mul_assoc (-(2 * Real.pi * I) : ℂ)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h']`. Express the relevant statement in the definitionally equal form `_ = _ * c F m at h`.

Establish `hb' : b j ^ n ≠ 0` using `pow_ne_zero _ (hb j)`. Prove the components needed by the constructor for the conclusion. Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `(mul_eq_zero.1 h.symm).resolve_left (Complex.exp_ne_zero _)`.

Introduce `h0`. Rewrite `h` using `[h0, mul_zero]`. Conclude with `(mul_eq_zero.1 h).resolve_left hb'`. Set `v : Fin N → (Fin g → Fin n) → ℂ` to `fun k r => c (f k) (fun i => ((r i : ℕ) : ℤ))`. Establish `hv : LinearIndependent ℂ v`.

Rewrite `hli`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `a ha`. Apply `hli a` to reduce the goal to its premises. Apply `key` to reduce the goal to its premises. Conclude with `Differentiable.sum fun k _ => (hf k).1.const_smul (a k)`.

Introduce `i z`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, (hf _).2.1]`. Introduce `j z`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, (hf _).2.2, Finset.mul_sum, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.

Introduce `r`. Establish `har` using `congrFun ha r`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, c] at har`. Rewrite using `[← har]`. Simplify using `only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]`.

Rewrite using `[MeasureTheory.integral_finsetSum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← MeasureTheory.integral_const_mul]`. Simplify using `only [mul_assoc]`. Introduce `k _`.

Establish `hk` using `(hf k).1.continuous`. Use `ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)` and prove the remaining obligations. Use `fun_prop`. Use `hv.fintype_card_le_finrank` as an intermediate fact. Simplify using `using this`.
-/
theorem card_le_pow_of_linearIndependent :
    (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → ∀ (m : Fin g → ℤ) (w : Fin g → ℂ), (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) * (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ)))) → (∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), Differentiable ℂ f → (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) → (∀ m : Fin g → ℤ, (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) = 0) → f = 0) → (∀ (g n : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (b : Fin g → ℂ), 1 ≤ n → (∀ j, b j ≠ 0) → ∀ (N : ℕ) (f : Fin N → (Fin g → ℂ) → ℂ), (∀ k, (Differentiable ℂ (f k) ∧ (∀ (i : Fin g) z, (f k) (z + Pi.single i 1) = (f k) z) ∧ ∀ (j : Fin g) z, (f k) (z + τ.mulVec (Pi.single j 1)) = b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * (f k) z)) → LinearIndependent ℂ f → N ≤ n ^ g) := by
  intro hshift huniq g n τ b hn hb N f hf hli
  let c : ((Fin g → ℂ) → ℂ) → (Fin g → ℤ) → ℂ := fun F m =>
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, F (fun i => (x i : ℂ)) *
      cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))
  have key : ∀ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F →
      (∀ (i : Fin g) z, F (z + Pi.single i 1) = F z) →
      (∀ (j : Fin g) z, F (z + τ.mulVec (Pi.single j 1)) =
        b j ^ n * cexp (-(2 * Real.pi * I) * n * z j) * F z) →
      (∀ r : Fin g → Fin n, c F (fun i => ((r i : ℕ) : ℤ)) = 0) → F = 0 := by
    intro F hd hp hl hbox
    refine huniq g F hd hp (forall_of_box_of_translate hn (fun m => c F m = 0) ?_ hbox)
    intro m j
    have h := hshift g F hd hp m (τ.mulVec (Pi.single j 1))
    have h' : (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
        F ((fun i => (x i : ℂ)) + τ.mulVec (Pi.single j 1)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
        b j ^ n * c F (m + Pi.single j (n : ℤ)) := by
      simp only [c]
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext x
      have hs : ∑ i, (((m + Pi.single j (n : ℤ) : Fin g → ℤ) i : ℤ) : ℂ) * (x i : ℂ) =
          n * (x j : ℂ) + ∑ i, (m i : ℂ) * (x i : ℂ) := by
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · simp
      rw [hl, hs, mul_add, Complex.exp_add, mul_assoc (-(2 * Real.pi * I) : ℂ)]
      ring
    rw [h'] at h
    change _ = _ * c F m at h
    have hb' : b j ^ n ≠ 0 := pow_ne_zero _ (hb j)
    constructor
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h.symm).resolve_left (Complex.exp_ne_zero _)
    · intro h0
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hb'
  let v : Fin N → (Fin g → Fin n) → ℂ := fun k r => c (f k) (fun i => ((r i : ℕ) : ℤ))
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro a ha
    apply hli a
    apply key
    · exact Differentiable.sum fun k _ => (hf k).1.const_smul (a k)
    · intro i z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.1]
    · intro j z
      simp only [Finset.sum_apply, Pi.smul_apply, (hf _).2.2, Finset.mul_sum, smul_eq_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    · intro r
      have har := congrFun ha r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, c] at har
      rw [← har]
      simp only [c, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [← MeasureTheory.integral_const_mul]
        simp only [mul_assoc]
      · intro k _
        have hk := (hf k).1.continuous
        refine ContinuousOn.integrableOn_Icc (Continuous.continuousOn ?_)
        fun_prop
  have := hv.fintype_card_le_finrank
  simpa using this

end GlobalTheory.ClassicalTheta
