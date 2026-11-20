import Mathlib
open NumberField
open scoped TensorProduct NNReal

/- English proof (translation)
Introduce `E _ _ d hd hd0`. Set `B` to `integralBasis E`. Establish `hrep : ∀ (x : E) i, B.repr x i = Algebra.trace ℚ E (x * B.traceDual i)` using `fun x i => by`. Establish `h` using `B.traceDual.traceDual_repr_apply x i`. Rewrite `h` using `[B.traceDual_traceDual, Algebra.traceForm_apply]`.

Conclude with `h`. Establish `hrep' : ∀ (x : E) i, B.traceDual.repr x i = Algebra.trace ℚ E (x * B i)` using `fun x i => by`. Establish `h` using `B.traceDual_repr_apply x i`. Rewrite `h` using `[Algebra.traceForm_apply]`. Conclude with `h`.

Establish `hc : ∀ i, ∃ c : 𝓞 E, (c : E) = B.traceDual i * d` using `fun i => by`. Establish `hx : B.traceDual i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)`. Rewrite using `[FractionalIdeal.mem_dual (by simp)]`. Introduce `a ha`. Take `⟨y, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`.

Use `⟨(RingOfIntegers.basis E).repr y i, ?_⟩` and prove the remaining obligations. Rewrite using `[← integralBasis_repr_apply]`. Establish `h` using `B.traceDual.traceDual_repr_apply (algebraMap (𝓞 E) E y) i`. Rewrite `h` using `[B.traceDual_traceDual, Algebra.traceForm_apply, mul_comm]`. Conclude with `h`.

Establish `hdd : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)` using `(FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩`. Rewrite `hdd` using `[coeIdeal_differentIdeal ℤ ℚ]`. Establish `hm` using `FractionalIdeal.mul_mem_mul hx hdd`. Rewrite `hm` using `[mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (by simp))]`. Conclude with `(FractionalIdeal.mem_one_iff _).1 hm`.

Use `choose c hc using hc`. Establish `hdE : (d : E) ≠ 0` using `fun h => hd0 (RingOfIntegers.ext h)`. Set `e` to `(Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm`. Establish `ha : ∀ i, ((RingOfIntegers.basis E i : 𝓞 E) : E) = B i` using `fun i => (integralBasis_apply E i).symm`. Establish `hdiv : ∀ (y : E) i, y * (c i : E) / (d : E) = y * B.traceDual i` using `fun y i => by`.

Rewrite using `[hc, ← mul_assoc, mul_div_cancel_right₀ _ hdE]`. Use `⟨_, fun j => RingOfIntegers.basis E (e j), fun j => c (e j), fun x => ?_, fun x => ?_, fun x i j => ?_⟩` and prove the remaining obligations. Simplify using `only [hdiv, ha, ← hrep]`. Rewrite using `[e.sum_comp (fun i => B.repr x i • B i)]`. Conclude with `B.sum_repr x`.

Establish `h1 : ∀ i, Algebra.trace ℚ E (x * B i / (d : E)) • (c i : E) = (B.traceDual.repr (x / d) i • B.traceDual i) * d` using `fun i => by`. Rewrite using `[hrep', hc, smul_mul_assoc, mul_div_right_comm]`. Simplify using `only [ha, h1]`. Rewrite using `[e.sum_comp (fun i => (B.traceDual.repr (x / d) i • B.traceDual i) * (d : E)), ← Finset.sum_mul, B.traceDual.sum_repr, div_mul_cancel₀ _ hdE]`. Use `⟨(RingOfIntegers.basis E).repr (x * RingOfIntegers.basis E (e j)) (e i), ?_⟩` and prove the remaining obligations.

Rewrite using `[hdiv, ← hrep]`. Establish `h` using `integralBasis_repr_apply E (x * RingOfIntegers.basis E (e j)) (e i)`. Rewrite `h` using `[map_mul]`. Conclude with `h.symm`.
-/
theorem UpperTheory.WildB.dualFamily :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E), d ∈ differentIdeal ℤ (𝓞 E) → d ≠ 0 → ∃ (n : ℕ) (a b : Fin n → 𝓞 E), (∀ x : E, ∑ j, Algebra.trace ℚ E (x * (b j : E) / (d : E)) • (a j : E) = x) ∧ (∀ x : E, ∑ j, Algebra.trace ℚ E (x * (a j : E) / (d : E)) • (b j : E) = x) ∧ ∀ (x : 𝓞 E) (i j : Fin n), ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E ((x : E) * (a j : E) * (b i : E) / (d : E)) := by
  intro E _ _ d hd hd0
  classical
  let B := integralBasis E
  have hrep : ∀ (x : E) i, B.repr x i = Algebra.trace ℚ E (x * B.traceDual i) := fun x i => by
    have h := B.traceDual.traceDual_repr_apply x i
    rw [B.traceDual_traceDual, Algebra.traceForm_apply] at h
    exact h
  have hrep' : ∀ (x : E) i, B.traceDual.repr x i = Algebra.trace ℚ E (x * B i) := fun x i => by
    have h := B.traceDual_repr_apply x i
    rw [Algebra.traceForm_apply] at h
    exact h
  have hc : ∀ i, ∃ c : 𝓞 E, (c : E) = B.traceDual i * d := fun i => by
    have hx : B.traceDual i ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
      rw [FractionalIdeal.mem_dual (by simp)]
      intro a ha
      obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      refine ⟨(RingOfIntegers.basis E).repr y i, ?_⟩
      rw [← integralBasis_repr_apply]
      have h := B.traceDual.traceDual_repr_apply (algebraMap (𝓞 E) E y) i
      rw [B.traceDual_traceDual, Algebra.traceForm_apply, mul_comm] at h
      exact h
    have hdd : (d : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at hdd
    have hm := FractionalIdeal.mul_mem_mul hx hdd
    rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (by simp))] at hm
    exact (FractionalIdeal.mem_one_iff _).1 hm
  choose c hc using hc
  have hdE : (d : E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
  have ha : ∀ i, ((RingOfIntegers.basis E i : 𝓞 E) : E) = B i := fun i =>
    (integralBasis_apply E i).symm
  have hdiv : ∀ (y : E) i, y * (c i : E) / (d : E) = y * B.traceDual i := fun y i => by
    rw [hc, ← mul_assoc, mul_div_cancel_right₀ _ hdE]
  refine ⟨_, fun j => RingOfIntegers.basis E (e j), fun j => c (e j), fun x => ?_, fun x => ?_,
    fun x i j => ?_⟩
  · simp only [hdiv, ha, ← hrep]
    rw [e.sum_comp (fun i => B.repr x i • B i)]
    exact B.sum_repr x
  · have h1 : ∀ i, Algebra.trace ℚ E (x * B i / (d : E)) • (c i : E)
        = (B.traceDual.repr (x / d) i • B.traceDual i) * d := fun i => by
      rw [hrep', hc, smul_mul_assoc, mul_div_right_comm]
    simp only [ha, h1]
    rw [e.sum_comp (fun i => (B.traceDual.repr (x / d) i • B.traceDual i) * (d : E)),
      ← Finset.sum_mul, B.traceDual.sum_repr, div_mul_cancel₀ _ hdE]
  · refine ⟨(RingOfIntegers.basis E).repr (x * RingOfIntegers.basis E (e j)) (e i), ?_⟩
    rw [hdiv, ← hrep]
    have h := integralBasis_repr_apply E (x * RingOfIntegers.basis E (e j)) (e i)
    rw [map_mul] at h
    exact h.symm
