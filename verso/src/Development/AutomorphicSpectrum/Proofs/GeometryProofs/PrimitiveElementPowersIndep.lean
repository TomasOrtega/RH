import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HopfPrim

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A]

/- English proof (translation)
Establish `h1 : Coalgebra.comul (R` using `k) (f ^ i) = (f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) ^ i := by`. Rewrite using `[← hf, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]`. Rewrite using `[h1, add_pow]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]`.
-/
theorem comul_pow_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (i : ℕ) :
    Coalgebra.comul (R := k) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) • ((f ^ l) ⊗ₜ[k] (f ^ (i - l))) := by
  have h1 : Coalgebra.comul (R := k) (f ^ i) = (f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) ^ i := by
    rw [← hf, ← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply]
  rw [h1, add_pow]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_pow, mul_one, one_mul,
    Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

noncomputable def convPow (y : A →ₗ[k] k) : ℕ → (A →ₗ[k] k)
  | 0 => Coalgebra.counit
  | m + 1 => LinearMap.mul' k k ∘ₗ TensorProduct.map y (convPow y m) ∘ₗ Coalgebra.comul

/- English proof (translation)
Simplify using `only [convPow, LinearMap.comp_apply]`. Rewrite using `[comul_pow_of_primitive f hf i, map_sum, map_sum]`. Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]`.
-/
theorem convPow_succ_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (m i : ℕ) :
    convPow y (m + 1) (f ^ i) =
      ∑ l ∈ Finset.range (i + 1), (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) := by
  simp only [convPow, LinearMap.comp_apply]
  rw [comul_pow_of_primitive f hf i, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [map_smul, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Use `⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩` and prove the remaining obligations. Simplify using `[convPow]`. Consider the case `succ m ih`.

Establish `hterm : ∀ i ≤ m + 1, ∀ l ∈ Finset.range (i + 1), l ≠ 1 → (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) = 0`. Introduce `i hi l hl hl1`. Break down `Nat.lt_or_ge l 2 with h | h` into its components or cases. Establish `: l = 0` using `by omega`. Substitute `this` using the available equality.

Simplify using `[hy1]`. Establish `hlt : i - l < m`. Use `Finset.mem_range.mp hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[ih.1 _ hlt, mul_zero, mul_zero]`.

Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[convPow_succ_pow y f hf m i]`. Use `Finset.sum_eq_zero (fun l hl => ?_)` and prove the remaining obligations. Distinguish the cases in `hl1 : l = 1`. Substitute `hl1` using the available equality.

Establish `hlt : i - 1 < m`. Use `Finset.mem_range.mp hl` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[ih.1 _ hlt, mul_zero, mul_zero]`. Conclude with `hterm i hi.le l hl hl1`.

Rewrite using `[convPow_succ_pow y f hf m (m + 1), Finset.sum_eq_single 1 (fun l hl hl1 => hterm (m + 1) le_rfl l hl hl1) (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]`. Rewrite using `[pow_one, hyf, Nat.add_sub_cancel, ih.2, Nat.choose_one_right, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem convPow_pow (y : A →ₗ[k] k) (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f)
    (hy1 : y 1 = 0) (hyf : y f = 1) (m : ℕ) :
    (∀ i < m, convPow y m (f ^ i) = 0) ∧ convPow y m (f ^ m) = (m.factorial : k) := by
  induction m with
  | zero =>
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
    simp [convPow]
  | succ m ih =>
    have hterm : ∀ i ≤ m + 1, ∀ l ∈ Finset.range (i + 1), l ≠ 1 →
        (i.choose l : k) * (y (f ^ l) * convPow y m (f ^ (i - l))) = 0 := by
      intro i hi l hl hl1
      rcases Nat.lt_or_ge l 2 with h | h
      · have : l = 0 := by omega
        subst this
        simp [hy1]
      · have hlt : i - l < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [convPow_succ_pow y f hf m i]
      refine Finset.sum_eq_zero (fun l hl => ?_)
      by_cases hl1 : l = 1
      · subst hl1
        have hlt : i - 1 < m := by
          have := Finset.mem_range.mp hl
          omega
        rw [ih.1 _ hlt, mul_zero, mul_zero]
      · exact hterm i hi.le l hl hl1
    · rw [convPow_succ_pow y f hf m (m + 1),
        Finset.sum_eq_single 1 (fun l hl hl1 => hterm (m + 1) le_rfl l hl hl1)
          (fun h => absurd (Finset.mem_range.mpr (by omega)) h)]
      rw [pow_one, hyf, Nat.add_sub_cancel, ih.2, Nat.choose_one_right, Nat.factorial_succ]
      push_cast
      ring

/- English proof (translation)
Establish `key` using `congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A Coalgebra.counit t)) hf`. Simplify using `only [Coalgebra.rTensor_counit_comul, map_add, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Bialgebra.counit_one, one_smul] at key`. Establish `h2 : Coalgebra.counit (R` using `k) f • (1 : A) = 0 := by`. Use `congrArg (· - f) key` as an intermediate fact. Simplify using `using this.symm`.

Rewrite `h2` using `[Algebra.smul_def, mul_one]`. Conclude with `(algebraMap k A).injective (h2.trans (map_zero _).symm)`.
-/
theorem counit_eq_zero_of_primitive [Nontrivial A] (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) :
    Coalgebra.counit (R := k) f = 0 := by
  have key := congrArg (fun t => TensorProduct.lid k A (LinearMap.rTensor A Coalgebra.counit t)) hf
  simp only [Coalgebra.rTensor_counit_comul, map_add, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul, Bialgebra.counit_one, one_smul] at key
  have h2 : Coalgebra.counit (R := k) f • (1 : A) = 0 := by
    have := congrArg (· - f) key
    simpa using this.symm
  rw [Algebra.smul_def, mul_one] at h2
  exact (algebraMap k A).injective (h2.trans (map_zero _).symm)

/- English proof (translation)
Establish `: Nontrivial A` using `nontrivial_of_ne f 0 hf0`. Establish `hε` using `counit_eq_zero_of_primitive f hf`. Set `p : Submodule k A` to `k ∙ (1 : A)`. Establish `hfp : Submodule.Quotient.mk (p` using `p) f ≠ 0 := by`. Rewrite using `[ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]`.

Introduce and unpack `⟨a, rfl⟩`. Apply `hf0` to reduce the goal to its premises. Rewrite `hε` using `[map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one]`. Rewrite using `[hε, zero_smul]`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ p), φ (Submodule.Quotient.mk f) ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hfp ((Module.forall_dual_apply_eq_zero_iff k _).mp h)`. Use `⟨(φ (Submodule.Quotient.mk f))⁻¹ • (φ ∘ₗ p.mkQ), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Submodule.Quotient.mk (p` using `p) (1 : A) = 0 := (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_span_singleton_self 1)`.

Simplify using `[h1]`. Simplify using `[inv_mul_cancel₀ hφ]`.
-/
theorem exists_form_of_primitive (f : A)
    (hf : Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f) (hf0 : f ≠ 0) :
    ∃ y : A →ₗ[k] k, y 1 = 0 ∧ y f = 1 := by
  have : Nontrivial A := nontrivial_of_ne f 0 hf0
  have hε := counit_eq_zero_of_primitive f hf
  let p : Submodule k A := k ∙ (1 : A)
  have hfp : Submodule.Quotient.mk (p := p) f ≠ 0 := by
    rw [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
    rintro ⟨a, rfl⟩
    apply hf0
    rw [map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one] at hε
    rw [hε, zero_smul]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (A ⧸ p), φ (Submodule.Quotient.mk f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hfp ((Module.forall_dual_apply_eq_zero_iff k _).mp h)
  refine ⟨(φ (Submodule.Quotient.mk f))⁻¹ • (φ ∘ₗ p.mkQ), ?_, ?_⟩
  · have h1 : Submodule.Quotient.mk (p := p) (1 : A) = 0 :=
      (Submodule.Quotient.mk_eq_zero p).mpr (Submodule.mem_span_singleton_self 1)
    simp [h1]
  · simp [inv_mul_cancel₀ hφ]

/- English proof (translation)
Introduce `k _ p _ _ A _ _ _ _ f hf hf0 c hsum`. Take `⟨y, hy1, hyf⟩` from `exists_form_of_primitive f hf hf0`. Establish `key : ∀ m < p, (∀ i, m < i → i < p → c i = 0) → c m = 0`. Introduce `m hm hgt`. Establish `h` using `congrArg (convPow y m) hsum`.

Rewrite `h` using `[map_sum, map_zero]`. Simplify using `only [map_smul, smul_eq_mul] at h`. Rewrite `h` using `[Finset.sum_eq_single m]`. Rewrite `h` using `[(convPow_pow y f hf hy1 hyf m).2]`. Establish `hfact : (m.factorial : k) ≠ 0`.

Rewrite using `[ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial (Fact.out)]`. Use linear arithmetic over natural numbers and integers. Conclude with `(mul_eq_zero.mp h).resolve_right hfact`. Introduce `i hi hne`. Break down `Nat.lt_or_gt_of_ne hne with h' | h'` into its components or cases.

Rewrite using `[(convPow_pow y f hf hy1 hyf m).1 i h', mul_zero]`. Rewrite using `[hgt i h' (Finset.mem_range.mp hi), zero_mul]`. Introduce `h'`. Conclude with `absurd (Finset.mem_range.mpr hm) h'`. Establish `hall : ∀ n, ∀ i < p, p - 1 - i < n → c i = 0`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro i _ h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`.

Introduce `i hi hn`. Conclude with `key i hi (fun j hij hj => ih j hj (by omega))`. Introduce `i hi`. Conclude with `hall p i hi (by omega)`.
-/
theorem powers_indep_of_primitive :
    ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  intro k _ p _ _ A _ _ _ _ f hf hf0 c hsum
  obtain ⟨y, hy1, hyf⟩ := exists_form_of_primitive f hf hf0
  have key : ∀ m < p, (∀ i, m < i → i < p → c i = 0) → c m = 0 := by
    intro m hm hgt
    have h := congrArg (convPow y m) hsum
    rw [map_sum, map_zero] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [Finset.sum_eq_single m] at h
    · rw [(convPow_pow y f hf hy1 hyf m).2] at h
      have hfact : (m.factorial : k) ≠ 0 := by
        rw [ne_eq, CharP.cast_eq_zero_iff k p, Nat.Prime.dvd_factorial (Fact.out)]
        omega
      exact (mul_eq_zero.mp h).resolve_right hfact
    · intro i hi hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · rw [(convPow_pow y f hf hy1 hyf m).1 i h', mul_zero]
      · rw [hgt i h' (Finset.mem_range.mp hi), zero_mul]
    · intro h'
      exact absurd (Finset.mem_range.mpr hm) h'
  have hall : ∀ n, ∀ i < p, p - 1 - i < n → c i = 0 := by
    intro n
    induction n with
    | zero => intro i _ h; omega
    | succ n ih =>
      intro i hi hn
      exact key i hi (fun j hij hj => ih j hj (by omega))
  intro i hi
  exact hall p i hi (by omega)

end GlobalTheory.CompanionTheory.HopfPrim
