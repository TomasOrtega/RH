import Mathlib

/- English proof (translation)
Set `K : Submodule ℂ (Fin n → ℂ)` to `{ carrier := {y | f y = 0} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[map_add, ha, hb, add_zero]`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := fun z y hy => by`.

Simplify using `only [Set.mem_setOf_eq] at hy ⊢`. Establish `hz : z • y = z.re • y + z.im • (Complex.I • y)`. Use extensionality with `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]`. Use `conv_lhs => rw [← Complex.re_add_im z]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz, map_add, map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }`. Use `⟨K, fun y => Iff.rfl, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker f`. Establish `h2 : LinearMap.ker f = K.restrictScalars ℝ`.

Use extensionality with `y`. Both sides reduce to the same expression. Establish `h3 : LinearMap.range f ≤ U.restrictScalars ℝ`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hU y`.

Establish `h4` using `Submodule.finrank_mono h3`. Establish `h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U` using `finrank_real_of_complex U`. Establish `h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K` using `finrank_real_of_complex K`. Establish `h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n`. Rewrite using `[finrank_real_of_complex]`.

Simplify using the standard rewrite rules. Rewrite `h1` using `[h2, h6, h7]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem exists_ker {n g : ℕ} (f : (Fin n → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (U : Submodule ℂ (Fin g → ℂ)) (hU : ∀ y, f y ∈ U)
    (hI : ∀ y, f y = 0 → f (Complex.I • y) = 0) :
    ∃ K : Submodule ℂ (Fin n → ℂ), (∀ y, y ∈ K ↔ f y = 0) ∧
      n ≤ Module.finrank ℂ K + Module.finrank ℂ U := by
  let K : Submodule ℂ (Fin n → ℂ) :=
    { carrier := {y | f y = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun z y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have hz : z • y = z.re • y + z.im • (Complex.I • y) := by
          ext i
          simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.real_smul]
          conv_lhs => rw [← Complex.re_add_im z]
          ring
        rw [hz, map_add, map_smul, map_smul, hy, hI y hy, smul_zero, smul_zero, add_zero] }
  refine ⟨K, fun y => Iff.rfl, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.ker f = K.restrictScalars ℝ := by
    ext y
    rfl
  have h3 : LinearMap.range f ≤ U.restrictScalars ℝ := by
    rintro _ ⟨y, rfl⟩
    exact hU y
  have h4 := Submodule.finrank_mono h3
  have h5 : Module.finrank ℝ (U.restrictScalars ℝ) = 2 * Module.finrank ℂ U :=
    finrank_real_of_complex U
  have h6 : Module.finrank ℝ (K.restrictScalars ℝ) = 2 * Module.finrank ℂ K :=
    finrank_real_of_complex K
  have h7 : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [finrank_real_of_complex]; simp
  rw [h2, h6, h7] at h1
  omega

/- English proof (translation)
Introduce `g j j' p H S c U U' hH hS hc hp hU hU' hA hB`. Set `Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)` to `{ toFun := fun y => Complex.I • p (Complex.I • y) map_add' := fun a b => by rw [smul_add, map_add, smul_add] map_smul' := fun r a => by`. Rewrite using `[smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]`. Use `rfl }`. Establish `hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v`.

Introduce `m v`. Rewrite using `[smul_smul, Complex.I_mul_I, neg_smul, one_smul]`. Establish `eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 → p (Complex.I • y) = -(Complex.I • p y)`. Introduce `y hy`. Rewrite using `[sub_eq_zero.mp hy, hII, neg_neg]`.

Establish `eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 → p (Complex.I • y) = Complex.I • p y`. Introduce `y hy`. Rewrite using `[eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]`. Take `⟨K, hK, dK⟩` from `exists_ker (p - Q) U hA (by`. Introduce `y hy`.

Express the relevant statement in the definitionally equal form `p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0`. Rewrite using `[hII, map_neg, eA y hy, smul_neg, sub_self])`. Take `⟨K', hK', dK'⟩` from `exists_ker (p + Q) U' hB (by`. Introduce `y hy`. Express the relevant statement in the definitionally equal form `p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0`.

Rewrite using `[hII, map_neg, eB y hy, smul_neg, add_neg_cancel])`. Establish `hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im = -(2 * c * (dotProduct (star y') (S.mulVec y)).im)`. Introduce `y y'`. Rewrite using `[hp]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `hinj : ∀ y, y ≠ 0 → p y ≠ 0`. Introduce `y hy h0`. Apply `hy` to reduce the goal to its premises. Establish `hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0`.

Introduce `y'`. Establish `h` using `hp' y y'`. Rewrite `h` using `[h0, zero_dotProduct, Complex.zero_im]`. Establish `: c * (dotProduct (star y') (S.mulVec y)).im = 0` using `by linarith`. Conclude with `(mul_eq_zero.mp this).resolve_left hc.ne'`.

Establish `hSy : S.mulVec y = 0`. Use extensionality with `i`. Establish `h1` using `hz (Pi.single i 1)`. Establish `h2` using `hz (Pi.single i Complex.I)`. Simplify using `[← Pi.single_star] at h1 h2`.

Apply the tactic sequence `apply Complex.ext <;> simp [h1, h2]`. Conclude with `Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy`. Use `⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy h0`. Establish `h1` using `hH _ (hinj y h0)`.

Establish `h2` using `hp' (Complex.I • y) y`. Rewrite `h2` using `[eA y ((hK y).mp hy)]`. Simplify using `[Matrix.mulVec_smul] at h2`. Assume the negation of the conclusion as `hn`. Use `mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `y hy h0`. Establish `h1` using `hH _ (hinj y h0)`. Establish `h2` using `hp' (Complex.I • y) y`. Rewrite `h2` using `[eB y ((hK' y).mp hy)]`.

Simplify using `[Matrix.mulVec_smul] at h2`. Assume the negation of the conclusion as `hn`. Use `mul_nonneg hc.le (not_lt.mp hn)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `y hy y' hy'`.

Establish `e1` using `eA y ((hK y).mp hy)`. Establish `e2` using `eB y' ((hK' y').mp hy')`. Establish `h1` using `hp' y y'`. Establish `h2` using `hp' (Complex.I • y) y'`. Establish `h3` using `hp' y (Complex.I • y')`.

Establish `h4` using `hp' (Complex.I • y) (Complex.I • y')`. Rewrite `h2`, `h4` using `[e1]`. Rewrite `h3`, `h4` using `[e2]`. Simplify using `[Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4`. Establish `r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0` using `by linarith`.

Establish `r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0` using `by linarith`. Conclude with `Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne') ((mul_eq_zero.mp r2).resolve_left hc.ne')`.
-/
theorem UpperTheory.hermitian_positive_symplectic :
    ∀ {g j j' : ℕ} (p : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ)
        (S : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) (c : ℝ) (U U' : Submodule ℂ (Fin g → ℂ)),
        (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (dotProduct z (H.mulVec (star z))).re) →
        IsUnit S.det → 0 < c →
        (∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
          2 * (Complex.I * (c : ℂ) * dotProduct (star y') (S.mulVec y)).re) →
        Module.finrank ℂ U = j' → Module.finrank ℂ U' = j →
        (∀ y, p y - Complex.I • p (Complex.I • y) ∈ U) →
        (∀ y, p y + Complex.I • p (Complex.I • y) ∈ U') →
        ∃ K K' : Submodule ℂ (Fin (j + j') → ℂ),
          j ≤ Module.finrank ℂ K ∧ j' ≤ Module.finrank ℂ K' ∧
          (∀ y ∈ K, p y - Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K', p y + Complex.I • p (Complex.I • y) = 0) ∧
          (∀ y ∈ K, y ≠ 0 → 0 < (dotProduct (star y) (S.mulVec y)).re) ∧
          (∀ y ∈ K', y ≠ 0 → (dotProduct (star y) (S.mulVec y)).re < 0) ∧
          ∀ y ∈ K, ∀ y' ∈ K', dotProduct (star y') (S.mulVec y) = 0 := by
  intro g j j' p H S c U U' hH hS hc hp hU hU' hA hB
  let Q : (Fin (j + j') → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun y => Complex.I • p (Complex.I • y)
      map_add' := fun a b => by rw [smul_add, map_add, smul_add]
      map_smul' := fun r a => by
        rw [smul_comm Complex.I r a, map_smul, smul_comm Complex.I r]; rfl }
  have hII : ∀ {m : ℕ} (v : Fin m → ℂ), Complex.I • Complex.I • v = -v := by
    intro m v
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  have eA : ∀ y, p y - Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = -(Complex.I • p y) := by
    intro y hy
    rw [sub_eq_zero.mp hy, hII, neg_neg]
  have eB : ∀ y, p y + Complex.I • p (Complex.I • y) = 0 →
      p (Complex.I • y) = Complex.I • p y := by
    intro y hy
    rw [eq_neg_of_add_eq_zero_left hy, smul_neg, hII, neg_neg]
  obtain ⟨K, hK, dK⟩ := exists_ker (p - Q) U hA (by
    intro y hy
    change p (Complex.I • y) - Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eA y hy, smul_neg, sub_self])
  obtain ⟨K', hK', dK'⟩ := exists_ker (p + Q) U' hB (by
    intro y hy
    change p (Complex.I • y) + Complex.I • p (Complex.I • Complex.I • y) = 0
    rw [hII, map_neg, eB y hy, smul_neg, add_neg_cancel])
  have hp' : ∀ y y', (dotProduct (p y) (H.mulVec (star (p y')))).im =
      -(2 * c * (dotProduct (star y') (S.mulVec y)).im) := by
    intro y y'
    rw [hp]
    simp
    ring
  have hinj : ∀ y, y ≠ 0 → p y ≠ 0 := by
    intro y hy h0
    apply hy
    have hz : ∀ y', (dotProduct (star y') (S.mulVec y)).im = 0 := by
      intro y'
      have h := hp' y y'
      rw [h0, zero_dotProduct, Complex.zero_im] at h
      have : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hc.ne'
    have hSy : S.mulVec y = 0 := by
      ext i
      have h1 := hz (Pi.single i 1)
      have h2 := hz (Pi.single i Complex.I)
      simp [← Pi.single_star] at h1 h2
      apply Complex.ext <;> simp [h1, h2]
    exact Matrix.eq_zero_of_mulVec_eq_zero hS.ne_zero hSy
  refine ⟨K, K', by omega, by omega, fun y hy => (hK y).mp hy, fun y hy => (hK' y).mp hy,
    ?_, ?_, ?_⟩
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eA y ((hK y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (neg_nonneg.mpr (not_lt.mp hn))
    linarith
  · intro y hy h0
    have h1 := hH _ (hinj y h0)
    have h2 := hp' (Complex.I • y) y
    rw [eB y ((hK' y).mp hy)] at h2
    simp [Matrix.mulVec_smul] at h2
    by_contra hn
    have := mul_nonneg hc.le (not_lt.mp hn)
    linarith
  · intro y hy y' hy'
    have e1 := eA y ((hK y).mp hy)
    have e2 := eB y' ((hK' y').mp hy')
    have h1 := hp' y y'
    have h2 := hp' (Complex.I • y) y'
    have h3 := hp' y (Complex.I • y')
    have h4 := hp' (Complex.I • y) (Complex.I • y')
    rw [e1] at h2 h4
    rw [e2] at h3 h4
    simp [Matrix.mulVec_smul, Matrix.mulVec_neg] at h2 h3 h4
    have r1 : c * (dotProduct (star y') (S.mulVec y)).re = 0 := by linarith
    have r2 : c * (dotProduct (star y') (S.mulVec y)).im = 0 := by linarith
    exact Complex.ext ((mul_eq_zero.mp r1).resolve_left hc.ne')
      ((mul_eq_zero.mp r2).resolve_left hc.ne')
