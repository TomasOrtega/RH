import Mathlib

open Polynomial Matrix

namespace GlobalTheory.SimAlg

/- English proof (translation)
Establish `h0 : Q 0 = 0` using `by have := h 0 0; simp at this; omega`. Establish `h3 : ∀ x y z, Q (x + y + z) = Q (x + y) + Q (x + z) + Q (y + z) - Q x - Q y - Q z`. Introduce `x y z`. Establish `a1` using `h (x + y) z`. Establish `a2` using `h (x + z) y`.

Establish `a3` using `h x (y - z)`. Establish `a4` using `h y z`. Rewrite `a2` using `[show x + z + y = x + y + z by abel]`. Rewrite `a3` using `[show x + (y - z) = x + y - z by abel, show x - (y - z) = x + z - y by abel]`. Use linear arithmetic over natural numbers and integers.

Set `b0 : Λ →+ Λ →+ ℤ` to `AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Q (x + y) - Q x - Q y) (by intro y z; rw [← add_assoc, h3]; ring)) (by`. Introduce `x y`. Use extensionality with `z`. Simplify using `only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]`. Rewrite using `[h3]`.

Use the proof step `ring)`. Use `⟨LinearMap.mk₂ ℤ (fun x y => b0 x y) (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp), fun x y => rfl, fun x => ?_⟩` and prove the remaining obligations. Use `h x x` as an intermediate fact. Rewrite `this` using `[sub_self, h0]`. Express the relevant statement in the definitionally equal form `Q (x + x) - Q x - Q x = _`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exists_polar {Λ : Type} [AddCommGroup Λ] (Q : Λ → ℤ)
    (h : ∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) :
    ∃ b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x y, b x y = Q (x + y) - Q x - Q y) ∧ ∀ x, b x x = 2 * Q x := by
  have h0 : Q 0 = 0 := by have := h 0 0; simp at this; omega
  have h3 : ∀ x y z, Q (x + y + z) = Q (x + y) + Q (x + z) + Q (y + z) - Q x - Q y - Q z := by
    intro x y z
    have a1 := h (x + y) z
    have a2 := h (x + z) y
    have a3 := h x (y - z)
    have a4 := h y z
    rw [show x + z + y = x + y + z by abel] at a2
    rw [show x + (y - z) = x + y - z by abel, show x - (y - z) = x + z - y by abel] at a3
    omega
  let b0 : Λ →+ Λ →+ ℤ := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Q (x + y) - Q x - Q y)
    (by intro y z; rw [← add_assoc, h3]; ring)) (by
      intro x y; ext z
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [h3]; ring)
  refine ⟨LinearMap.mk₂ ℤ (fun x y => b0 x y) (by intros; simp) (by intros; simp)
    (by intros; simp) (by intros; simp), fun x y => rfl, fun x => ?_⟩
  have := h x x
  rw [sub_self, h0] at this
  change Q (x + x) - Q x - Q x = _
  omega

/- English proof (translation)
Introduce `h`. Take `⟨v, hv, hv'⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 h`. Use `hG v hv` as an intermediate fact. Rewrite `this` using `[hv']`. Simplify using `at this`.
-/
theorem det_ne_zero {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) : G.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv'⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have := hG v hv
  rw [hv'] at this
  simp at this

/- English proof (translation)
Establish `hZ : ∀ c : Fin d → ℤ, 0 ≤ ∑ i, ∑ j, c i * c j * G i j`. Introduce `c`. Distinguish the cases in `hc : c = 0`. Simplify using `[hc]`. Use `(hG c hc).le` as an intermediate fact.

Simplify using `only [dotProduct, mulVec, Finset.mul_sum] at this`. Use `this.trans_eq ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `hQ : ∀ c : Fin d → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ)`. Introduce `c`.

Take `⟨m, hm⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) c`. Use `choose a ha using hm`. Establish `hm0 : ((m : ℤ) : ℝ) ≠ 0` using `by exact_mod_cast nonZeroDivisors.coe_ne_zero m`. Establish `ha' : ∀ i, (a i : ℝ) = ((m : ℤ) : ℝ) * (c i : ℝ)`. Introduce `i`.

Use `ha i` as an intermediate fact. Simplify using `only [eq_intCast, zsmul_eq_mul, Submonoid.smul_def] at this`. Conclude with `this` after adjusting the coercions. Establish `h1 : (0 : ℝ) ≤ ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ)`. Conclude with `hZ a` after adjusting the coercions.

Establish `h2 : ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ) = ((m : ℤ) : ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ)`. Simplify using `only [Finset.mul_sum, ha']`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Rewrite `h1` using `[h2]`. Conclude with `(mul_nonneg_iff_of_pos_left (by positivity)).1 h1`.

Establish `hd : DenseRange (Pi.map fun (_ : Fin d) => ((↑) : ℚ → ℝ))` using `DenseRange.piMap fun _ => Rat.denseRange_cast`. Use `hd.induction_on (p := fun x : Fin d → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ)) x ?_ hQ` and prove the remaining obligations. Conclude with `isClosed_le continuous_const (by fun_prop)`.
-/
theorem real_nonneg {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ) :
    0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ) := by
  have hZ : ∀ c : Fin d → ℤ, 0 ≤ ∑ i, ∑ j, c i * c j * G i j := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · have := (hG c hc).le
      simp only [dotProduct, mulVec, Finset.mul_sum] at this
      refine this.trans_eq ?_
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hQ : ∀ c : Fin d → ℚ, 0 ≤ ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ) := by
    intro c
    obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) c
    choose a ha using hm
    have hm0 : ((m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero m
    have ha' : ∀ i, (a i : ℝ) = ((m : ℤ) : ℝ) * (c i : ℝ) := by
      intro i
      have := ha i
      simp only [eq_intCast, zsmul_eq_mul, Submonoid.smul_def] at this
      exact_mod_cast this
    have h1 : (0 : ℝ) ≤ ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ) := by
      exact_mod_cast hZ a
    have h2 : ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * (G i j : ℝ)
        = ((m : ℤ) : ℝ) ^ 2 * ∑ i, ∑ j, (c i : ℝ) * (c j : ℝ) * (G i j : ℝ) := by
      simp only [Finset.mul_sum, ha']
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h2] at h1
    exact (mul_nonneg_iff_of_pos_left (by positivity)).1 h1
  have hd : DenseRange (Pi.map fun (_ : Fin d) => ((↑) : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x : Fin d → ℝ => 0 ≤ ∑ i, ∑ j, x i * x j * (G i j : ℝ)) x ?_ hQ
  exact isClosed_le continuous_const (by fun_prop)

/- English proof (translation)
Use `set M : Matrix (Fin d) (Fin d) ℝ := G.map (Int.castRingHom ℝ) with hM`. Establish `key : ∀ y : Fin d → ℝ, star y ⬝ᵥ M *ᵥ y = ∑ i, ∑ j, y i * y j * (G i j : ℝ)`. Introduce `y`. Simplify using `only [dotProduct, mulVec, Finset.mul_sum, hM]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hp : M.PosSemidef`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `[hM, hs i j]`. Rewrite using `[key]`. Conclude with `real_nonneg G hG y`. Establish `h0 : M *ᵥ x = 0` using `(hp.dotProduct_mulVec_zero_iff x).1 (by rw [key, hx])`. Assume the negation of the conclusion as `hne`.

Establish `: M.det = 0` using `Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hne, h0⟩`. Rewrite `this` using `[hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `det_ne_zero G hG (by simpa using this)`.
-/
theorem real_pos {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ) (hs : ∀ i j, G i j = G j i)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℝ)
    (hx : ∑ i, ∑ j, x i * x j * (G i j : ℝ) = 0) : x = 0 := by
  set M : Matrix (Fin d) (Fin d) ℝ := G.map (Int.castRingHom ℝ) with hM
  have key : ∀ y : Fin d → ℝ, star y ⬝ᵥ M *ᵥ y = ∑ i, ∑ j, y i * y j * (G i j : ℝ) := by
    intro y
    simp only [dotProduct, mulVec, Finset.mul_sum, hM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp; ring
  have hp : M.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
    · ext i j; simp [hM, hs i j]
    · rw [key]; exact real_nonneg G hG y
  have h0 : M *ᵥ x = 0 := (hp.dotProduct_mulVec_zero_iff x).1 (by rw [key, hx])
  by_contra hne
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hne, h0⟩
  rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  exact det_ne_zero G hG (by simpa using this)

/- English proof (translation)
Establish `h` using `congrArg Complex.re hx`. Establish `h1` using `real_nonneg G hG fun i => (x i).re`. Establish `h2` using `real_nonneg G hG fun i => (x i).im`. Establish `h3 : (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (G i j : ℂ)).re = ∑ i, ∑ j, (x i).re * (x j).re * (G i j : ℝ) + ∑ i, ∑ j, (x i).im * (x j).im * (G i j : ℝ)`. Simplify using `only [Complex.re_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[h3, Complex.zero_re]`. Establish `e1` using `real_pos G hs hG (fun i => (x i).re) (by linarith)`.

Establish `e2` using `real_pos G hs hG (fun i => (x i).im) (by linarith)`. Use extensionality with `i`. Conclude with `Complex.ext (congrFun e1 i) (congrFun e2 i)`.
-/
theorem complex_pos {d : ℕ} (G : Matrix (Fin d) (Fin d) ℤ) (hs : ∀ i j, G i j = G j i)
    (hG : ∀ c : Fin d → ℤ, c ≠ 0 → 0 < c ⬝ᵥ G *ᵥ c) (x : Fin d → ℂ)
    (hx : ∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (G i j : ℂ) = 0) : x = 0 := by
  have h := congrArg Complex.re hx
  have h1 := real_nonneg G hG fun i => (x i).re
  have h2 := real_nonneg G hG fun i => (x i).im
  have h3 : (∑ i, ∑ j, x i * (starRingEnd ℂ) (x j) * (G i j : ℂ)).re =
      ∑ i, ∑ j, (x i).re * (x j).re * (G i j : ℝ) + ∑ i, ∑ j, (x i).im * (x j).im * (G i j : ℝ) := by
    simp only [Complex.re_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp; ring
  rw [h3, Complex.zero_re] at h
  have e1 := real_pos G hs hG (fun i => (x i).re) (by linarith)
  have e2 := real_pos G hs hG (fun i => (x i).im) (by linarith)
  ext i
  exact Complex.ext (congrFun e1 i) (congrFun e2 i)

/- English proof (translation)
Establish `h1 : aeval φ (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) e = ∑ i : Fin d, c i • (φ ^ (i : ℕ)) e`. Simplify using `[map_sum, LinearMap.sum_apply, Module.End.intCast_apply]`. Establish `h2 : (∑ i : Fin d, C (c i) * X ^ (i : ℕ) : ℤ[X]) ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises.

Use extensionality with `k`. Use `congrArg (fun p : ℤ[X] => p.coeff k) h` as an intermediate fact. Simplify using `only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj] at this`. Simplify using `using this`. Establish `h3` using `hb _ (hd _ h2 (degree_sum_fin_lt c))`.

Rewrite `h3` using `[h1]`. Use `h3.trans_eq ?_` and prove the remaining obligations. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, dotProduct, mulVec, Finset.mul_sum, Matrix.of_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem gram_pos {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (hb : ∀ x, x ≠ 0 → 0 < b x x) (φ : Module.End ℤ Λ) (e : Λ) (d : ℕ)
    (hd : ∀ P : ℤ[X], P ≠ 0 → P.degree < d → aeval φ P e ≠ 0) (c : Fin d → ℤ) (hc : c ≠ 0) :
    0 < c ⬝ᵥ (Matrix.of fun i j : Fin d => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e)) *ᵥ c := by
  have h1 : aeval φ (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) e = ∑ i : Fin d, c i • (φ ^ (i : ℕ)) e := by
    simp [map_sum, LinearMap.sum_apply, Module.End.intCast_apply]
  have h2 : (∑ i : Fin d, C (c i) * X ^ (i : ℕ) : ℤ[X]) ≠ 0 := by
    intro h
    apply hc
    ext k
    have := congrArg (fun p : ℤ[X] => p.coeff k) h
    simp only [finset_sum_coeff, coeff_C_mul_X_pow, coeff_zero, Fin.val_inj] at this
    simpa using this
  have h3 := hb _ (hd _ h2 (degree_sum_fin_lt c))
  rw [h1] at h3
  refine h3.trans_eq ?_
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, dotProduct, mulVec,
    Finset.mul_sum, Matrix.of_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Use `set G : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ := Matrix.of fun i j => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e) with hG`. Establish `hD : G.det ≠ 0` using `det_ne_zero G (gram_pos b hb φ e (r + 1) fun P hP _ => hne P hP)`. Take `⟨χ, y, hm, hr, hy⟩` from `h G.det.natAbs`.

Use `set n := G.det.natAbs with hn`. Establish `h1 : aeval φ χ e = ∑ i : Fin (r + 1), χ.coeff i • (φ ^ (i : ℕ)) e`. Rewrite using `[aeval_eq_sum_range, hr, Finset.sum_range]`. Simplify using `[LinearMap.sum_apply]`. Establish `h2 : G *ᵥ (fun i => χ.coeff i) = ((l : ℤ) ^ n) • fun i : Fin (r + 1) => b ((φ ^ (i : ℕ)) e) y`.

Use extensionality with `i`. Establish `: b ((φ ^ (i : ℕ)) e) (aeval φ χ e) = (l : ℤ) ^ n * b ((φ ^ (i : ℕ)) e) y`. Rewrite using `[hy, map_nsmul]`. Simplify using the standard rewrite rules. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← this, h1]`.

Simplify using `[mulVec, dotProduct, hG, mul_comm]`. Establish `h3` using `congrArg (fun v => (G.adjugate *ᵥ v) (Fin.last r)) h2`. Simplify using `only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul, Pi.smul_apply, smul_eq_mul, Fin.val_last] at h3`. Establish `hc : χ.coeff r = 1` using `by rw [← hr]; exact hm`. Rewrite `h3` using `[hc, mul_one]`.

Establish `h4 : l ^ n ∣ n`. Establish `: ((l ^ n : ℕ) : ℤ) ∣ G.det` using `⟨_, by push_cast; exact h3⟩`. Conclude with `Int.natCast_dvd.1 this`. Establish `h5` using `Nat.le_of_dvd (Int.natAbs_pos.2 hD) h4`. Conclude with `absurd (Nat.lt_pow_self (n := n) (by omega : 1 < l)) (not_lt.2 h5)`.
-/
theorem exists_ann {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (hb : ∀ x, x ≠ 0 → 0 < b x x) (φ : Module.End ℤ Λ) (e : Λ) (l r : ℕ) (hl : 2 ≤ l)
    (h : ∀ n : ℕ, ∃ (χ : ℤ[X]) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ aeval φ χ e = l ^ n • y) :
    ∃ P : ℤ[X], P ≠ 0 ∧ aeval φ P e = 0 := by
  by_contra hne
  push Not at hne
  set G : Matrix (Fin (r + 1)) (Fin (r + 1)) ℤ :=
    Matrix.of fun i j => b ((φ ^ (i : ℕ)) e) ((φ ^ (j : ℕ)) e) with hG
  have hD : G.det ≠ 0 := det_ne_zero G (gram_pos b hb φ e (r + 1) fun P hP _ => hne P hP)
  obtain ⟨χ, y, hm, hr, hy⟩ := h G.det.natAbs
  set n := G.det.natAbs with hn
  have h1 : aeval φ χ e = ∑ i : Fin (r + 1), χ.coeff i • (φ ^ (i : ℕ)) e := by
    rw [aeval_eq_sum_range, hr, Finset.sum_range]
    simp [LinearMap.sum_apply]
  have h2 : G *ᵥ (fun i => χ.coeff i) = ((l : ℤ) ^ n) • fun i : Fin (r + 1) => b ((φ ^ (i : ℕ)) e) y := by
    ext i
    have : b ((φ ^ (i : ℕ)) e) (aeval φ χ e) = (l : ℤ) ^ n * b ((φ ^ (i : ℕ)) e) y := by
      rw [hy, map_nsmul]; simp
    rw [Pi.smul_apply, smul_eq_mul, ← this, h1]
    simp [mulVec, dotProduct, hG, mul_comm]
  have h3 := congrArg (fun v => (G.adjugate *ᵥ v) (Fin.last r)) h2
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul, Pi.smul_apply,
    smul_eq_mul, Fin.val_last] at h3
  have hc : χ.coeff r = 1 := by rw [← hr]; exact hm
  rw [hc, mul_one] at h3
  have h4 : l ^ n ∣ n := by
    have : ((l ^ n : ℕ) : ℤ) ∣ G.det := ⟨_, by push_cast; exact h3⟩
    exact Int.natCast_dvd.1 this
  have h5 := Nat.le_of_dvd (Int.natAbs_pos.2 hD) h4
  exact absurd (Nat.lt_pow_self (n := n) (by omega : 1 < l)) (not_lt.2 h5)

noncomputable def form (g : ℕ → ℕ → ℤ) : ℂ[X] →ₗ[ℂ] ℂ[X] →ₗ[ℂ] ℂ :=
  (basisMonomials ℂ).constr ℂ fun i => (basisMonomials ℂ).constr ℂ fun j => (g i j : ℂ)

/- English proof (translation)
Establish `h : ∀ k, (X ^ k : ℂ[X]) = basisMonomials ℂ k` using `fun k => by`. Simplify using `[monomial_one_right_eq_X_pow]`. Rewrite using `[form, h, h, Module.Basis.constr_basis, Module.Basis.constr_basis]`.
-/
theorem form_pow (g : ℕ → ℕ → ℤ) (i j : ℕ) : form g (X ^ i) (X ^ j) = g i j := by
  have h : ∀ k, (X ^ k : ℂ[X]) = basisMonomials ℂ k := fun k => by
    simp [monomial_one_right_eq_X_pow]
  rw [form, h, h, Module.Basis.constr_basis, Module.Basis.constr_basis]

/- English proof (translation)
Use `conv_lhs => rw [f.as_sum_range' d hf, h.as_sum_range' d hh]`. Simplify using `only [Finset.sum_range, ← smul_X_eq_monomial, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, form_pow, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem form_sum (g : ℕ → ℕ → ℤ) (d : ℕ) (f h : ℂ[X]) (hf : f.natDegree < d) (hh : h.natDegree < d) :
    form g f h = ∑ i : Fin d, ∑ j : Fin d, f.coeff i * h.coeff j * (g i j : ℂ) := by
  conv_lhs => rw [f.as_sum_range' d hf, h.as_sum_range' d hh]
  simp only [Finset.sum_range, ← smul_X_eq_monomial, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, form_pow, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [mul_add, hp, hq]`. Consider the case `monomial i a`. Proceed by induction on `h using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [mul_add, map_add, hp, hq]`.

Consider the case `monomial j c`. Simplify using `only [← smul_X_eq_monomial, mul_smul_comm, ← pow_succ', map_smul, LinearMap.smul_apply, form_pow, hg, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_shift (g : ℕ → ℕ → ℤ) (q : ℤ) (hg : ∀ i j, g (i + 1) (j + 1) = q * g i j)
    (f h : ℂ[X]) : form g (X * f) (X * h) = q * form g f h := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial i a =>
    induction h using Polynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq]
    | monomial j c =>
      simp only [← smul_X_eq_monomial, mul_smul_comm, ← pow_succ', map_smul, LinearMap.smul_apply,
        form_pow, hg, smul_eq_mul]
      push_cast; ring

/- English proof (translation)
Use `set d := max f.natDegree h.natDegree + 1`. Rewrite using `[form_sum g d f h (by omega) (by omega), form_sum g d h f (by omega) (by omega), Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hg]; ring` and prove the remaining obligations.
-/
theorem form_symm (g : ℕ → ℕ → ℤ) (hg : ∀ i j, g i j = g j i)
    (f h : ℂ[X]) : form g f h = form g h f := by
  set d := max f.natDegree h.natDegree + 1
  rw [form_sum g d f h (by omega) (by omega), form_sum g d h f (by omega) (by omega),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hg]; ring

/- English proof (translation)
Establish `key : ∀ (P : ℤ[X]) (j : ℕ), form (fun i j => b ((φ ^ i) e) ((φ ^ j) e)) (P.map (Int.castRingHom ℂ)) (X ^ j) = (b (aeval φ P e) ((φ ^ j) e) : ℤ)`. Introduce `P j`. Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `monomial i a`.

Rewrite using `[Polynomial.map_monomial, ← smul_X_eq_monomial, ← smul_X_eq_monomial]`. Simplify using `only [map_smul, LinearMap.smul_apply, form_pow, map_pow, aeval_X, smul_eq_mul]`. Simplify using the standard rewrite rules. Proceed by induction on `h using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp [hp, hq]`.

Consider the case `monomial j c => rw [← smul_X_eq_monomial, map_smul, key, hP]`. Simplify using the standard rewrite rules.
-/
theorem form_ann {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (φ : Module.End ℤ Λ) (e : Λ) (P : ℤ[X]) (hP : aeval φ P e = 0) (h : ℂ[X]) :
    form (fun i j => b ((φ ^ i) e) ((φ ^ j) e)) (P.map (Int.castRingHom ℂ)) h = 0 := by
  have key : ∀ (P : ℤ[X]) (j : ℕ), form (fun i j => b ((φ ^ i) e) ((φ ^ j) e))
      (P.map (Int.castRingHom ℂ)) (X ^ j) = (b (aeval φ P e) ((φ ^ j) e) : ℤ) := by
    intro P j
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial i a =>
      rw [Polynomial.map_monomial, ← smul_X_eq_monomial, ← smul_X_eq_monomial]
      simp only [map_smul, LinearMap.smul_apply, form_pow, map_pow, aeval_X, smul_eq_mul]
      simp
  induction h using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial j c => rw [← smul_X_eq_monomial, map_smul, key, hP]; simp

/- English proof (translation)
Introduce `Λ _ Q φ e q l r hl hpar h0 hdef hφ hχ`. Take `⟨b, hb, hbb⟩` from `exists_polar Q hpar`. Establish `hpos : ∀ x, x ≠ 0 → 0 < b x x`. Introduce `x hx`. Use `h0 x` as an intermediate fact.

Establish `h' : Q x ≠ 0` using `fun h => hx (hdef x h)`. Rewrite using `[hbb]`. Use linear arithmetic over natural numbers and integers. Take `⟨P₀, hP₀, hP₀'⟩` from `exists_ann b hpos φ e l r hl hχ`. Establish `hex : ∃ d : ℕ, ∃ P : ℤ[X], P ≠ 0 ∧ aeval φ P e = 0 ∧ P.natDegree = d` using `⟨_, P₀, hP₀, hP₀', rfl⟩`.

Take `⟨P, hP, hPe, hPd⟩` from `Nat.find_spec hex`. Use `set d := Nat.find hex with hd`. Establish `hmin : ∀ R : ℤ[X], R ≠ 0 → R.degree < d → aeval φ R e ≠ 0`. Introduce `R hR hRd hRe`. Conclude with `Nat.find_min hex ((natDegree_lt_iff_degree_lt hR).2 hRd) ⟨R, hR, hRe, rfl⟩`.

Use `⟨P, hP, hPe, fun β hβ => ?_⟩` and prove the remaining obligations. Use `set g : ℕ → ℕ → ℤ := fun i j => b ((φ ^ i) e) ((φ ^ j) e) with hg`. Establish `hsymm : ∀ i j, g i j = g j i`. Introduce `i j`. Simplify using `only [hg, hb]`.

Rewrite using `[add_comm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hshift : ∀ i j, g (i + 1) (j + 1) = (q : ℤ) * g i j`. Introduce `i j`. Simplify using `only [hg, hb, pow_succ', Module.End.mul_apply, ← map_add, hφ]`.

Expand and normalize the polynomial expressions, which then agree. Use `set Pc := P.map (Int.castRingHom ℂ) with hPc`. Establish `hinj : Function.Injective (Int.castRingHom ℂ)` using `Int.cast_injective`. Establish `hPc0 : Pc ≠ 0` using `(Polynomial.map_ne_zero_iff hinj).2 hP`. Establish `hPcd : Pc.natDegree = d` using `by rw [hPc, natDegree_map_eq_of_injective hinj, hPd]`.

Establish `hroot : Pc.IsRoot β`. Rewrite using `[IsRoot, hPc, eval_map]`. Conclude with `hβ`. Take `⟨f, hf⟩` from `dvd_iff_isRoot.2 hroot`. Establish `hf0 : f ≠ 0` using `by rintro rfl; simp [hf] at hPc0`.

Establish `hfd : f.natDegree < d`. Rewrite using `[← hPcd, hf, natDegree_mul (X_sub_C_ne_zero β) hf0, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Use `set f' := f.map (starRingEnd ℂ) with hf'`. Establish `hf'd : f'.natDegree < d` using `lt_of_le_of_lt natDegree_map_le hfd`.

Establish `hconj : Pc = (X - C ((starRingEnd ℂ) β)) * f'`. Establish `: Pc.map (starRingEnd ℂ) = Pc`. Rewrite using `[hPc, Polynomial.map_map]`. Use `congr 1`. Conclude with `RingHom.ext_int _ _`.

Rewrite using `[← this, hf]`. Simplify using `[hf']`. Establish `e1 : X * f = β • f + Pc` using `by rw [hf, smul_eq_C_mul]; ring`. Establish `e2 : X * f' = (starRingEnd ℂ) β • f' + Pc` using `by rw [hconj, smul_eq_C_mul]; ring`. Establish `a1 : ∀ h, form g Pc h = 0` using `form_ann b φ e P hPe`.

Establish `a2 : ∀ h, form g h Pc = 0` using `fun h => by rw [form_symm g hsymm, a1]`. Establish `main` using `form_shift g q hshift f f'`. Rewrite `main` using `[e1, e2]`. Simplify using `only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, a1, a2, add_zero, smul_eq_mul, mul_zero] at main`. Establish `hne : form g f f' ≠ 0`.

Introduce `hz`. Rewrite `hz` using `[form_sum g d f f' hfd hf'd]`. Use `complex_pos (Matrix.of fun i j : Fin d => g i j) (fun i j => hsymm i j) (gram_pos b hpos φ e d hmin) (fun i => f.coeff i) (by simpa [hf'] using hz)` as an intermediate fact. Conclude with `hf0 (leadingCoeff_eq_zero.1 (congrFun this ⟨f.natDegree, hfd⟩))`. Establish `: ((Complex.normSq β : ℝ) : ℂ) = (q : ℂ)`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Move the coercions through the operations in `at main`. Take the linear combination `main`. Conclude with `this` after adjusting the coercions.
-/
theorem similitude_algebraic : ∀ (Λ : Type) [AddCommGroup Λ] (Q : Λ → ℤ) (φ : Module.End ℤ Λ) (e : Λ) (q l r : ℕ), 2 ≤ l → (∀ x y, Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y) → (∀ x, 0 ≤ Q x) → (∀ x, Q x = 0 → x = 0) → (∀ x, Q (φ x) = q * Q x) → (∀ n : ℕ, ∃ (χ : Polynomial ℤ) (y : Λ), χ.Monic ∧ χ.natDegree = r ∧ Polynomial.aeval φ χ e = l ^ n • y) → ∃ P : Polynomial ℤ, P ≠ 0 ∧ Polynomial.aeval φ P e = 0 ∧ ∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q := by
  classical
  intro Λ _ Q φ e q l r hl hpar h0 hdef hφ hχ
  obtain ⟨b, hb, hbb⟩ := exists_polar Q hpar
  have hpos : ∀ x, x ≠ 0 → 0 < b x x := by
    intro x hx
    have := h0 x
    have h' : Q x ≠ 0 := fun h => hx (hdef x h)
    rw [hbb]; omega
  obtain ⟨P₀, hP₀, hP₀'⟩ := exists_ann b hpos φ e l r hl hχ
  have hex : ∃ d : ℕ, ∃ P : ℤ[X], P ≠ 0 ∧ aeval φ P e = 0 ∧ P.natDegree = d := ⟨_, P₀, hP₀, hP₀', rfl⟩
  obtain ⟨P, hP, hPe, hPd⟩ := Nat.find_spec hex
  set d := Nat.find hex with hd
  have hmin : ∀ R : ℤ[X], R ≠ 0 → R.degree < d → aeval φ R e ≠ 0 := by
    intro R hR hRd hRe
    exact Nat.find_min hex ((natDegree_lt_iff_degree_lt hR).2 hRd) ⟨R, hR, hRe, rfl⟩
  refine ⟨P, hP, hPe, fun β hβ => ?_⟩
  set g : ℕ → ℕ → ℤ := fun i j => b ((φ ^ i) e) ((φ ^ j) e) with hg
  have hsymm : ∀ i j, g i j = g j i := by
    intro i j; simp only [hg, hb]; rw [add_comm]; ring
  have hshift : ∀ i j, g (i + 1) (j + 1) = (q : ℤ) * g i j := by
    intro i j
    simp only [hg, hb, pow_succ', Module.End.mul_apply, ← map_add, hφ]; ring
  set Pc := P.map (Int.castRingHom ℂ) with hPc
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hPc0 : Pc ≠ 0 := (Polynomial.map_ne_zero_iff hinj).2 hP
  have hPcd : Pc.natDegree = d := by rw [hPc, natDegree_map_eq_of_injective hinj, hPd]
  have hroot : Pc.IsRoot β := by
    rw [IsRoot, hPc, eval_map]; exact hβ
  obtain ⟨f, hf⟩ := dvd_iff_isRoot.2 hroot
  have hf0 : f ≠ 0 := by rintro rfl; simp [hf] at hPc0
  have hfd : f.natDegree < d := by
    rw [← hPcd, hf, natDegree_mul (X_sub_C_ne_zero β) hf0, natDegree_X_sub_C]; omega
  set f' := f.map (starRingEnd ℂ) with hf'
  have hf'd : f'.natDegree < d := lt_of_le_of_lt natDegree_map_le hfd
  have hconj : Pc = (X - C ((starRingEnd ℂ) β)) * f' := by
    have : Pc.map (starRingEnd ℂ) = Pc := by
      rw [hPc, Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _
    rw [← this, hf]; simp [hf']
  have e1 : X * f = β • f + Pc := by rw [hf, smul_eq_C_mul]; ring
  have e2 : X * f' = (starRingEnd ℂ) β • f' + Pc := by rw [hconj, smul_eq_C_mul]; ring
  have a1 : ∀ h, form g Pc h = 0 := form_ann b φ e P hPe
  have a2 : ∀ h, form g h Pc = 0 := fun h => by rw [form_symm g hsymm, a1]
  have main := form_shift g q hshift f f'
  rw [e1, e2] at main
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, a1, a2, add_zero,
    smul_eq_mul, mul_zero] at main
  have hne : form g f f' ≠ 0 := by
    intro hz
    rw [form_sum g d f f' hfd hf'd] at hz
    have := complex_pos (Matrix.of fun i j : Fin d => g i j) (fun i j => hsymm i j)
      (gram_pos b hpos φ e d hmin) (fun i => f.coeff i) (by simpa [hf'] using hz)
    exact hf0 (leadingCoeff_eq_zero.1 (congrFun this ⟨f.natDegree, hfd⟩))
  have : ((Complex.normSq β : ℝ) : ℂ) = (q : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    apply mul_right_cancel₀ hne
    push_cast at main
    linear_combination main
  exact_mod_cast this

end GlobalTheory.SimAlg
