import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta

variable (D : D7) (T : Tor D) {N N' : ℕ}

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]`.
-/
theorem Hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]`.
-/
theorem Hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

/- English proof (translation)
Simplify using `only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]`.
-/
theorem Hf_smul_left (c : ℂ) (x y : VC D N N') : Hf D T (c • x) y = c * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

/- English proof (translation)
Simplify using `only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]`.
-/
theorem Hf_conj (x y : VC D N N') : (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

/- English proof (translation)
Rewrite using `[← Hf_conj D T (c • y) x, Hf_smul_left, map_mul, Hf_conj]`.
-/
theorem Hf_smul_right (c : ℂ) (x y : VC D N N') : Hf D T x (c • y) = (starRingEnd ℂ) c * Hf D T x y := by
  rw [← Hf_conj D T (c • y) x, Hf_smul_left, map_mul, Hf_conj]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem Hf_zero_left (y : VC D N N') : Hf D T 0 y = 0 := by simp [Hf]

/- English proof (translation)
Simplify using `[Hf]`.
-/
theorem Hf_zero_right (y : VC D N N') : Hf D T y 0 = 0 := by simp [Hf]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]`.
-/
theorem Hf_nsmul_left (n : ℕ) (x y : VC D N N') : Hf D T (n • x) y = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_left]

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_right, Complex.conj_natCast]`.
-/
theorem Hf_nsmul_right (n : ℕ) (x y : VC D N N') : Hf D T x (n • y) = n * Hf D T x y := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, Hf_smul_right, Complex.conj_natCast]

/- English proof (translation)
Rewrite using `[← Hf_conj D T x y, Complex.conj_im]`.
-/
theorem Hf_im_swap (x y : VC D N N') : (Hf D T y x).im = -(Hf D T x y).im := by
  rw [← Hf_conj D T x y, Complex.conj_im]

/- English proof (translation)
Rewrite using `[← Hf_conj D T x y, Complex.conj_re]`.
-/
theorem Hf_re_swap (x y : VC D N N') : (Hf D T y x).re = (Hf D T x y).re := by
  rw [← Hf_conj D T x y, Complex.conj_re]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `[U, Hf_zero_right]`.
-/
theorem U_zero (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf_zero_right]

/- English proof (translation)
Establish `h : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ)`. Rewrite using `[← Hf_conj D T x y]`. Apply the tactic sequence `apply Complex.ext <;> simp`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [U, Hf_add_left, Hf_add_right, add_assoc]`.

Rewrite using `[h, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem U_U (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ)) * U D T (x + y) G z := by
  have h : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← Hf_conj D T x y]
    apply Complex.ext <;> simp
    ring
  simp only [U, Hf_add_left, Hf_add_right, add_assoc]
  rw [h, mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

/- English proof (translation)
Simplify using `only [U, mul_assoc]`.
-/
theorem U_mul (x : VC D N N') (a : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => a * G w) z = a * U D T x G z := by
  simp only [U, mul_assoc]

/- English proof (translation)
Simplify using `only [U, Finset.sum_mul]`.
-/
theorem U_sum {ι : Type*} (s : Finset ι) (x : VC D N N') (G : ι → VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => ∑ i ∈ s, G i w) z = ∑ i ∈ s, U D T x (G i) z := by
  simp only [U, Finset.sum_mul]

/- English proof (translation)
Unfold `Hf`. Use `fun_prop`.
-/
theorem differentiable_Hf (x : VC D N N') : Differentiable ℂ (fun z : VC D N N' => Hf D T z x) := by
  unfold Hf
  fun_prop

/- English proof (translation)
Establish `h` using `differentiable_Hf D T x`. Unfold `U`. Use `fun_prop`.
-/
theorem differentiable_U (x : VC D N N') {G : VC D N N' → ℂ} (hG : Differentiable ℂ G) :
    Differentiable ℂ (U D T x G) := by
  have h := differentiable_Hf D T x
  unfold U
  fun_prop

/- English proof (translation)
Establish `h` using `fun i => differentiable_U D T (t i) hG`. Unfold `comb`. Use `fun_prop`.
-/
theorem differentiable_comb {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (comb D T c t G) := by
  have h := fun i => differentiable_U D T (t i) hG
  unfold comb
  fun_prop

def pad (m : ℕ) (z : VC D N N') : VC D (N + m) N' := fun τ a => Fin.append (z τ a) (0 : Fin m → ℂ)

def padM (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) : Matrix (Fin N') (Fin (N + m)) D.host.E :=
  fun a => Fin.append (A a) (0 : Fin m → D.host.E)

/- English proof (translation)
Simplify using `[pad]`.
-/
@[simp] theorem pad_left (m : ℕ) (z : VC D N N') (τ a) (i : Fin N) : pad D m z τ a (Fin.castAdd m i) = z τ a i := by
  simp [pad]

/- English proof (translation)
Simplify using `[pad]`.
-/
@[simp] theorem pad_right (m : ℕ) (z : VC D N N') (τ a) (i : Fin m) : pad D m z τ a (Fin.natAdd N i) = 0 := by
  simp [pad]

def padL (m : ℕ) : VC D N N' →ₗ[ℂ] VC D (N + m) N' where
  toFun := pad D m
  map_add' x y := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  map_smul' c x := by
    funext τ a i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem padL_apply (m : ℕ) (z : VC D N N') : padL D m z = pad D m z := rfl

/- English proof (translation)
The claim follows from `(padL D m).map_add x y`.
-/
theorem pad_add (m : ℕ) (x y : VC D N N') : pad D m (x + y) = pad D m x + pad D m y := (padL D m).map_add x y

/- English proof (translation)
The claim follows from `(padL D m).map_smul c x`.
-/
theorem pad_smul (m : ℕ) (c : ℂ) (x : VC D N N') : pad D m (c • x) = c • pad D m x := (padL D m).map_smul c x

/- English proof (translation)
The claim follows from `map_nsmul (padL D m) n x`.
-/
theorem pad_nsmul (m n : ℕ) (x : VC D N N') : pad D m (n • x) = n • pad D m x := map_nsmul (padL D m) n x

/- English proof (translation)
The claim follows from `(padL D m).map_zero`.
-/
theorem pad_zero (m : ℕ) : pad D m (0 : VC D N N') = 0 := (padL D m).map_zero

/- English proof (translation)
The claim follows from `map_sum (padL D m) x s`.
-/
theorem pad_sum {ι : Type*} (s : Finset ι) (m : ℕ) (x : ι → VC D N N') :
    pad D m (∑ i ∈ s, x i) = ∑ i ∈ s, pad D m (x i) := map_sum (padL D m) x s

/- English proof (translation)
The claim follows from `(LinearMap.toContinuousLinearMap (padL D m)).differentiable`.
-/
theorem differentiable_pad (m : ℕ) : Differentiable ℂ (pad D m : VC D N N' → VC D (N + m) N') :=
  (LinearMap.toContinuousLinearMap (padL D m)).differentiable

/- English proof (translation)
Use function extensionality and compare the values at `τ a i`. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [embV, padM, h0]`.
-/
theorem pad_embV (h0 : ∀ τ, T.emb τ 0 = 0) (m : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    pad D m (embV D T A) = embV D T (padM D m A) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [embV, padM, h0]

/- English proof (translation)
Simplify using `[Hf, Fin.sum_univ_add]`.
-/
theorem Hf_pad (m : ℕ) (x y : VC D N N') : Hf D T (pad D m x) (pad D m y) = Hf D T x y := by
  simp [Hf, Fin.sum_univ_add]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [U, Hf_pad, pad_add]`.
-/
theorem U_pad (m : ℕ) (x : VC D N N') (G : VC D (N + m) N' → ℂ) :
    U D T x (fun z => G (pad D m z)) = fun z => U D T (pad D m x) G (pad D m z) := by
  funext z
  simp only [U, Hf_pad, pad_add]

/- English proof (translation)
Simplify using `only [wdPh, qH, Hf_pad]`.
-/
theorem wdPh_pad (m : ℕ) (x : VC D N N') : wdPh D T (pad D m x) = wdPh D T x := by
  simp only [wdPh, qH, Hf_pad]

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [comb, U_pad]`.
-/
theorem comb_pad (m : ℕ) {k : ℕ} (c : Fin k → ℂ) (t : Fin k → VC D N N') (G : VC D (N + m) N' → ℂ) :
    comb D T c t (fun z => G (pad D m z)) = fun z => comb D T c (fun i => pad D m (t i)) G (pad D m z) := by
  funext z
  simp only [comb, U_pad]

def IsTr (A : AddSubgroup (VC D N N')) (F G : VC D N N' → ℂ) : Prop :=
  ∃ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (m : ℕ), 0 < m ∧ (∀ i, m • t i ∈ A) ∧ G = comb D T c t F

/- English proof (translation)
Take `⟨k, c, t, m, hm, ht, rfl⟩` from `h₁`. Take `⟨k', c', t', m', hm', ht', rfl⟩` from `h₂`. Use `⟨k' * k, fun p => c' (finProdFinEquiv.symm p).1 * c (finProdFinEquiv.symm p).2 * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T (t' (finProdFinEquiv.symm p).1) (t (finProdFinEquiv.symm p).2)).im : ℂ)), fun p => t' (finProdFinEquiv.symm p).1 + t (finProdFinEquiv.symm p).2, m * …` and prove the remaining obligations. Introduce `p`. Rewrite using `[smul_add]`.

Use `A.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `A.nsmul_mem (ht' _) _`. Rewrite using `[mul_comm, mul_smul]`. Conclude with `A.nsmul_mem (ht _) _`.

Use function extensionality and compare the values at `z`. Establish `h : ∀ i, U D T (t' i) (comb D T c t F) z = ∑ j, c j * U D T (t' i) (U D T (t j) F) z`. Introduce `i`. Use `U_sum D T Finset.univ (t' i) (fun j w => c j * U D T (t j) F w) z` as an intermediate fact. Simplify using `only [U_mul] at this`.

Conclude with `this`. Establish `e : comb D T c' t' (comb D T c t F) z = ∑ i, c' i * U D T (t' i) (comb D T c t F) z` using `rfl`. Rewrite using `[e]`. Simplify using `only [h, U_U]`. Unfold `comb`.

Rewrite using `[← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]`. Simplify using `only [Equiv.symm_apply_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsTr.trans {A : AddSubgroup (VC D N N')} {F G H : VC D N N' → ℂ} (h₁ : IsTr D T A F G)
    (h₂ : IsTr D T A G H) : IsTr D T A F H := by
  obtain ⟨k, c, t, m, hm, ht, rfl⟩ := h₁
  obtain ⟨k', c', t', m', hm', ht', rfl⟩ := h₂
  refine ⟨k' * k, fun p => c' (finProdFinEquiv.symm p).1 * c (finProdFinEquiv.symm p).2 *
      Complex.exp (-(Real.pi : ℂ) * Complex.I *
        ((Hf D T (t' (finProdFinEquiv.symm p).1) (t (finProdFinEquiv.symm p).2)).im : ℂ)),
    fun p => t' (finProdFinEquiv.symm p).1 + t (finProdFinEquiv.symm p).2, m * m', Nat.mul_pos hm hm', ?_, ?_⟩
  · intro p
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_smul]; exact A.nsmul_mem (ht' _) _
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem (ht _) _
  · funext z
    have h : ∀ i, U D T (t' i) (comb D T c t F) z = ∑ j, c j * U D T (t' i) (U D T (t j) F) z := by
      intro i
      have := U_sum D T Finset.univ (t' i) (fun j w => c j * U D T (t j) F w) z
      simp only [U_mul] at this
      exact this
    have e : comb D T c' t' (comb D T c t F) z = ∑ i, c' i * U D T (t' i) (comb D T c t F) z := rfl
    rw [e]
    simp only [h, U_U]
    unfold comb
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun _ => a, fun _ => t, m, hm, fun _ => ht, by funext z; simp [comb]⟩`.
-/
theorem IsTr.single {A : AddSubgroup (VC D N N')} (F : VC D N N' → ℂ) (a : ℂ) (t : VC D N N') (m : ℕ)
    (hm : 0 < m) (ht : m • t ∈ A) : IsTr D T A F (fun z => a * U D T t F z) :=
  ⟨1, fun _ => a, fun _ => t, m, hm, fun _ => ht, by funext z; simp [comb]⟩

/- English proof (translation)
Take `⟨k, c, t, n, hn, ht, rfl⟩` from `h`. Use `⟨_, ⟨k, c, fun i => GalTheta.pad D m (t i), R * n, Nat.mul_pos hR hn, fun i => ?_, rfl⟩, comb_pad D T m c t F⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← pad_nsmul]`. Conclude with `hAB _ (ht i)`.
-/
theorem IsTr.pad {A : AddSubgroup (VC D N N')} {m : ℕ} {B : AddSubgroup (VC D (N + m) N')} {R : ℕ} (hR : 0 < R)
    (hAB : ∀ y ∈ A, R • pad D m y ∈ B) {F : VC D (N + m) N' → ℂ} {G : VC D N N' → ℂ}
    (h : IsTr D T A (fun z => F (pad D m z)) G) :
    ∃ G₁, IsTr D T B F G₁ ∧ G = fun z => G₁ (pad D m z) := by
  obtain ⟨k, c, t, n, hn, ht, rfl⟩ := h
  refine ⟨_, ⟨k, c, fun i => GalTheta.pad D m (t i), R * n, Nat.mul_pos hR hn, fun i => ?_, rfl⟩, comb_pad D T m c t F⟩
  rw [mul_smul, ← pad_nsmul]
  exact hAB _ (ht i)

end GlobalTheory.GalTheta
