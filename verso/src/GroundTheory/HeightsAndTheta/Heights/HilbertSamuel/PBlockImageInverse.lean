import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageInverse

section Forms

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.mp (support_add hm) with h | h` into its components or cases. Conclude with `hf m h`. Conclude with `hg m h`.
-/
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h
  · exact hg m h

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[support_neg]`. Conclude with `hf m hm`.
-/
theorem isMultiHomog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `isMultiHomog_add hf (isMultiHomog_neg hg)`.
-/
theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  exact isMultiHomog_add hf (isMultiHomog_neg hg)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_zero a`. Consider the case `insert t s ht ih`. Rewrite using `[Finset.sum_insert ht]`. Conclude with `isMultiHomog_add (hf t (Finset.mem_insert_self _ _)) (ih fun t' h => hf t' (Finset.mem_insert_of_mem h))`.
-/
theorem isMultiHomog_sum {α : Type*} (s : Finset α) {f : α → MRing ι} {a : K → ℕ}
    (hf : ∀ t ∈ s, IsMultiHomog (f t) a) : IsMultiHomog (∑ t ∈ s, f t) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_zero a
  | insert t s ht ih =>
    rw [Finset.sum_insert ht]
    exact isMultiHomog_add (hf t (Finset.mem_insert_self _ _))
      (ih fun t' h => hf t' (Finset.mem_insert_of_mem h))

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.mp (support_mul f g hm)`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]`.
-/
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m₁ h₁ k, hg m₂ h₂ k]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_one, Finset.mem_singleton]`. Simplify using `[hm]`.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [support_one, Finset.mem_singleton] at hm
  simp [hm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_one`. Consider the case `insert t s ht ih`. Rewrite using `[Finset.prod_insert ht, Finset.sum_insert ht]`. Conclude with `isMultiHomog_mul (hf t (Finset.mem_insert_self _ _)) (ih fun t' h => hf t' (Finset.mem_insert_of_mem h))`.
-/
theorem isMultiHomog_prod {α : Type*} (s : Finset α) {f : α → MRing ι} {a : α → K → ℕ}
    (hf : ∀ t ∈ s, IsMultiHomog (f t) (a t)) : IsMultiHomog (∏ t ∈ s, f t) (∑ t ∈ s, a t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMultiHomog_one
  | insert t s ht ih =>
    rw [Finset.prod_insert ht, Finset.sum_insert ht]
    exact isMultiHomog_mul (hf t (Finset.mem_insert_self _ _))
      (ih fun t' h => hf t' (Finset.mem_insert_of_mem h))

/- English proof (translation)
Use `isMultiHomog_prod (Finset.range n) (f := fun _ => f) (a := fun _ => a) (fun _ _ => hf)` as an intermediate fact. Simplify using `using this`.
-/
theorem isMultiHomog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  have := isMultiHomog_prod (Finset.range n) (f := fun _ => f) (a := fun _ => a) (fun _ _ => hf)
  simpa using this

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[C_mul']`. Conclude with `hf m (support_smul hm)`.
-/
theorem isMultiHomog_C_mul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : ℤ) :
    IsMultiHomog (C c * f) a := by
  intro m hm
  rw [C_mul'] at hm
  exact hf m (support_smul hm)

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Take `⟨k', i'⟩` from `p`. Distinguish the cases in `hk : k = k'`.

Substitute `hk` using the available equality. Rewrite using `[Finset.sum_eq_single i']`. Simplify using `[blockDeg]`. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hb (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm`. Simplify using the standard rewrite rules. Simplify using `only [blockDeg, if_neg hk]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`. Conclude with `hk (congrArg Sigma.fst h).symm`.
-/
theorem isMultiHomog_X' [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (blockDeg p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k', i'⟩ := p
  by_cases hk : k = k'
  · subst hk
    rw [Finset.sum_eq_single i']
    · simp [blockDeg]
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hb (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · simp only [blockDeg, if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

/- English proof (translation)
Rewrite using `[bind₁, aeval_def, eval₂_eq']`. Use `isMultiHomog_sum _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.algebraMap_eq]`. Establish `hsum : ∑ k, a k • δ k = ∑ p : (Σ k, ι k), m p • δ p.1`. Rewrite using `[Fintype.sum_sigma]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hf m hm k, Finset.sum_smul]`. Rewrite using `[hsum]`. Conclude with `isMultiHomog_C_mul (isMultiHomog_prod _ fun p _ => isMultiHomog_pow (hτ p) _) _`.
-/
theorem isMultiHomog_bind₁ {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (τ : (Σ k, ι k) → MRing ι') (δ : K → K' → ℕ)
    (hτ : ∀ p, IsMultiHomog (τ p) (δ p.1)) : IsMultiHomog (bind₁ τ f) (∑ k, a k • δ k) := by
  rw [bind₁, aeval_def, eval₂_eq']
  refine isMultiHomog_sum _ fun m hm => ?_
  rw [MvPolynomial.algebraMap_eq]
  have hsum : ∑ k, a k • δ k = ∑ p : (Σ k, ι k), m p • δ p.1 := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hf m hm k, Finset.sum_smul]
  rw [hsum]
  exact isMultiHomog_C_mul (isMultiHomog_prod _ fun p _ => isMultiHomog_pow (hτ p) _) _

/- English proof (translation)
Use `isMultiHomog_mul hf hg` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [blockDeg, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isMultiHomog_blockDeg_mul [DecidableEq K] {k₀ : K} {f g : MRing ι} {n m : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) (hg : IsMultiHomog g (blockDeg k₀ m)) :
    IsMultiHomog (f * g) (blockDeg k₀ (n + m)) := by
  have := isMultiHomog_mul hf hg
  convert this using 1
  funext k
  simp only [blockDeg, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `isMultiHomog_prod s hf` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `only [blockDeg, Finset.sum_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isMultiHomog_blockDeg_prod [DecidableEq K] {k₀ : K} {α : Type*} (s : Finset α) {f : α → MRing ι}
    {n : α → ℕ} (hf : ∀ t ∈ s, IsMultiHomog (f t) (blockDeg k₀ (n t))) :
    IsMultiHomog (∏ t ∈ s, f t) (blockDeg k₀ (∑ t ∈ s, n t)) := by
  have := isMultiHomog_prod s hf
  convert this using 1
  funext k
  simp only [blockDeg, Finset.sum_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hprod : ∏ p, (c p.1 * v p) ^ d p = (∏ k, c k ^ a k) * ∏ p, v p ^ d p`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf d hd k]`. Rewrite using `[hprod]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul {S : Type*} [CommRing S] [Algebra ℤ S] {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → S)
    (v : (Σ k, ι k) → S) : aeval (fun p => c p.1 * v p) f = (∏ k, c k ^ a k) * aeval v f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * v p) ^ d p = (∏ k, c k ^ a k) * ∏ p, v p ^ d p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  rw [hprod]
  ring

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq']`. Use `Finset.sum_congr rfl fun d hd => congrArg _ (Finset.prod_congr rfl fun p _ => ?_)` and prove the remaining obligations. Take `⟨k, i⟩` from `p`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Rewrite using `[hvw]`. Establish `h0 : d ⟨k, i⟩ = 0`. Use `hh d hd k` as an intermediate fact. Simplify using `only [blockDeg, if_neg hk] at this`. Conclude with `(Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ _)`.

Rewrite using `[h0, pow_zero, pow_zero]`.
-/
theorem aeval_congr_block [DecidableEq K] {S : Type*} [CommRing S] [Algebra ℤ S] {h : MRing ι} {k₀ : K} {n : ℕ}
    (hh : IsMultiHomog h (blockDeg k₀ n)) {v w : (Σ k, ι k) → S} (hvw : ∀ i, v ⟨k₀, i⟩ = w ⟨k₀, i⟩) :
    aeval v h = aeval w h := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq']
  refine Finset.sum_congr rfl fun d hd => congrArg _ (Finset.prod_congr rfl fun p _ => ?_)
  obtain ⟨k, i⟩ := p
  by_cases hk : k = k₀
  · subst hk
    rw [hvw]
  · have h0 : d ⟨k, i⟩ = 0 := by
      have := hh d hd k
      simp only [blockDeg, if_neg hk] at this
      exact (Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ _)
    rw [h0, pow_zero, pow_zero]

/- English proof (translation)
Rewrite using `[eval_map, aeval_def, algebraMap_int_eq]`.
-/
theorem eval_map_int {σ : Type*} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h1 : mConeMap y f = aeval (fun p => (X p.1 : MvPolynomial K Ω) * C (y p)) f`. Rewrite using `[mConeMap]`. Conclude with `congrArg (fun φ => aeval φ f) (funext fun p => mul_comm _ _)`. Rewrite using `[h1, aeval_smul hf (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))]`. Establish `h2 : aeval (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f)` using `aeval_C_comp_left y f`.

Rewrite using `[h2]`.
-/
theorem mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    mConeMap y f = (∏ k, (X k : MvPolynomial K Ω) ^ a k) * C (aeval y f) := by
  have h1 : mConeMap y f = aeval (fun p => (X p.1 : MvPolynomial K Ω) * C (y p)) f := by
    rw [mConeMap]
    exact congrArg (fun φ => aeval φ f) (funext fun p => mul_comm _ _)
  rw [h1, aeval_smul hf (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))]
  have h2 : aeval (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f) := aeval_C_comp_left y f
  rw [h2]

/- English proof (translation)
Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Rewrite using `[mConeMap_of_isMultiHomog y hf]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `mul_eq_zero.mp h with h | h` into its components or cases.

Conclude with `absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))`. Conclude with `(C_injective _ _) (h.trans C_0.symm)`. Introduce `h`. Rewrite using `[h, C_0, mul_zero]`.
-/
theorem mem_mCoordIdeal_iff (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    f ∈ mCoordIdeal y ↔ aeval y f = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker]
  rw [mConeMap_of_isMultiHomog y hf]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))
    · exact (C_injective _ _) (h.trans C_0.symm)
  · intro h
    rw [h, C_0, mul_zero]

/- English proof (translation)
Establish `h1 : (fun i => Polynomial.C (x i) * Polynomial.X) = fun p : Ix (Fin r) => (fun _ : Unit => (Polynomial.X : Polynomial Ω)) p.1 * Polynomial.C (x p)`. Use function extensionality and compare the values at `p`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, aeval_smul hF (fun _ => (Polynomial.X : Polynomial Ω)) (fun p => Polynomial.C (x p))]`. Simplify using `only [Finset.univ_unique, Finset.prod_singleton]`.

Establish `h2 : aeval (fun p => Polynomial.C (x p)) F = Polynomial.C (aeval x F)`. Rewrite using `[← Polynomial.algebraMap_eq]`. Conclude with `aeval_algebraMap_apply (B := Polynomial Ω) x F`. Rewrite using `[h2]`.
-/
theorem coneMap_of_isMultiHomog {r : ℕ} (x : Ix (Fin r) → Ω) {F : MRing (GlobalTheory (Fin r))} {e : ℕ}
    (hF : IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e)) :
    aeval (fun i => Polynomial.C (x i) * Polynomial.X) F = Polynomial.X ^ e * Polynomial.C (aeval x F) := by
  have h1 : (fun i => Polynomial.C (x i) * Polynomial.X) =
      fun p : Ix (Fin r) => (fun _ : Unit => (Polynomial.X : Polynomial Ω)) p.1 * Polynomial.C (x p) := by
    funext p
    ring
  rw [h1, aeval_smul hF (fun _ => (Polynomial.X : Polynomial Ω)) (fun p => Polynomial.C (x p))]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  have h2 : aeval (fun p => Polynomial.C (x p)) F = Polynomial.C (aeval x F) := by
    rw [← Polynomial.algebraMap_eq]
    exact aeval_algebraMap_apply (B := Polynomial Ω) x F
  rw [h2]

/- English proof (translation)
Rewrite using `[coordIdeal, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (fun i => Polynomial.C (x i) * Polynomial.X) F = 0 ↔ _`. Rewrite using `[coneMap_of_isMultiHomog x hF]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Break down `mul_eq_zero.mp h with h | h` into its components or cases. Conclude with `absurd h (pow_ne_zero _ Polynomial.X_ne_zero)`. Conclude with `Polynomial.C_eq_zero.mp h`. Introduce `h`. Rewrite using `[h, Polynomial.C_0, mul_zero]`.
-/
theorem mem_coordIdeal_iff {r : ℕ} (x : Ix (Fin r) → Ω) {F : MRing (GlobalTheory (Fin r))} {e : ℕ}
    (hF : IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e)) : F ∈ coordIdeal ℤ x ↔ aeval x F = 0 := by
  rw [coordIdeal, RingHom.mem_ker]
  change aeval (fun i => Polynomial.C (x i) * Polynomial.X) F = 0 ↔ _
  rw [coneMap_of_isMultiHomog x hF]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero _ Polynomial.X_ne_zero)
    · exact Polynomial.C_eq_zero.mp h
  · intro h
    rw [h, Polynomial.C_0, mul_zero]

/- English proof (translation)
Simplify using `[map_sum]`.
-/
theorem aeval_linear {σ α : Type*} [Fintype α] {S : Type*} [CommRing S] [Algebra ℤ S] (v : σ → S)
    (A : α → ℤ) (q : α → σ) : aeval v (∑ j, C (A j) * X (q j) : MvPolynomial σ ℤ) = ∑ j, (A j : S) * v (q j) := by
  simp [map_sum]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem sum_mul_sum {α β γ : Type*} [Fintype β] [Fintype γ] {S : Type*} [CommRing S] (N : Matrix α β ℤ)
    (M : Matrix β γ ℤ) (w : γ → S) (i : α) :
    ∑ j, (N i j : S) * ∑ l, (M j l : S) * w l = ∑ l, ((N * M) i l : S) * w l := by
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Forms

end BlockImageInverse

set_option maxHeartbeats 1000000 in
open BlockImageInverse in

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ y k₀ r M N x J hA hB hI _ hJ hJy`. Establish `hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`. Take `⟨i, hi⟩` from `hA.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_mCoordIdeal_iff y (isMultiHomog_X' _), aeval_X]`. Conclude with `h0`. Use `choose c hc using hrel`. Establish `hrat : ∀ k i, ∃ (n : ℕ) (g' h' : MRing ι), IsMultiHomog g' (blockDeg k₀ n) ∧ IsMultiHomog h' (blockDeg k₀ n) ∧ aeval y h' ≠ 0 ∧ aeval y (X ⟨k, i⟩ : MRing ι) * aeval y h' = aeval y g' * aeval y (X ⟨k, c k⟩ : MRing ι)` using `fun k i => hB (blockDeg k 1) (X ⟨k, i⟩) (X ⟨k, c k⟩) (isMultiHomog_X' _) (isMultiHomog_X' _) (by rw [aeval_X]; exact hc k)`. Use `choose nn gg hh hgg hhh hhy hgh using hrat`.

Simplify using `only [aeval_X] at hgh`. Choose the witnesses or unpack the hypotheses as in `⟨g, a, hgJ, hga, hgy⟩ : ∃ (g : MRing ι) (a : K → ℕ), g ∈ J ∧ IsMultiHomog g a ∧ aeval y g ≠ 0 := by`. Take `⟨S, hS, rfl⟩` from `hJ`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`.

Apply `hJy` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `(mem_mCoordIdeal_iff y ha).mpr (hno f a (Ideal.subset_span hf) ha)`.

Take `⟨ma, hma⟩ : ∃ ma : MRing ι, ma = ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k` from `⟨_, rfl⟩`. Establish `hmaH : IsMultiHomog ma a`. Use `isMultiHomog_prod Finset.univ (f := fun k => (X ⟨k, c k⟩ : MRing ι) ^ a k) (a := fun k => a k • blockDeg k 1) (fun k _ => isMultiHomog_pow (isMultiHomog_X' _) _)` as an intermediate fact. Rewrite using `[hma]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k'`. Simplify using `[blockDeg, Finset.sum_apply]`. Establish `hmaz : ∀ {S : Type} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S), aeval v ma = ∏ k, v ⟨k, c k⟩ ^ a k`. Introduce `S _ _ v`. Simplify using `[hma, map_prod]`.

Establish `hmay : aeval y ma ≠ 0`. Rewrite using `[hmaz]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Take `⟨n₀, g₀, h₀, hg₀, hh₀, hh₀y, hgh₀⟩` from `hB a g ma hga hmaH hmay`. Establish `hg₀y : aeval y g₀ ≠ 0`.

Introduce `h0`. Rewrite `hgh₀` using `[h0, zero_mul]`. Conclude with `mul_ne_zero hgy hh₀y hgh₀`. Take `⟨Bf, hBf⟩ : ∃ Bf : MRing ι, Bf = g₀ * X ⟨k₀, c k₀⟩ * ∏ k, (gg k (c k) * ∏ i, hh k i)` from `⟨_, rfl⟩`. Establish `hBH : IsMultiHomog Bf (blockDeg k₀ (n₀ + 1 + ∑ k, (nn k (c k) + ∑ i, nn k i)))`.

Rewrite using `[hBf]`. Use `isMultiHomog_blockDeg_mul (isMultiHomog_blockDeg_mul hg₀ (isMultiHomog_X' _)) (isMultiHomog_blockDeg_prod _ fun k _ => isMultiHomog_blockDeg_mul (hgg k (c k)) (isMultiHomog_blockDeg_prod _ fun i _ => hhh k i))` and prove the remaining obligations. Establish `hBfac : ∀ v : (Σ k, ι k) → ℂ, aeval v Bf ≠ 0 → aeval v g₀ ≠ 0 ∧ v ⟨k₀, c k₀⟩ ≠ 0 ∧ (∀ k, aeval v (gg k (c k)) ≠ 0) ∧ ∀ k i, aeval v (hh k i) ≠ 0`. Introduce `v hv`. Rewrite `hv` using `[hBf]`.

Simplify using `only [map_mul, map_prod, aeval_X, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, not_exists] at hv`. Conclude with `⟨hv.1.1, hv.1.2, fun k => (hv.2 k).1, fun k i => (hv.2 k).2 i⟩`. Establish `hgg_c : ∀ k, aeval y (gg k (c k)) = aeval y (hh k (c k))` using `fun k => (mul_left_cancel₀ (hc k) ((hgh k (c k)).trans (mul_comm _ _))).symm`. Establish `hBy : aeval y Bf ≠ 0`. Rewrite using `[hBf]`.

Simplify using `only [map_mul, map_prod, aeval_X]`. Use `mul_ne_zero (mul_ne_zero hg₀y (hc k₀)) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[hgg_c k]`. Conclude with `mul_ne_zero (hhy k (c k)) (Finset.prod_ne_zero_iff.mpr fun i _ => hhy k i)`. Take `⟨σ, hσ⟩ : ∃ σ : (Σ k, ι k) → MRing (GlobalTheory (Fin r)), σ = fun p => if h : p.1 = k₀ then ∑ j, C (N (cast (congrArg ι h) p.2) j) * X j else 0` from `⟨_, rfl⟩`.

Establish `hσ0 : ∀ i, σ ⟨k₀, i⟩ = ∑ j, C (N i j) * X j`. Introduce `i`. Simplify using `[hσ]`. Establish `hXu : ∀ j : Ix (Fin r), IsMultiHomog (ι` using `GlobalTheory (Fin r)) (X j : MRing (GlobalTheory (Fin r))) (fun _ => 1) := by`. Introduce `j`.

Use `isMultiHomog_X' (ι := GlobalTheory (Fin r)) j using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using `[blockDeg]`. Establish `hσH : ∀ p : (Σ k, ι k), IsMultiHomog (ι` using `GlobalTheory (Fin r)) (σ p) ((fun k (_ : Unit) => if k = k₀ then 1 else 0) p.1) := by`. Introduce and unpack `⟨k, i⟩`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Rewrite using `[hσ0]`. Simplify using `only [if_true]`. Conclude with `isMultiHomog_sum _ fun j _ => isMultiHomog_C_mul (hXu j) _`.

Simplify using `only [hσ, dif_neg hk, if_neg hk]`. Conclude with `isMultiHomog_zero _`. Establish `hpull : ∀ {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) → IsMultiHomog (ι` using `GlobalTheory (Fin r)) (bind₁ σ P) (fun _ => n) := by`. Introduce `P n hP`. Use `isMultiHomog_bind₁ hP σ (fun k (_ : Unit) => if k = k₀ then 1 else 0) hσH` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single k₀]`. Simplify using `[blockDeg]`. Introduce `b _ hb`.

Simplify using `[blockDeg, hb]`. Simplify using the standard rewrite rules. Establish `heval : ∀ {S : Type} [CommRing S] [Algebra ℤ S] {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) → ∀ (u : Ix (Fin r) → S) (v : (Σ k, ι k) → S), (∀ i, v ⟨k₀, i⟩ = ∑ j, (N i j : S) * u j) → aeval u (bind₁ σ P) = aeval v P`. Introduce `S _ _ P n hP u v hv`. Rewrite using `[aeval_bind₁]`.

Use `aeval_congr_block hP fun i => ?_` and prove the remaining obligations. Rewrite using `[hσ0, hv i]`. Simplify using `[map_sum]`. Use `set e := n₀ + 1 + ∑ k, (nn k (c k) + ∑ i, nn k i) with he`. Take `⟨F, hF⟩ : ∃ F : MRing (GlobalTheory (Fin r)), F = bind₁ σ Bf` from `⟨_, rfl⟩`.

Establish `hFH : IsMultiHomog (ι` using `GlobalTheory (Fin r)) F (fun _ => e) := hF ▸ hpull hBH`. Take `⟨ρ, hρ⟩ : ∃ ρ : Ix (Fin r) → MRing ι, ρ = fun j => ∑ i, C (M j i) * X ⟨k₀, i⟩` from `⟨_, rfl⟩`. Establish `hρH : ∀ j, IsMultiHomog (ρ j) ((fun (_ : Unit) => blockDeg k₀ 1) j.1)`. Introduce `j`. Rewrite using `[hρ]`.

Conclude with `isMultiHomog_sum _ fun i _ => isMultiHomog_C_mul (isMultiHomog_X' _) _`. Establish `hGH` using `isMultiHomog_bind₁ hFH ρ (fun _ => blockDeg k₀ 1) hρH`. Establish `hGz : ∀ z : (Σ k, ι k) → ℂ, aeval z (bind₁ ρ F) = aeval (blockMapC k₀ M z) F`. Introduce `z`. Rewrite using `[aeval_bind₁]`.

Use `congrArg (fun φ => aeval φ F) (funext fun j => ?_)` and prove the remaining obligations. Simplify using `[hρ, blockMapC, map_sum]`. Establish `hFx : aeval x F = aeval y Bf` using `hF ▸ heval hBH x y fun i => hI.2 i`. Establish `hGy : aeval y (bind₁ ρ F) = aeval x F`. Rewrite using `[aeval_bind₁]`.

Use `congrArg (fun φ => aeval φ F) (funext fun j => ?_)` and prove the remaining obligations. Simplify using `[hρ, hI.1 j, map_sum]`. Take `⟨Q, hQ⟩ : ∃ Q : ∀ k, ι k → MRing ι, Q = fun k i => gg k i * ∏ i' ∈ Finset.univ.erase i, hh k i'` from `⟨_, rfl⟩`. Establish `hQH : ∀ k i, IsMultiHomog (Q k i) (blockDeg k₀ (∑ i', nn k i'))`. Introduce `k i`.

Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ]`. Conclude with `isMultiHomog_blockDeg_mul (hgg k i) (isMultiHomog_blockDeg_prod _ fun i' _ => hhh k i')`. Establish `hQv : ∀ {S : Type} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S) k i, aeval v (Q k i) = aeval v (gg k i) * ∏ i' ∈ Finset.univ.erase i, aeval v (hh k i')`. Introduce `S _ _ v k i`. Simplify using `[hQ, map_prod]`.

Take `⟨Dg, hDg⟩ : ∃ Dg : K → ℕ, Dg = fun k => if k = k₀ then 1 else ∑ i', nn k i'` from `⟨_, rfl⟩`. Take `⟨τ, hτ⟩ : ∃ τ : (Σ k, ι k) → MRing (GlobalTheory (Fin r)), τ = fun p => if p.1 = k₀ then σ p else bind₁ σ (Q p.1 p.2)` from `⟨_, rfl⟩`. Establish `hτH : ∀ p : (Σ k, ι k), IsMultiHomog (ι` using `GlobalTheory (Fin r)) (τ p) (fun _ => Dg p.1) := by`. Introduce and unpack `⟨k, i⟩`. Distinguish the cases in `hk : k = k₀`.

Substitute `hk` using the available equality. Simplify using `only [hτ, hDg, if_true]`. Simplify using `using hσH ⟨k, i⟩`. Simplify using `only [hτ, hDg, if_neg hk]`. Conclude with `hpull (hQH k i)`.

Take `⟨lam, hlam⟩ : ∃ lam : K → Ω, lam = fun k => if k = k₀ then 1 else (∏ i, aeval y (hh k i)) / y ⟨k, c k⟩` from `⟨_, rfl⟩`. Establish `hτx : ∀ p : (Σ k, ι k), aeval x (τ p) = lam p.1 * y p`. Introduce and unpack `⟨k, i⟩`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Simplify using `only [hτ, hlam, if_true, one_mul, hσ0]`. Rewrite using `[show aeval x (∑ j, C (N i j) * X j : MRing (GlobalTheory (Fin r))) = ∑ j, (N i j : Ω) * x j from aeval_linear _ _ _]`. Conclude with `(hI.2 i).symm`. Simplify using `only [hτ, hlam, if_neg hk]`. Rewrite using `[heval (hQH k i) x y (fun i => hI.2 i), hQv, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), div_mul_eq_mul_div, eq_div_iff (hc k)]`.

Take the linear combination `(-(∏ i' ∈ Finset.univ.erase i, aeval y (hh k i'))) * hgh k i`. Establish `key : ∀ (ψ : MvPolynomial K Ω →+* Polynomial Ω) (f : MRing ι), ψ (mConeMap y f) = aeval (fun p => ψ (C (y p) * X p.1)) f`. Introduce `ψ f`. Rewrite using `[mConeMap, aeval_def, aeval_def, eval₂_comp_left, show ψ.comp (algebraMap ℤ (MvPolynomial K Ω)) = algebraMap ℤ (Polynomial Ω) from RingHom.ext_int _ _]`. Both sides reduce to the same expression.

Establish `hZ1 : ∀ f ∈ mCoordIdeal y, bind₁ τ f ∈ coordIdeal ℤ x`. Introduce `f hf`. Establish `hf0 : mConeMap y f = 0` using `RingHom.mem_ker.mp hf`. Rewrite using `[coordIdeal, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (fun i => Polynomial.C (x i) * Polynomial.X) (bind₁ τ f) = 0`.

Rewrite using `[aeval_bind₁]`. Set `ψ : MvPolynomial K Ω →+* Polynomial Ω` to `(aeval (fun k => Polynomial.C (lam k) * Polynomial.X ^ Dg k) : MvPolynomial K Ω →ₐ[Ω] Polynomial Ω).toRingHom`. Establish `hc' : (fun p => aeval (fun i => Polynomial.C (x i) * Polynomial.X) (τ p)) = fun p : (Σ k, ι k) => ψ (C (y p) * X p.1)`. Use function extensionality and compare the values at `p`. Rewrite using `[coneMap_of_isMultiHomog x (hτH p), hτx p]`.

Simplify using `[ψ, Polynomial.C_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc', ← key ψ f, hf0, map_zero]`. Establish `hvan : ∀ z ∈ mcPts (mCoordIdeal y), ∀ f ∈ mCoordIdeal y, aeval z f = 0` using `fun z hz f hf => by rw [← eval_map_int]; exact hz.2 f hf`. Establish `hRz : ∀ z ∈ mcPts (mCoordIdeal y), ∀ k i, z ⟨k, i⟩ * aeval z (hh k i) = aeval z (gg k i) * z ⟨k, c k⟩`.

Introduce `z hz k i`. Establish `h1` using `isMultiHomog_mul (isMultiHomog_X' ⟨k, i⟩) (hhh k i)`. Establish `h2` using `isMultiHomog_mul (hgg k i) (isMultiHomog_X' ⟨k, c k⟩)`. Rewrite `h2` using `[add_comm]`. Establish `hmem : (X ⟨k, i⟩ * hh k i - gg k i * X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y` using `(mem_mCoordIdeal_iff y (isMultiHomog_sub h1 h2)).mpr (by`.

Simplify using `only [map_sub, map_mul, aeval_X]`. Rewrite using `[hgh k i, sub_self])`. Use `hvan z hz _ hmem` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `hSz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z g * aeval z h₀ = aeval z g₀ * aeval z ma`.

Introduce `z hz`. Establish `h1` using `isMultiHomog_mul hga hh₀`. Establish `h2` using `isMultiHomog_mul hg₀ hmaH`. Rewrite `h2` using `[add_comm]`. Establish `hmem : (g * h₀ - g₀ * ma : MRing ι) ∈ mCoordIdeal y` using `(mem_mCoordIdeal_iff y (isMultiHomog_sub h1 h2)).mpr (by`.

Simplify using `only [map_sub, map_mul]`. Rewrite using `[hgh₀, sub_self])`. Use `hvan z hz _ hmem` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `hLz : ∀ z ∈ mcPts (mCoordIdeal y), ∀ i, z ⟨k₀, i⟩ = ∑ j, (N i j : ℂ) * blockMapC k₀ M z j`.

Introduce `z hz i`. Establish `hL : IsMultiHomog (X ⟨k₀, i⟩ - ∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) (blockDeg k₀ 1)` using `isMultiHomog_sub (isMultiHomog_X' _) (isMultiHomog_sum _ fun l _ => isMultiHomog_C_mul (isMultiHomog_X' _) _)`. Establish `hyNM : y ⟨k₀, i⟩ = ∑ l, ((N * M) i l : Ω) * y ⟨k₀, l⟩`. Rewrite using `[← sum_mul_sum N M (fun l => y ⟨k₀, l⟩) i, hI.2 i]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hI.1 j]`.

Establish `hmem` using `(mem_mCoordIdeal_iff y hL).mpr (by`. Rewrite using `[map_sub, aeval_X, show aeval y (∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) = ∑ l, ((N * M) i l : Ω) * y ⟨k₀, l⟩ from aeval_linear _ _ _]`. Conclude with `sub_eq_zero.mpr hyNM)`. Use `hvan z hz _ hmem` as an intermediate fact. Rewrite `this` using `[map_sub, aeval_X, show aeval z (∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) = ∑ l, ((N * M) i l : ℂ) * z ⟨k₀, l⟩ from aeval_linear _ _ _, sub_eq_zero]`.

Rewrite using `[this, ← sum_mul_sum N M (fun l => z ⟨k₀, l⟩) i]`. Both sides reduce to the same expression. Establish `hFz : ∀ z ∈ mcPts (mCoordIdeal y), aeval (blockMapC k₀ M z) F = aeval z Bf` using `fun z hz => hF ▸ heval hBH _ z (hLz z hz)`. Establish `hcz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z Bf ≠ 0 → ∀ k, z ⟨k, c k⟩ ≠ 0`. Introduce `z hz hBz k h0`.

Take `⟨i, hi⟩` from `hz.1 k`. Use `hRz z hz k i` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `hi ((mul_eq_zero.mp this).resolve_right ((hBfac z hBz).2.2.2 k i))`. Establish `hgz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z Bf ≠ 0 → aeval z g ≠ 0`.

Introduce `z hz hBz h0`. Use `hSz z hz` as an intermediate fact. Rewrite `this` using `[h0, zero_mul, hmaz]`. Conclude with `mul_ne_zero (hBfac z hBz).1 (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcz z hz hBz k)) this.symm`. Use `⟨F, e, bind₁ ρ F, _, hFH, ?_, hGH, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_coordIdeal_iff x hFH, hFx]`. Conclude with `hBy`. Rewrite using `[mem_mCoordIdeal_iff y hGH, hGy, hFx]`. Conclude with `hBy`. Introduce `z`.

Rewrite using `[eval_map_int, eval_map_int, hGz]`. Introduce `u hu hFu`. Rewrite `hFu` using `[eval_map_int]`. Establish `hu0 : ∀ f ∈ coordIdeal ℤ x, aeval u f = 0` using `fun f hf => by`. Rewrite using `[← eval_map_int]`.

Conclude with `hu.2 f hf`. Take `⟨z, hz⟩ : ∃ z : (Σ k, ι k) → ℂ, z = fun p => aeval u (τ p)` from `⟨_, rfl⟩`. Establish `hzk₀ : ∀ i, z ⟨k₀, i⟩ = ∑ j, (N i j : ℂ) * u j`. Introduce `i`. Simplify using `[hz, hτ, hσ0, map_sum]`.

Establish `hzB : aeval z Bf = aeval u F`. Rewrite using `[hF]`. Conclude with `(heval hBH u z hzk₀).symm`. Establish `hfac` using `hBfac z (hzB ▸ hFu)`. Establish `hzc : ∀ k, z ⟨k, c k⟩ ≠ 0`.

Introduce `k`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Conclude with `hfac.2.1`. Establish `: z ⟨k, c k⟩ = aeval u (bind₁ σ (Q k (c k)))`.

Rewrite using `[hz]`. Simplify using `only [hτ, if_neg hk]`. Rewrite using `[this, heval (hQH k (c k)) u z hzk₀, hQv]`. Conclude with `mul_ne_zero (hfac.2.2.1 k) (Finset.prod_ne_zero_iff.mpr fun i _ => hfac.2.2.2 k i)`. Establish `hzmem : z ∈ mcPts (mCoordIdeal y)`.

Use `⟨fun k => ⟨c k, hzc k⟩, fun f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[eval_map_int]`. Use `hu0 _ (hZ1 f hf)` as an intermediate fact. Rewrite `this` using `[aeval_bind₁, ← hz]`. Then use the resulting hypothesis. Establish `hMN : blockMapC k₀ M z = u`.

Use function extensionality and compare the values at `j`. Establish `hLx : (X j - ∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) ∈ coordIdeal ℤ x`. Use `(mem_coordIdeal_iff x (e := 1) (isMultiHomog_sub (hXu j) (isMultiHomog_sum _ fun l _ => isMultiHomog_C_mul (hXu l) _))).mpr ?_` and prove the remaining obligations. Rewrite using `[map_sub, aeval_X, show aeval x (∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) = ∑ l, ((M * N) j l : Ω) * x l from aeval_linear _ _ _, sub_eq_zero, ← sum_mul_sum M N x j, hI.1 j]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hI.2 i]`.

Use `hu0 _ hLx` as an intermediate fact. Rewrite `this` using `[map_sub, aeval_X, show aeval u (∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) = ∑ l, ((M * N) j l : ℂ) * u l from aeval_linear _ _ _, sub_eq_zero, ← sum_mul_sum M N u j]`. Rewrite using `[this]`. Simplify using `only [blockMapC, hzk₀]`. Use `⟨z, hzmem, fun hzJ => hgz z hzmem (hzB ▸ hFu) ?_, ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← eval_map_int]`. Conclude with `hzJ.2 g hgJ`. Rewrite using `[hMN]`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.

Introduce `z hz hFz' hzJ`. Rewrite `hFz'` using `[eval_map_int, hFz z hz]`. Conclude with `hgz z hz hFz' (by rw [← eval_map_int]; exact hzJ.2 g hgJ)`. Introduce `z hz z' hz' hF0 hor`. Rewrite `hF0` using `[eval_map_int, hFz z hz]`.

Take `⟨cc, hcc, hczz⟩` from `hor`. Establish `ht : cc () ≠ 0` using `hcc ()`. Establish `hk₀ : ∀ i, z ⟨k₀, i⟩ = cc () * z' ⟨k₀, i⟩`. Introduce `i`. Rewrite using `[hLz z hz i, hLz z' hz' i, hczz, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Take `⟨⟨⟩, j⟩` from `j`. Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Establish `hscale : ∀ {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) → aeval z P = cc () ^ n * aeval z' P`.

Introduce `P n hP`. Rewrite using `[aeval_congr_block hP (v := z) (w := fun p => (fun k => if k = k₀ then cc () else 1) p.1 * z' p) (by intro i; simp [hk₀]), aeval_smul hP (fun k => if k = k₀ then cc () else 1) z']`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single k₀]`. Simplify using `[blockDeg]`.

Introduce `b _ hb`. Simplify using `[blockDeg, hb]`. Simplify using the standard rewrite rules. Establish `hB' : aeval z' Bf ≠ 0`. Introduce `h0`.

Apply `hF0` to reduce the goal to its premises. Rewrite using `[hscale hBH, h0, mul_zero]`. Use `⟨fun k => if k = k₀ then cc () else z ⟨k, c k⟩ / z' ⟨k, c k⟩, fun k => ?_, ?_⟩` and prove the remaining obligations. Use `show (if k = k₀ then cc () else z ⟨k, c k⟩ / z' ⟨k, c k⟩) ≠ 0 split_ifs`. Conclude with `ht`.

Conclude with `div_ne_zero (hcz z hz hF0 k) (hcz z' hz' hB' k)`. Use function extensionality and compare the values at `p`. Take `⟨k, i⟩` from `p`. Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality.

Simplify using `[hk₀]`. Simplify using `only [if_neg hk]`. Establish `h1` using `hRz z hz k i`. Establish `h2` using `hRz z' hz' k i`. Rewrite `h1` using `[hscale (hhh k i), hscale (hgg k i)]`.

Establish `hh'` using `(hBfac z' hB').2.2.2 k i`. Establish `hc'` using `hcz z' hz' hB' k`. Establish `h3 : (z ⟨k, i⟩ * z' ⟨k, c k⟩ - z ⟨k, c k⟩ * z' ⟨k, i⟩) * (cc () ^ nn k i * aeval z' (hh k i)) = 0`. Take the linear combination `z' ⟨k, c k⟩ * h1 - cc () ^ nn k i * z ⟨k, c k⟩ * h2`. Establish `h4` using `(mul_eq_zero.mp h3).resolve_right (mul_ne_zero (pow_ne_zero _ ht) hh')`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff hc']`. Take the linear combination `h4`.
-/
theorem BlockImageInverse.proof : BlockImageInverse.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ r M N x J hA hB hI _ hJ hJy
  classical

  have hrel : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hA.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mem_mCoordIdeal_iff y (isMultiHomog_X' _), aeval_X]
    exact h0
  choose c hc using hrel

  have hrat : ∀ k i, ∃ (n : ℕ) (g' h' : MRing ι), IsMultiHomog g' (blockDeg k₀ n) ∧
      IsMultiHomog h' (blockDeg k₀ n) ∧ aeval y h' ≠ 0 ∧
      aeval y (X ⟨k, i⟩ : MRing ι) * aeval y h' = aeval y g' * aeval y (X ⟨k, c k⟩ : MRing ι) :=
    fun k i => hB (blockDeg k 1) (X ⟨k, i⟩) (X ⟨k, c k⟩) (isMultiHomog_X' _) (isMultiHomog_X' _)
      (by rw [aeval_X]; exact hc k)
  choose nn gg hh hgg hhh hhy hgh using hrat
  simp only [aeval_X] at hgh

  obtain ⟨g, a, hgJ, hga, hgy⟩ : ∃ (g : MRing ι) (a : K → ℕ), g ∈ J ∧ IsMultiHomog g a ∧ aeval y g ≠ 0 := by
    obtain ⟨S, hS, rfl⟩ := hJ
    by_contra hno
    push Not at hno
    apply hJy
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact (mem_mCoordIdeal_iff y ha).mpr (hno f a (Ideal.subset_span hf) ha)

  obtain ⟨ma, hma⟩ : ∃ ma : MRing ι, ma = ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k := ⟨_, rfl⟩
  have hmaH : IsMultiHomog ma a := by
    have := isMultiHomog_prod Finset.univ (f := fun k => (X ⟨k, c k⟩ : MRing ι) ^ a k)
      (a := fun k => a k • blockDeg k 1) (fun k _ => isMultiHomog_pow (isMultiHomog_X' _) _)
    rw [hma]
    convert this using 1
    funext k'
    simp [blockDeg, Finset.sum_apply]
  have hmaz : ∀ {S : Type} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S),
      aeval v ma = ∏ k, v ⟨k, c k⟩ ^ a k := by
    intro S _ _ v
    simp [hma, map_prod]
  have hmay : aeval y ma ≠ 0 := by
    rw [hmaz]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  obtain ⟨n₀, g₀, h₀, hg₀, hh₀, hh₀y, hgh₀⟩ := hB a g ma hga hmaH hmay
  have hg₀y : aeval y g₀ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hgh₀
    exact mul_ne_zero hgy hh₀y hgh₀

  obtain ⟨Bf, hBf⟩ : ∃ Bf : MRing ι, Bf = g₀ * X ⟨k₀, c k₀⟩ * ∏ k, (gg k (c k) * ∏ i, hh k i) := ⟨_, rfl⟩
  have hBH : IsMultiHomog Bf (blockDeg k₀ (n₀ + 1 + ∑ k, (nn k (c k) + ∑ i, nn k i))) := by
    rw [hBf]
    refine isMultiHomog_blockDeg_mul (isMultiHomog_blockDeg_mul hg₀ (isMultiHomog_X' _))
      (isMultiHomog_blockDeg_prod _ fun k _ => isMultiHomog_blockDeg_mul (hgg k (c k))
        (isMultiHomog_blockDeg_prod _ fun i _ => hhh k i))
  have hBfac : ∀ v : (Σ k, ι k) → ℂ, aeval v Bf ≠ 0 → aeval v g₀ ≠ 0 ∧ v ⟨k₀, c k₀⟩ ≠ 0 ∧
      (∀ k, aeval v (gg k (c k)) ≠ 0) ∧ ∀ k i, aeval v (hh k i) ≠ 0 := by
    intro v hv
    rw [hBf] at hv
    simp only [map_mul, map_prod, aeval_X, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists] at hv
    exact ⟨hv.1.1, hv.1.2, fun k => (hv.2 k).1, fun k i => (hv.2 k).2 i⟩
  have hgg_c : ∀ k, aeval y (gg k (c k)) = aeval y (hh k (c k)) := fun k =>
    (mul_left_cancel₀ (hc k) ((hgh k (c k)).trans (mul_comm _ _))).symm
  have hBy : aeval y Bf ≠ 0 := by
    rw [hBf]
    simp only [map_mul, map_prod, aeval_X]
    refine mul_ne_zero (mul_ne_zero hg₀y (hc k₀)) (Finset.prod_ne_zero_iff.mpr fun k _ => ?_)
    rw [hgg_c k]
    exact mul_ne_zero (hhy k (c k)) (Finset.prod_ne_zero_iff.mpr fun i _ => hhy k i)

  obtain ⟨σ, hσ⟩ : ∃ σ : (Σ k, ι k) → MRing (GlobalTheory (Fin r)), σ = fun p =>
      if h : p.1 = k₀ then ∑ j, C (N (cast (congrArg ι h) p.2) j) * X j else 0 := ⟨_, rfl⟩
  have hσ0 : ∀ i, σ ⟨k₀, i⟩ = ∑ j, C (N i j) * X j := by
    intro i
    simp [hσ]
  have hXu : ∀ j : Ix (Fin r), IsMultiHomog (ι := GlobalTheory (Fin r)) (X j : MRing (GlobalTheory (Fin r))) (fun _ => 1) := by
    intro j
    convert isMultiHomog_X' (ι := GlobalTheory (Fin r)) j using 1
    funext u
    simp [blockDeg]
  have hσH : ∀ p : (Σ k, ι k), IsMultiHomog (ι := GlobalTheory (Fin r)) (σ p)
      ((fun k (_ : Unit) => if k = k₀ then 1 else 0) p.1) := by
    rintro ⟨k, i⟩
    by_cases hk : k = k₀
    · subst hk
      rw [hσ0]
      simp only [if_true]
      exact isMultiHomog_sum _ fun j _ => isMultiHomog_C_mul (hXu j) _
    · simp only [hσ, dif_neg hk, if_neg hk]
      exact isMultiHomog_zero _
  have hpull : ∀ {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) →
      IsMultiHomog (ι := GlobalTheory (Fin r)) (bind₁ σ P) (fun _ => n) := by
    intro P n hP
    have := isMultiHomog_bind₁ hP σ (fun k (_ : Unit) => if k = k₀ then 1 else 0) hσH
    convert this using 1
    funext u
    rw [Finset.sum_apply, Finset.sum_eq_single k₀]
    · simp [blockDeg]
    · intro b _ hb
      simp [blockDeg, hb]
    · simp
  have heval : ∀ {S : Type} [CommRing S] [Algebra ℤ S] {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) →
      ∀ (u : Ix (Fin r) → S) (v : (Σ k, ι k) → S), (∀ i, v ⟨k₀, i⟩ = ∑ j, (N i j : S) * u j) →
      aeval u (bind₁ σ P) = aeval v P := by
    intro S _ _ P n hP u v hv
    rw [aeval_bind₁]
    refine aeval_congr_block hP fun i => ?_
    rw [hσ0, hv i]
    simp [map_sum]

  set e := n₀ + 1 + ∑ k, (nn k (c k) + ∑ i, nn k i) with he
  obtain ⟨F, hF⟩ : ∃ F : MRing (GlobalTheory (Fin r)), F = bind₁ σ Bf := ⟨_, rfl⟩
  have hFH : IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e) := hF ▸ hpull hBH
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Ix (Fin r) → MRing ι, ρ = fun j => ∑ i, C (M j i) * X ⟨k₀, i⟩ := ⟨_, rfl⟩
  have hρH : ∀ j, IsMultiHomog (ρ j) ((fun (_ : Unit) => blockDeg k₀ 1) j.1) := by
    intro j
    rw [hρ]
    exact isMultiHomog_sum _ fun i _ => isMultiHomog_C_mul (isMultiHomog_X' _) _
  have hGH := isMultiHomog_bind₁ hFH ρ (fun _ => blockDeg k₀ 1) hρH
  have hGz : ∀ z : (Σ k, ι k) → ℂ, aeval z (bind₁ ρ F) = aeval (blockMapC k₀ M z) F := by
    intro z
    rw [aeval_bind₁]
    refine congrArg (fun φ => aeval φ F) (funext fun j => ?_)
    simp [hρ, blockMapC, map_sum]
  have hFx : aeval x F = aeval y Bf := hF ▸ heval hBH x y fun i => hI.2 i
  have hGy : aeval y (bind₁ ρ F) = aeval x F := by
    rw [aeval_bind₁]
    refine congrArg (fun φ => aeval φ F) (funext fun j => ?_)
    simp [hρ, hI.1 j, map_sum]

  obtain ⟨Q, hQ⟩ : ∃ Q : ∀ k, ι k → MRing ι, Q = fun k i => gg k i * ∏ i' ∈ Finset.univ.erase i, hh k i' :=
    ⟨_, rfl⟩
  have hQH : ∀ k i, IsMultiHomog (Q k i) (blockDeg k₀ (∑ i', nn k i')) := by
    intro k i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hQ]
    exact isMultiHomog_blockDeg_mul (hgg k i) (isMultiHomog_blockDeg_prod _ fun i' _ => hhh k i')
  have hQv : ∀ {S : Type} [CommRing S] [Algebra ℤ S] (v : (Σ k, ι k) → S) k i,
      aeval v (Q k i) = aeval v (gg k i) * ∏ i' ∈ Finset.univ.erase i, aeval v (hh k i') := by
    intro S _ _ v k i
    simp [hQ, map_prod]
  obtain ⟨Dg, hDg⟩ : ∃ Dg : K → ℕ, Dg = fun k => if k = k₀ then 1 else ∑ i', nn k i' := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Σ k, ι k) → MRing (GlobalTheory (Fin r)),
      τ = fun p => if p.1 = k₀ then σ p else bind₁ σ (Q p.1 p.2) := ⟨_, rfl⟩
  have hτH : ∀ p : (Σ k, ι k), IsMultiHomog (ι := GlobalTheory (Fin r)) (τ p) (fun _ => Dg p.1) := by
    rintro ⟨k, i⟩
    by_cases hk : k = k₀
    · subst hk
      simp only [hτ, hDg, if_true]
      simpa using hσH ⟨k, i⟩
    · simp only [hτ, hDg, if_neg hk]
      exact hpull (hQH k i)
  obtain ⟨lam, hlam⟩ : ∃ lam : K → Ω,
      lam = fun k => if k = k₀ then 1 else (∏ i, aeval y (hh k i)) / y ⟨k, c k⟩ := ⟨_, rfl⟩
  have hτx : ∀ p : (Σ k, ι k), aeval x (τ p) = lam p.1 * y p := by
    rintro ⟨k, i⟩
    by_cases hk : k = k₀
    · subst hk
      simp only [hτ, hlam, if_true, one_mul, hσ0]
      rw [show aeval x (∑ j, C (N i j) * X j : MRing (GlobalTheory (Fin r))) = ∑ j, (N i j : Ω) * x j from
        aeval_linear _ _ _]
      exact (hI.2 i).symm
    · simp only [hτ, hlam, if_neg hk]
      rw [heval (hQH k i) x y (fun i => hI.2 i), hQv, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        div_mul_eq_mul_div, eq_div_iff (hc k)]
      linear_combination (-(∏ i' ∈ Finset.univ.erase i, aeval y (hh k i'))) * hgh k i

  have key : ∀ (ψ : MvPolynomial K Ω →+* Polynomial Ω) (f : MRing ι),
      ψ (mConeMap y f) = aeval (fun p => ψ (C (y p) * X p.1)) f := by
    intro ψ f
    rw [mConeMap, aeval_def, aeval_def, eval₂_comp_left,
      show ψ.comp (algebraMap ℤ (MvPolynomial K Ω)) = algebraMap ℤ (Polynomial Ω) from RingHom.ext_int _ _]
    rfl
  have hZ1 : ∀ f ∈ mCoordIdeal y, bind₁ τ f ∈ coordIdeal ℤ x := by
    intro f hf
    have hf0 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
    rw [coordIdeal, RingHom.mem_ker]
    change aeval (fun i => Polynomial.C (x i) * Polynomial.X) (bind₁ τ f) = 0
    rw [aeval_bind₁]
    let ψ : MvPolynomial K Ω →+* Polynomial Ω :=
      (aeval (fun k => Polynomial.C (lam k) * Polynomial.X ^ Dg k) : MvPolynomial K Ω →ₐ[Ω] Polynomial Ω).toRingHom
    have hc' : (fun p => aeval (fun i => Polynomial.C (x i) * Polynomial.X) (τ p)) =
        fun p : (Σ k, ι k) => ψ (C (y p) * X p.1) := by
      funext p
      rw [coneMap_of_isMultiHomog x (hτH p), hτx p]
      simp [ψ, Polynomial.C_mul]
      ring
    rw [hc', ← key ψ f, hf0, map_zero]

  have hvan : ∀ z ∈ mcPts (mCoordIdeal y), ∀ f ∈ mCoordIdeal y, aeval z f = 0 :=
    fun z hz f hf => by rw [← eval_map_int]; exact hz.2 f hf
  have hRz : ∀ z ∈ mcPts (mCoordIdeal y), ∀ k i,
      z ⟨k, i⟩ * aeval z (hh k i) = aeval z (gg k i) * z ⟨k, c k⟩ := by
    intro z hz k i
    have h1 := isMultiHomog_mul (isMultiHomog_X' ⟨k, i⟩) (hhh k i)
    have h2 := isMultiHomog_mul (hgg k i) (isMultiHomog_X' ⟨k, c k⟩)
    rw [add_comm] at h2
    have hmem : (X ⟨k, i⟩ * hh k i - gg k i * X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y :=
      (mem_mCoordIdeal_iff y (isMultiHomog_sub h1 h2)).mpr (by
        simp only [map_sub, map_mul, aeval_X]
        rw [hgh k i, sub_self])
    have := hvan z hz _ hmem
    simpa [sub_eq_zero] using this
  have hSz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z g * aeval z h₀ = aeval z g₀ * aeval z ma := by
    intro z hz
    have h1 := isMultiHomog_mul hga hh₀
    have h2 := isMultiHomog_mul hg₀ hmaH
    rw [add_comm] at h2
    have hmem : (g * h₀ - g₀ * ma : MRing ι) ∈ mCoordIdeal y :=
      (mem_mCoordIdeal_iff y (isMultiHomog_sub h1 h2)).mpr (by
        simp only [map_sub, map_mul]
        rw [hgh₀, sub_self])
    have := hvan z hz _ hmem
    simpa [sub_eq_zero] using this
  have hLz : ∀ z ∈ mcPts (mCoordIdeal y), ∀ i, z ⟨k₀, i⟩ = ∑ j, (N i j : ℂ) * blockMapC k₀ M z j := by
    intro z hz i
    have hL : IsMultiHomog (X ⟨k₀, i⟩ - ∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) (blockDeg k₀ 1) :=
      isMultiHomog_sub (isMultiHomog_X' _) (isMultiHomog_sum _ fun l _ => isMultiHomog_C_mul (isMultiHomog_X' _) _)
    have hyNM : y ⟨k₀, i⟩ = ∑ l, ((N * M) i l : Ω) * y ⟨k₀, l⟩ := by
      rw [← sum_mul_sum N M (fun l => y ⟨k₀, l⟩) i, hI.2 i]
      exact Finset.sum_congr rfl fun j _ => by rw [hI.1 j]
    have hmem := (mem_mCoordIdeal_iff y hL).mpr (by
      rw [map_sub, aeval_X, show aeval y (∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) =
        ∑ l, ((N * M) i l : Ω) * y ⟨k₀, l⟩ from aeval_linear _ _ _]
      exact sub_eq_zero.mpr hyNM)
    have := hvan z hz _ hmem
    rw [map_sub, aeval_X, show aeval z (∑ l, C ((N * M) i l) * X ⟨k₀, l⟩ : MRing ι) =
      ∑ l, ((N * M) i l : ℂ) * z ⟨k₀, l⟩ from aeval_linear _ _ _, sub_eq_zero] at this
    rw [this, ← sum_mul_sum N M (fun l => z ⟨k₀, l⟩) i]
    rfl
  have hFz : ∀ z ∈ mcPts (mCoordIdeal y), aeval (blockMapC k₀ M z) F = aeval z Bf :=
    fun z hz => hF ▸ heval hBH _ z (hLz z hz)
  have hcz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z Bf ≠ 0 → ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz hBz k h0
    obtain ⟨i, hi⟩ := hz.1 k
    have := hRz z hz k i
    rw [h0, mul_zero] at this
    exact hi ((mul_eq_zero.mp this).resolve_right ((hBfac z hBz).2.2.2 k i))
  have hgz : ∀ z ∈ mcPts (mCoordIdeal y), aeval z Bf ≠ 0 → aeval z g ≠ 0 := by
    intro z hz hBz h0
    have := hSz z hz
    rw [h0, zero_mul, hmaz] at this
    exact mul_ne_zero (hBfac z hBz).1
      (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hcz z hz hBz k)) this.symm
  refine ⟨F, e, bind₁ ρ F, _, hFH, ?_, hGH, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_coordIdeal_iff x hFH, hFx]
    exact hBy
  · rw [mem_mCoordIdeal_iff y hGH, hGy, hFx]
    exact hBy
  · intro z
    rw [eval_map_int, eval_map_int, hGz]
  · intro u hu hFu
    rw [eval_map_int] at hFu
    have hu0 : ∀ f ∈ coordIdeal ℤ x, aeval u f = 0 := fun f hf => by
      rw [← eval_map_int]
      exact hu.2 f hf
    obtain ⟨z, hz⟩ : ∃ z : (Σ k, ι k) → ℂ, z = fun p => aeval u (τ p) := ⟨_, rfl⟩
    have hzk₀ : ∀ i, z ⟨k₀, i⟩ = ∑ j, (N i j : ℂ) * u j := by
      intro i
      simp [hz, hτ, hσ0, map_sum]
    have hzB : aeval z Bf = aeval u F := by
      rw [hF]
      exact (heval hBH u z hzk₀).symm
    have hfac := hBfac z (hzB ▸ hFu)
    have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := by
      intro k
      by_cases hk : k = k₀
      · subst hk
        exact hfac.2.1
      · have : z ⟨k, c k⟩ = aeval u (bind₁ σ (Q k (c k))) := by
          rw [hz]
          simp only [hτ, if_neg hk]
        rw [this, heval (hQH k (c k)) u z hzk₀, hQv]
        exact mul_ne_zero (hfac.2.2.1 k) (Finset.prod_ne_zero_iff.mpr fun i _ => hfac.2.2.2 k i)
    have hzmem : z ∈ mcPts (mCoordIdeal y) := by
      refine ⟨fun k => ⟨c k, hzc k⟩, fun f hf => ?_⟩
      rw [eval_map_int]
      have := hu0 _ (hZ1 f hf)
      rwa [aeval_bind₁, ← hz] at this
    have hMN : blockMapC k₀ M z = u := by
      funext j
      have hLx : (X j - ∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) ∈ coordIdeal ℤ x := by
        refine (mem_coordIdeal_iff x (e := 1) (isMultiHomog_sub (hXu j) (isMultiHomog_sum _ fun l _ =>
          isMultiHomog_C_mul (hXu l) _))).mpr ?_
        rw [map_sub, aeval_X, show aeval x (∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) =
          ∑ l, ((M * N) j l : Ω) * x l from aeval_linear _ _ _, sub_eq_zero,
          ← sum_mul_sum M N x j, hI.1 j]
        exact Finset.sum_congr rfl fun i _ => by rw [hI.2 i]
      have := hu0 _ hLx
      rw [map_sub, aeval_X, show aeval u (∑ l, C ((M * N) j l) * X l : MRing (GlobalTheory (Fin r))) =
        ∑ l, ((M * N) j l : ℂ) * u l from aeval_linear _ _ _, sub_eq_zero,
        ← sum_mul_sum M N u j] at this
      rw [this]
      simp only [blockMapC, hzk₀]
    refine ⟨z, hzmem, fun hzJ => hgz z hzmem (hzB ▸ hFu) ?_, ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩⟩
    · rw [← eval_map_int]
      exact hzJ.2 g hgJ
    · rw [hMN]
      funext p
      simp
  · intro z hz hFz' hzJ
    rw [eval_map_int, hFz z hz] at hFz'
    exact hgz z hz hFz' (by rw [← eval_map_int]; exact hzJ.2 g hgJ)
  · intro z hz z' hz' hF0 hor
    rw [eval_map_int, hFz z hz] at hF0
    obtain ⟨cc, hcc, hczz⟩ := hor
    have ht : cc () ≠ 0 := hcc ()
    have hk₀ : ∀ i, z ⟨k₀, i⟩ = cc () * z' ⟨k₀, i⟩ := by
      intro i
      rw [hLz z hz i, hLz z' hz' i, hczz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      obtain ⟨⟨⟩, j⟩ := j
      dsimp only
      ring
    have hscale : ∀ {P : MRing ι} {n : ℕ}, IsMultiHomog P (blockDeg k₀ n) →
        aeval z P = cc () ^ n * aeval z' P := by
      intro P n hP
      rw [aeval_congr_block hP (v := z) (w := fun p => (fun k => if k = k₀ then cc () else 1) p.1 * z' p)
        (by intro i; simp [hk₀]), aeval_smul hP (fun k => if k = k₀ then cc () else 1) z']
      congr 1
      rw [Finset.prod_eq_single k₀]
      · simp [blockDeg]
      · intro b _ hb
        simp [blockDeg, hb]
      · simp
    have hB' : aeval z' Bf ≠ 0 := by
      intro h0
      apply hF0
      rw [hscale hBH, h0, mul_zero]
    refine ⟨fun k => if k = k₀ then cc () else z ⟨k, c k⟩ / z' ⟨k, c k⟩, fun k => ?_, ?_⟩
    · show (if k = k₀ then cc () else z ⟨k, c k⟩ / z' ⟨k, c k⟩) ≠ 0
      split_ifs
      · exact ht
      · exact div_ne_zero (hcz z hz hF0 k) (hcz z' hz' hB' k)
    · funext p
      obtain ⟨k, i⟩ := p
      by_cases hk : k = k₀
      · subst hk
        simp [hk₀]
      · simp only [if_neg hk]
        have h1 := hRz z hz k i
        have h2 := hRz z' hz' k i
        rw [hscale (hhh k i), hscale (hgg k i)] at h1
        have hh' := (hBfac z' hB').2.2.2 k i
        have hc' := hcz z' hz' hB' k
        have h3 : (z ⟨k, i⟩ * z' ⟨k, c k⟩ - z ⟨k, c k⟩ * z' ⟨k, i⟩) * (cc () ^ nn k i * aeval z' (hh k i)) = 0 := by
          linear_combination z' ⟨k, c k⟩ * h1 - cc () ^ nn k i * z ⟨k, c k⟩ * h2
        have h4 := (mul_eq_zero.mp h3).resolve_right (mul_ne_zero (pow_ne_zero _ ht) hh')
        rw [div_mul_eq_mul_div, eq_div_iff hc']
        linear_combination h4

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
