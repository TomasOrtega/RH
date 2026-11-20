import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[mem_support_iff, coeff_C]`. Use `split_ifs at hm with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Conclude with `absurd rfl hm`.
-/
theorem isMultiHomog_C (c : ℂ) : IsMultiHomog (C c : MvPolynomial (Σ k, ι k) ℂ) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.1 (support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_add {f g : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, h₁, m₂, h₂, rfl⟩` from `Finset.mem_add.1 (support_mul f g hm)`. Establish `e₁` using `hf m₁ h₁ k`. Establish `e₂` using `hg m₂ h₂ k`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, e₁, e₂, Pi.add_apply]`.
-/
theorem isMultiHomog_mul {f g : MvPolynomial (Σ k, ι k) ℂ} {a b : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  have e₁ := hf m₁ h₁ k
  have e₂ := hg m₂ h₂ k
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, e₁, e₂, Pi.add_apply]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Take `⟨k₀, i₀⟩` from `s`. Distinguish the cases in `h : k = k₀`.

Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Establish `: ∀ i, (Finsupp.single (⟨k₀, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0` using `fun i => by`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `e`.

Conclude with `h (congrArg Sigma.fst e).symm`. Simplify using `[this, Pi.single_apply, h]`.
-/
theorem isMultiHomog_X [DecidableEq K] (s : Σ k, ι k) :
    IsMultiHomog (X s : MvPolynomial (Σ k, ι k) ℂ) (Pi.single s.1 1 : K → ℕ) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := s
  by_cases h : k = k₀
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ i, (Finsupp.single (⟨k₀, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = 0 := fun i => by
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact h (congrArg Sigma.fst e).symm
    simp [this, Pi.single_apply, h]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using isMultiHomog_C (K := K) (ι := ι) 1`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ih hf`.
-/
theorem isMultiHomog_pow {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using isMultiHomog_C (K := K) (ι := ι) 1
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul ih hf

/- English proof (translation)
Establish `h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) (∑ k ∈ s, e k • (Pi.single k 1 : K → ℕ))`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_C (K := K) (ι := ι) 1`. Consider the case `insert k s hk ih`.

Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk]`. Conclude with `isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, p k⟩) (e k)) ih`. Establish `h2 : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `h3` using `h Finset.univ`. Rewrite `h3` using `[h2]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_chartMonomial (p : (k : K) → ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k)
      (∑ k ∈ s, e k • (Pi.single k 1 : K → ℕ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (K := K) (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X ⟨k, p k⟩) (e k)) ih
  have h2 : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h3 := h Finset.univ
  rwa [h2] at h3

/- English proof (translation)
Establish `hM : ∀ e : K → ℕ, (∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) - 1 ∈ I`. Introduce `e`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_prod, sub_eq_zero]`. Use `Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Establish `: Ideal.Quotient.mk I (X ⟨k, p k⟩) = 1`.

Use `Ideal.Quotient.eq_zero_iff_mem.2 (hI k)` as an intermediate fact. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Then use the resulting hypothesis. Rewrite using `[map_pow, this, one_pow]`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => exact ⟨0, C a, isMultiHomog_C a, by simp⟩`.

Consider the case `add u v hu hv`. Take `⟨d₁, H₁, h₁, m₁⟩` from `hu`. Take `⟨d₂, H₂, h₂, m₂⟩` from `hv`. Use `set M₁ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₁ k with hM₁`. Use `set M₂ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₂ k with hM₂`.

Use `⟨d₁ + d₂, H₁ * M₂ + H₂ * M₁, isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMonomial p d₂)) (add_comm d₂ d₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMonomial p d₁)), ?_⟩` and prove the remaining obligations. Establish `e : H₁ * M₂ + H₂ * M₁ - (u + v) = M₂ * (H₁ - u) + u * (M₂ - 1) + M₁ * (H₂ - v) + v * (M₁ - 1)` using `by ring`. Rewrite using `[e]`. Conclude with `I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ m₁) (I.mul_mem_left _ (hM d₂))) (I.mul_mem_left _ m₂)) (I.mul_mem_left _ (hM d₁))`. Consider the case `mul_X u s hu`.

Take `⟨d, H, h, m⟩` from `hu`. Use `⟨d + Pi.single s.1 1, H * X s, isMultiHomog_mul h (isMultiHomog_X s), ?_⟩` and prove the remaining obligations. Establish `e : H * X s - u * X s = X s * (H - u)` using `by ring`. Rewrite using `[e]`. Conclude with `I.mul_mem_left _ m`.
-/
theorem exists_form (p : (k : K) → ι k) (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℂ) :
    ∃ (d : K → ℕ) (H : MvPolynomial (Σ k, ι k) ℂ), IsMultiHomog H d ∧ H - g ∈ I := by
  classical
  have hM : ∀ e : K → ℕ, (∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ e k) - 1 ∈ I := by
    intro e
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_prod, sub_eq_zero]
    refine Finset.prod_eq_one fun k _ => ?_
    have : Ideal.Quotient.mk I (X ⟨k, p k⟩) = 1 := by
      have := Ideal.Quotient.eq_zero_iff_mem.2 (hI k)
      rwa [map_sub, map_one, sub_eq_zero] at this
    rw [map_pow, this, one_pow]
  induction g using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, isMultiHomog_C a, by simp⟩
  | add u v hu hv =>
    obtain ⟨d₁, H₁, h₁, m₁⟩ := hu
    obtain ⟨d₂, H₂, h₂, m₂⟩ := hv
    set M₁ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₁ k with hM₁
    set M₂ := ∏ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ d₂ k with hM₂
    refine ⟨d₁ + d₂, H₁ * M₂ + H₂ * M₁, isMultiHomog_add
      (isMultiHomog_mul h₁ (isMultiHomog_chartMonomial p d₂))
      (add_comm d₂ d₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMonomial p d₁)), ?_⟩
    have e : H₁ * M₂ + H₂ * M₁ - (u + v) =
        M₂ * (H₁ - u) + u * (M₂ - 1) + M₁ * (H₂ - v) + v * (M₁ - 1) := by ring
    rw [e]
    exact I.add_mem (I.add_mem (I.add_mem (I.mul_mem_left _ m₁) (I.mul_mem_left _ (hM d₂)))
      (I.mul_mem_left _ m₂)) (I.mul_mem_left _ (hM d₁))
  | mul_X u s hu =>
    obtain ⟨d, H, h, m⟩ := hu
    refine ⟨d + Pi.single s.1 1, H * X s, isMultiHomog_mul h (isMultiHomog_X s), ?_⟩
    have e : H * X s - u * X s = X s * (H - u) := by ring
    rw [e]
    exact I.mul_mem_left _ m

/- English proof (translation)
Rewrite using `[eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q = (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hf m hm k]`. Rewrite using `[h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval₂_smul {R : Type} [CommRing R] (g : ℂ →+* R) (c : K → R) (y : (Σ k, ι k) → R)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    eval₂ g (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval₂ g y f := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ q : (Σ k, ι k), (c q.1 * y q) ^ m q =
      (∏ k, c k ^ a k) * ∏ q : (Σ k, ι k), y q ^ m q := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [h1]; ring

def phi (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] :
    MvPolynomial (Σ k, ι k) ℂ →+* FractionRing (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
  (algebraMap (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) _).comp (Ideal.Quotient.mk Q)

/- English proof (translation)
Rewrite using `[phi, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `IsFractionRing.to_map_eq_zero_iff`.
-/
theorem phi_eq_zero_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (f : MvPolynomial (Σ k, ι k) ℂ) : phi Q f = 0 ↔ f ∈ Q := by
  rw [phi, RingHom.comp_apply, ← Ideal.Quotient.eq_zero_iff_mem]
  exact IsFractionRing.to_map_eq_zero_iff

/- English proof (translation)
Establish `: phi Q = eval₂Hom ((phi Q).comp C) (fun q => phi Q (X q))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Introduce `q`.

Simplify using the standard rewrite rules. Conclude with `DFunLike.congr_fun this f`.
-/
theorem phi_eq_eval₂ (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    phi Q f = eval₂ ((phi Q).comp C) (fun q => phi Q (X q)) f := by
  have : phi Q = eval₂Hom ((phi Q).comp C) (fun q => phi Q (X q)) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro q; simp
  exact DFunLike.congr_fun this f

def theta (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (p : (k : K) → ι k) :
    MvPolynomial (Σ k, ι k) ℂ →+* FractionRing (MvPolynomial (Σ k, ι k) ℂ ⧸ Q) :=
  eval₂Hom ((phi Q).comp C) (fun q => phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩))

/- English proof (translation)
Simplify using `[theta]`.
-/
theorem theta_X (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (p : (k : K) → ι k)
    (q : Σ k, ι k) : theta Q p (X q) = phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩) := by
  simp [theta]

/- English proof (translation)
Simplify using `[theta]`.
-/
theorem theta_C (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (p : (k : K) → ι k)
    (c : ℂ) : theta Q p (C c) = phi Q (C c) := by
  simp [theta]

/- English proof (translation)
Establish `hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0` using `fun k h => hp k ((phi_eq_zero_iff Q _).1 h)`. Establish `h` using `eval₂_smul ((phi Q).comp C) (fun k => phi Q (X ⟨k, p k⟩)) (fun q => phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩)) hf`. Establish `h2 : (fun q : Σ k, ι k => phi Q (X ⟨q.1, p q.1⟩) * (phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩))) = fun q => phi Q (X q)`. Use function extensionality and compare the values at `q`. Conclude with `mul_div_cancel₀ _ (hx q.1)`.

Rewrite `h` using `[h2, ← phi_eq_eval₂]`. Conclude with `h`.
-/
theorem phi_eq_prod_mul_theta (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    phi Q f = (∏ k, phi Q (X ⟨k, p k⟩) ^ a k) * theta Q p f := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have h := eval₂_smul ((phi Q).comp C) (fun k => phi Q (X ⟨k, p k⟩))
    (fun q => phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩)) hf
  have h2 : (fun q : Σ k, ι k => phi Q (X ⟨q.1, p q.1⟩) * (phi Q (X q) / phi Q (X ⟨q.1, p q.1⟩))) =
      fun q => phi Q (X q) := by
    funext q
    exact mul_div_cancel₀ _ (hx q.1)
  rw [h2, ← phi_eq_eval₂] at h
  exact h

/- English proof (translation)
Establish `hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0` using `fun k h => hp k ((phi_eq_zero_iff Q _).1 h)`. Establish `hprod : (∏ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hx k)`. Rewrite using `[← phi_eq_zero_iff Q f, phi_eq_prod_mul_theta Q p hp hf]`. Simplify using `[hprod]`.
-/
theorem theta_eq_zero_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ} (hf : IsMultiHomog f a) :
    theta Q p f = 0 ↔ f ∈ Q := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hprod : (∏ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ^ a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hx k)
  rw [← phi_eq_zero_iff Q f, phi_eq_prod_mul_theta Q p hp hf]
  simp [hprod]

/- English proof (translation)
Establish `hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0` using `fun k h => hp k ((phi_eq_zero_iff Q _).1 h)`. Establish `hQk : Q ≤ RingHom.ker (theta Q p)`. Take `⟨S, hS, hQS⟩` from `hQ`. Establish `hSQ : S ⊆ Q` using `fun f hf => hQS ▸ Ideal.subset_span hf`. Use `conv_lhs => rw [hQS]`.

Rewrite using `[Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Conclude with `RingHom.mem_ker.2 ((theta_eq_zero_iff Q p hp ha).2 (hSQ hf))`. Establish `hgen : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ RingHom.ker (theta Q p)`.

Introduce `k`. Rewrite using `[RingHom.mem_ker, map_sub, map_one, theta_X, div_self (hx k), sub_self]`. Establish `hle : chartIdeal Q p ≤ RingHom.ker (theta Q p)`. Use `sup_le hQk ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hgen k`. Use `le_antisymm ?_ hle` and prove the remaining obligations. Introduce `g hg`. Establish `hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal Q p` using `fun k => Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)`.

Take `⟨d, H, hH, hm⟩` from `exists_form p (chartIdeal Q p) hI g`. Establish `hθ : theta Q p H = 0`. Establish `h1` using `RingHom.mem_ker.1 (hle hm)`. Rewrite `h1` using `[map_sub, RingHom.mem_ker.1 hg, sub_zero]`. Conclude with `h1`.

Establish `hHQ : H ∈ chartIdeal Q p` using `Ideal.mem_sup_left ((theta_eq_zero_iff Q p hp hH).1 hθ)`. Use `Ideal.sub_mem _ hHQ hm` as an intermediate fact. Simplify using `using this`.
-/
theorem ker_theta (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime] (hQ : IsMultiHomogIdeal Q)
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
    RingHom.ker (theta Q p) = chartIdeal Q p := by
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hQk : Q ≤ RingHom.ker (theta Q p) := by
    obtain ⟨S, hS, hQS⟩ := hQ
    have hSQ : S ⊆ Q := fun f hf => hQS ▸ Ideal.subset_span hf
    conv_lhs => rw [hQS]
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact RingHom.mem_ker.2 ((theta_eq_zero_iff Q p hp ha).2 (hSQ hf))
  have hgen : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ RingHom.ker (theta Q p) := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one, theta_X, div_self (hx k), sub_self]
  have hle : chartIdeal Q p ≤ RingHom.ker (theta Q p) := by
    refine sup_le hQk ?_
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    exact hgen k
  refine le_antisymm ?_ hle
  intro g hg
  have hI : ∀ k, (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal Q p := fun k =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨d, H, hH, hm⟩ := exists_form p (chartIdeal Q p) hI g
  have hθ : theta Q p H = 0 := by
    have h1 := RingHom.mem_ker.1 (hle hm)
    rw [map_sub, RingHom.mem_ker.1 hg, sub_zero] at h1
    exact h1
  have hHQ : H ∈ chartIdeal Q p :=
    Ideal.mem_sup_left ((theta_eq_zero_iff Q p hp hH).1 hθ)
  have := Ideal.sub_mem _ hHQ hm
  simpa using this

/- English proof (translation)
Establish `hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0` using `fun k h => hp k ((phi_eq_zero_iff Q _).1 h)`. Establish `hren : ∀ g : MvPolynomial (Σ k, ι k) ℂ, (renR (Σ k, ι k)).symm (renR (Σ k, ι k) g) = g` using `(renR (Σ k, ι k)).symm_apply_apply`. Establish `: ((theta Q p).comp ((renR (Σ k, ι k)).symm : _ →+* _)).comp (bind₁ (SncRes.lift p)).toRingHom = theta Q p`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Establish `e : (renR (Σ k, ι k)) (C r) = C r` using `by simp [renameEquiv_apply]`. Establish `e2 : (bind₁ (SncRes.lift p)) (C r : MvPolynomial (Σ k, ι k) ℂ) = C r` using `by simp`. Use `show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (C r))) = _`. Rewrite using `[e2, ← e, hren]`. Introduce `q show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (X q))) = _`.

Rewrite using `[bind₁_X_right, SncRes.lift]`. Use `split_ifs with h`. Take `⟨k, i⟩` from `q`. Simplify using `only at h`. Substitute `h` using the available equality.

Rewrite using `[map_one, map_one, theta_X, div_self (hx k)]`. Establish `e : X (Fintype.equivFin (Σ k, ι k) q) = renR (Σ k, ι k) (X q)`. Simplify using `[renameEquiv_apply]`. Rewrite using `[e, hren]`. Conclude with `DFunLike.congr_fun this f`.
-/
theorem theta_symm_bind₁ (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) [Q.IsPrime]
    (p : (k : K) → ι k) (hp : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) :
    theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) f)) = theta Q p f := by
  classical
  have hx : ∀ k, phi Q (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ≠ 0 := fun k h =>
    hp k ((phi_eq_zero_iff Q _).1 h)
  have hren : ∀ g : MvPolynomial (Σ k, ι k) ℂ,
      (renR (Σ k, ι k)).symm (renR (Σ k, ι k) g) = g := (renR (Σ k, ι k)).symm_apply_apply
  have : ((theta Q p).comp ((renR (Σ k, ι k)).symm : _ →+* _)).comp
      (bind₁ (SncRes.lift p)).toRingHom = theta Q p := by
    apply MvPolynomial.ringHom_ext
    · intro r
      have e : (renR (Σ k, ι k)) (C r) = C r := by simp [renameEquiv_apply]
      have e2 : (bind₁ (SncRes.lift p)) (C r : MvPolynomial (Σ k, ι k) ℂ) = C r := by simp
      show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (C r))) = _
      rw [e2, ← e, hren]
    · intro q
      show theta Q p ((renR (Σ k, ι k)).symm (bind₁ (SncRes.lift p) (X q))) = _
      rw [bind₁_X_right, SncRes.lift]
      split_ifs with h
      · obtain ⟨k, i⟩ := q
        simp only at h
        subst h
        rw [map_one, map_one, theta_X, div_self (hx k)]
      · have e : X (Fintype.equivFin (Σ k, ι k) q) = renR (Σ k, ι k) (X q) := by
          simp [renameEquiv_apply]
        rw [e, hren]
  exact DFunLike.congr_fun this f

/- English proof (translation)
Introduce `hQ hprime hp`. Establish `hker` using `ker_theta Q hQ p hp`. Use `⟨?_, fun f a hf => ?_⟩` and prove the remaining obligations. Establish `h1 : (chartIdeal Q p).IsPrime` using `hker ▸ RingHom.ker_isPrime (theta Q p)`. Conclude with `Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))`.

Rewrite using `[SncRes.ideal, mem_map_renR_iff, ← hker, RingHom.mem_ker, theta_symm_bind₁ Q p hp, theta_eq_zero_iff Q p hp hf]`.
-/
theorem ideal_isPrime_and_mem_iff (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) →
      (SncRes.ideal Q p).IsPrime ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
        (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
  intro hQ hprime hp
  have hker := ker_theta Q hQ p hp
  refine ⟨?_, fun f a hf => ?_⟩
  · have h1 : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (theta Q p)
    exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
  · rw [SncRes.ideal, mem_map_renR_iff, ← hker, RingHom.mem_ker, theta_symm_bind₁ Q p hp,
      theta_eq_zero_iff Q p hp hf]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dict
