import Mathlib

namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion

section

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/- English proof (authored)
Induct on the number of applications. The formula at zero has only the original product. At each successor, apply additivity and the Leibniz rule to every term. Each term produces one term with an extra derivative on the first factor and one with an extra derivative on the second. In the interior, Pascal’s identity combines the two neighboring coefficients. The two endpoint products have coefficient one. This proves the iterated product rule with coefficients acting by repeated addition.
-/
private theorem iterate_deriv_mul_eq_sum_nsmul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∀ i : ℕ,
        ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g))
          = n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      intro i
      rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        ← Function.iterate_succ_apply' (⇑D) (n - i) g,
        ← Function.iterate_succ_apply' (⇑D) i f,
        mul_comm ((⇑D)^[n - i] g) ((⇑D)^[i + 1] f), smul_add]
    have e3 : ∑ i ∈ Finset.range (n + 1), n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)
        = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), zero_smul,
        add_zero]
    have e1 : ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
        = (∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner : ∑ i ∈ Finset.range n,
            n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - (i + 1) + 1] g)
          = ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have h := Finset.mem_range.mp hi
        have hi' : n - (i + 1) + 1 = n - i := by omega
        rw [hi']
      rw [Finset.sum_range_succ', inner]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    have e2 : ∑ i ∈ Finset.range (n + 1 + 1),
          (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g)
        = ((∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
          + f * (⇑D)^[n + 1] g := by
      have inner2 : ∑ i ∈ Finset.range (n + 1),
            (n + 1).choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n + 1 - (i + 1)] g)
          = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g))
            + ∑ i ∈ Finset.range n, n.choose (i + 1) • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) := by
        rw [← e3, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hc : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) :=
          Nat.choose_succ_succ n i
        have hs : n + 1 - (i + 1) = n - i := by omega
        rw [hc, hs, add_smul]
      rw [Finset.sum_range_succ', inner2]
      simp only [Nat.choose_zero_right, one_smul, Function.iterate_zero_apply, Nat.sub_zero]
    calc (⇑D)^[n + 1] (f * g)
        = ⇑D ((⇑D)^[n] (f * g)) := Function.iterate_succ_apply' _ _ _
      _ = ⇑D (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [ih]
      _ = ∑ i ∈ Finset.range (n + 1), ⇑D (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i] g)) := by
            rw [map_sum]
      _ = ∑ i ∈ Finset.range (n + 1), (n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g)
            + n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g)) :=
            Finset.sum_congr rfl fun i _ => key i
      _ = (∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i] f * (⇑D)^[n - i + 1] g))
            + ∑ i ∈ Finset.range (n + 1), n.choose i • ((⇑D)^[i + 1] f * (⇑D)^[n - i] g) :=
            Finset.sum_add_distrib
      _ = ∑ i ∈ Finset.range (n + 1 + 1),
            (n + 1).choose i • ((⇑D)^[i] f * (⇑D)^[n + 1 - i] g) := by
            rw [e1, e2]; ring

/- English proof (authored)
In the repeated-addition formula, an integer count acting on a ring element is multiplication by its image in the ring. Replace each repeated-addition coefficient by that scalar factor.
-/
theorem iterate_deriv_mul (D : Derivation A R R) (n : ℕ) (f g : R) :
    (⇑D)^[n] (f * g) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) * ((⇑D)^[i] f * (⇑D)^[n - i] g) := by
  rw [iterate_deriv_mul_eq_sum_nsmul D n f g]
  exact Finset.sum_congr rfl fun i _ => by rw [nsmul_eq_mul]

end

section

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]

def coeff (σ : R →+* S) (D : Derivation A R R) (i : ℕ) (f : R) : S :=
  algebraMap ℚ S ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f)

def truncatedSeries (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) : S :=
  ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j

@[simp]
/- English proof (authored)
By definition the truncated series is the sum over degrees below N, with coefficient the image of the iterated derivative divided by its factorial, multiplied by the corresponding power of β.
-/
theorem truncatedSeries_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f : R) :
    truncatedSeries σ D β N f =
      ∑ j ∈ Finset.range N, algebraMap ℚ S ((j.factorial : ℚ)⁻¹) * σ ((⇑D)^[j] f) * β ^ j :=
  rfl

/- English proof (authored)
All positive iterates of D on f vanish because the first is zero and D fixes zero. Since N is positive, the sum contains the constant term. This is the only term left, and it equals σ(f).
-/
theorem truncatedSeries_of_deriv_eq_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) (hf : D f = 0) : truncatedSeries σ D β N f = σ f := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  have key : ∀ k : ℕ, (⇑D)^[k + 1] f = 0 := by
    intro k
    rw [Function.iterate_succ_apply, hf]
    exact Function.iterate_fixed hz k
  rw [truncatedSeries_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb0
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb0
    rw [key k]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : 0 < N)) h

/- English proof (authored)
Subtracting σ(f) removes the degree-zero term since N is positive. Every remaining term has a positive power of β, hence has β as a factor. Their sum lies in the principal ideal generated by β.
-/
theorem truncatedSeries_sub_mem_span_singleton (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (hN : 1 ≤ N) (f : R) :
    truncatedSeries σ D β N f - σ f ∈ Ideal.span ({β} : Set S) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos hN).symm⟩
  have key : truncatedSeries σ D β (M + 1) f - σ f =
      ∑ j ∈ Finset.range M,
        algebraMap ℚ S (((j + 1).factorial : ℚ)⁻¹) * σ ((⇑D)^[j + 1] f) * β ^ (j + 1) := by
    rw [truncatedSeries_apply, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Ideal.mem_span_singleton]
  exact dvd_mul_of_dvd_right (dvd_pow_self β j.succ_ne_zero) _

/- English proof (authored)
Start with the binomial identity that the coefficient times the two factorials of the split sizes equals the factorial of j. The factorials are nonzero in the rationals, so dividing by their product and by the factorial of j gives the equation there. Apply the algebra map to the target ring.
-/
private theorem factorial_inv_mul_choose {S' : Type*} [CommRing S'] [Algebra ℚ S'] (j i : ℕ)
    (h : i ≤ j) :
    algebraMap ℚ S' ((j.factorial : ℚ)⁻¹) * (j.choose i : S')
      = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * algebraMap ℚ S' (((j - i).factorial : ℚ)⁻¹) := by
  have hj : ((j.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos j).ne'
  have hi : ((i.factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos i).ne'
  have hji : (((j - i).factorial : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos (j - i)).ne'
  have h1 : (j.choose i : ℚ) * (i.factorial : ℚ) * ((j - i).factorial : ℚ)
      = (j.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  have key : ((j.factorial : ℚ))⁻¹ * (j.choose i : ℚ)
      = ((i.factorial : ℚ))⁻¹ * (((j - i).factorial : ℚ))⁻¹ := by
    field_simp
    linear_combination h1
  have h2 := congrArg (algebraMap ℚ S') key
  simpa only [map_mul, map_natCast] using h2

/- English proof (authored)
The coefficient is defined as the image of the iterated derivative multiplied by the image of the inverse factorial.
-/
private theorem coeff_eq {A' R' S' : Type*} [CommRing A'] [CommRing R'] [CommRing S']
    [Algebra A' R'] [Algebra ℚ S'] (σ : R' →+* S') (D : Derivation A' R' R') (i : ℕ) (f : R') :
    coeff σ D i f = algebraMap ℚ S' ((i.factorial : ℚ)⁻¹) * σ ((⇑D)^[i] f) := rfl

/- English proof (authored)
At each degree j expand the derivative of the product by the iterated Leibniz rule. The ring map transports this sum and its products to S. For each split i and j − i, the binomial coefficient divided by j factorial becomes the product of the inverses of the two split factorials. Thus the coefficient of β to the j-th power is the sum of products of the two individual Taylor coefficients.
-/
theorem truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f * g) =
      ∑ j ∈ Finset.range N,
        β ^ j * ∑ i ∈ Finset.range (j + 1),
          coeff σ D i f * coeff σ D (j - i) g := by
  rw [truncatedSeries_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iterate_deriv_mul D j f g, map_sum, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have key := factorial_inv_mul_choose (S' := S) j i hij
  simp only [coeff_eq, map_mul, map_natCast]
  linear_combination (σ ((⇑D)^[i] f) * σ ((⇑D)^[j - i] g) * β ^ j) * key

/- English proof (authored)
Every iterate of D sends zero to zero, including the identity iterate. Each term is consequently zero after applying σ, so the sum vanishes.
-/
theorem truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) :
    truncatedSeries σ D β N 0 = 0 := by
  have hz : (⇑D) (0 : R) = 0 := by simp
  rw [truncatedSeries_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Function.iterate_fixed hz j]
  simp

/- English proof (authored)
Every iterate of the additive derivation preserves addition. Apply this to every coefficient and use additivity of σ, then distribute the scalar factors and split the finite sum.
-/
theorem truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (f g : R) :
    truncatedSeries σ D β N (f + g) = truncatedSeries σ D β N f + truncatedSeries σ D β N g := by
  have key : ∀ j : ℕ, (⇑D)^[j] (f + g) = (⇑D)^[j] f + (⇑D)^[j] g := by
    intro j
    induction j with
    | zero => simp
    | succ k ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]
  simp only [truncatedSeries_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j, map_add]
  ring

/- English proof (authored)
Every derivation kills one. The series of an element killed by the derivation equals its constant term when N is positive, and σ sends one to one.
-/
theorem truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (hN : 1 ≤ N) :
    truncatedSeries σ D β N 1 = 1 := by
  have h1 : D (1 : R) = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1, map_one]

/- English proof (authored)
Both sums run over pairs with 0 ≤ i ≤ j < N. The first groups by the larger index j, and the second groups by the smaller index i. Equivalently, increasing N adds the same terms with j equal to the old bound on both sides.
-/
private theorem sum_range_sum_range_succ_eq_sum_sum_Ico {T : Type*} [AddCommMonoid T] (N : ℕ) (h : ℕ → ℕ → T) :
    ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hL : ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (j + 1), h i j
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), h i j)
          + ∑ i ∈ Finset.range (N + 1), h i N :=
      Finset.sum_range_succ (fun j => ∑ i ∈ Finset.range (j + 1), h i j) N
    have hR1 : ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j)
          + ∑ j ∈ Finset.Ico N (N + 1), h N j :=
      Finset.sum_range_succ (fun i => ∑ j ∈ Finset.Ico i (N + 1), h i j) N
    have hR2 : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i (N + 1), h i j
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico i N, h i j)
          + ∑ i ∈ Finset.range N, h i N := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hiN : i ≤ N := le_of_lt (Finset.mem_range.mp hi)
      exact Finset.sum_Ico_succ_top hiN (fun j => h i j)
    have hR3 : ∑ j ∈ Finset.Ico N (N + 1), h N j = h N N := by
      rw [Finset.sum_Ico_succ_top (le_refl N) (fun j => h N j), Finset.Ico_self,
        Finset.sum_empty, zero_add]
    have hlast : ∑ i ∈ Finset.range (N + 1), h i N
        = (∑ i ∈ Finset.range N, h i N) + h N N :=
      Finset.sum_range_succ (fun i => h i N) N
    rw [hL, hR1, hR2, hR3, ih, hlast, add_assoc]

/- English proof (authored)
Set j = i + k. The interval from i up to, but excluding, N corresponds to 0 ≤ k < N − i, and j − i becomes k. This changes the summand to exactly the one on the right.
-/
private theorem sum_Ico_mul_pow_eq_sum_range {T : Type*} [CommRing T] (a b : ℕ → T) (β : T) (N i : ℕ) :
    ∑ j ∈ Finset.Ico i N, a i * b (j - i) * β ^ j
      = ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : i + k - i = k := by omega
  simp only [hk]

/- English proof (authored)
Expand the product of the two truncated sums into terms indexed by pairs i,k each below N. The convolution sum uses precisely the pairs with i + k < N, by setting the total degree to i + k. Their difference is the negative of the terms with i + k at least N. Each of those terms contains β to a power at least N and hence is a multiple of β to the N-th power. They all lie in J, as does their signed sum.
-/
private theorem sum_convolution_sub_mul_mem {T : Type*} [CommRing T] (β : T) (N : ℕ) (J : Ideal T)
    (hβ : β ^ N ∈ J) (a b : ℕ → T) :
    (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      - (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j) ∈ J := by
  have hprod : (∑ j ∈ Finset.range N, a j * β ^ j) * (∑ j ∈ Finset.range N, b j * β ^ j)
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have htri : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
      = ∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k) := by
    have e1 : (∑ j ∈ Finset.range N, β ^ j * ∑ i ∈ Finset.range (j + 1), a i * b (j - i))
        = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (j + 1), a i * b (j - i) * β ^ j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine e1.trans ((sum_range_sum_range_succ_eq_sum_sum_Ico N (fun i j => a i * b (j - i) * β ^ j)).trans ?_)
    exact Finset.sum_congr rfl fun i _ => sum_Ico_mul_pow_eq_sum_range a b β N i
  have hdist : (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - (∑ i ∈ Finset.range N, ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k))
      = ∑ i ∈ Finset.range N, ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
          - ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)) := by
    refine (eq_sub_of_add_eq ?_).symm
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hprod, htri, hdist]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hiN : i < N := Finset.mem_range.mp hi
  have hsplit : ∑ k ∈ Finset.range N, a i * b k * β ^ (i + k)
      = (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le (N - i)) (Nat.sub_le N i)).symm
  rw [hsplit]
  have hre : (∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
      - ((∑ k ∈ Finset.range (N - i), a i * b k * β ^ (i + k))
        + ∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k))
      = -(∑ k ∈ Finset.Ico (N - i) N, a i * b k * β ^ (i + k)) := by ring
  rw [hre]
  refine neg_mem (Ideal.sum_mem _ fun k hk => ?_)
  have hk1 : N - i ≤ k := (Finset.mem_Ico.mp hk).1
  have hpow : β ^ (i + k) ∈ J := by
    have he : i + k = N + (i + k - N) := by omega
    rw [he, pow_add]
    exact Ideal.mul_mem_right _ _ hβ
  exact Ideal.mul_mem_left _ _ hpow

/- English proof (authored)
Use the convolution formula for the Taylor series of the product and express each individual Taylor series as the sum of its coefficients times powers of β. The difference is the convolution error, which belongs to J because β to the N-th power does.
-/
theorem truncatedSeries_mul_sub_mem (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    truncatedSeries σ D β N (f * g) - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J := by
  have hf : truncatedSeries σ D β N f
      = ∑ j ∈ Finset.range N, coeff σ D j f * β ^ j := rfl
  have hg : truncatedSeries σ D β N g
      = ∑ j ∈ Finset.range N, coeff σ D j g * β ^ j := rfl
  rw [truncatedSeries_mul σ D β N f g, hf, hg]
  exact sum_convolution_sub_mul_mem β N J hβ (fun i => coeff σ D i f)
    (fun i => coeff σ D i g)

/- English proof (authored)
The truncated series of one is one for positive N, and its class in the quotient is one.
-/
private theorem mk_truncatedSeries_one (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hN : 1 ≤ N) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 1) = 1 := by
  have h1 : D 1 = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1]
  simp

/- English proof (authored)
The difference between the truncated series of the product and the product of the two series lies in J. Their classes are therefore equal, and the quotient map carries a product to the product of its classes.
-/
private theorem mk_truncatedSeries_mul (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (hβ : β ^ N ∈ J) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) *
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  have h : truncatedSeries σ D β N (f * g)
      - truncatedSeries σ D β N f * truncatedSeries σ D β N g ∈ J :=
    truncatedSeries_mul_sub_mem σ D β N J hβ f g
  have h2 : Ideal.Quotient.mk J (truncatedSeries σ D β N (f * g))
      = Ideal.Quotient.mk J (truncatedSeries σ D β N f * truncatedSeries σ D β N g) :=
    Ideal.Quotient.eq.mpr h
  rw [h2, map_mul]

/- English proof (authored)
The truncated series of zero is zero, and its class in the quotient is zero.
-/
private theorem mk_truncatedSeries_zero (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N 0) = 0 := by
  rw [truncatedSeries_zero, map_zero]

/- English proof (authored)
The truncated series preserves addition. The quotient map also preserves addition, giving the displayed equality.
-/
private theorem mk_truncatedSeries_add (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ)
    (J : Ideal S) (f g : R) :
    Ideal.Quotient.mk J (truncatedSeries σ D β N (f + g)) =
      Ideal.Quotient.mk J (truncatedSeries σ D β N f) +
        Ideal.Quotient.mk J (truncatedSeries σ D β N g) := by
  rw [truncatedSeries_add, map_add]

def truncatedSeriesRingHom (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) : R →+* S ⧸ J :=
  { toFun := fun f => Ideal.Quotient.mk J (truncatedSeries σ D β N f)
    map_one' := mk_truncatedSeries_one σ D β N J hN
    map_mul' := mk_truncatedSeries_mul σ D β N J hβ
    map_zero' := mk_truncatedSeries_zero σ D β N J
    map_add' := mk_truncatedSeries_add σ D β N J }

@[simp]
/- English proof (authored)
The ring homomorphism is defined by evaluating the truncated series and taking its class modulo J. This gives its value at f.
-/
theorem truncatedSeriesRingHom_apply (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) (f : R) :
    truncatedSeriesRingHom σ D β N J hN hβ f = Ideal.Quotient.mk J (truncatedSeries σ D β N f) :=
  rfl

end

end FunctorialResolution.EmbeddedResolution.TaylorExpansion
