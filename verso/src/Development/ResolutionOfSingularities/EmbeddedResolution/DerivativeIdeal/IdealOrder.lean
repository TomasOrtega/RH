import Mathlib

namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

noncomputable def idealOrder (I : Ideal R) : ℕ∞ :=
  sSup ((fun n : ℕ => (n : ℕ∞)) '' {n : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ n})

/- English proof (authored)
If I is contained in the n-th power of the maximal ideal, then n occurs in the set defining its order and hence is at most the supremum. Conversely, if that containment fails, n is positive because the zeroth power is the unit ideal. The powers are decreasing, so every exponent for which containment holds is less than n. Their supremum is at most n − 1, contradicting the assumed lower bound.
-/
theorem le_idealOrder_iff (I : Ideal R) (n : ℕ) :
    (n : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by
  have hdef : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  constructor
  · intro h
    by_contra hI
    rw [hdef] at h
    have hn : n ≠ 0 := by
      rintro rfl
      apply hI
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    have hsup : sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k})
        ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro x ⟨k, hk, rfl⟩
      have hk' : I ≤ IsLocalRing.maximalIdeal R ^ k := hk
      have hkn : k < n := by
        by_contra hkn
        push Not at hkn
        exact hI (le_trans hk' (Ideal.pow_le_pow_right hkn))
      have hk2 : k ≤ n - 1 := by omega
      show (k : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞)
      exact_mod_cast hk2
    have hcon : n ≤ n - 1 := by exact_mod_cast h.trans hsup
    omega
  · intro h
    rw [hdef]
    exact le_sSup ⟨n, h, rfl⟩

/- English proof (authored)
An extended natural number is infinite exactly when it is at least every natural number. Apply the finite-exponent criterion to each such lower bound to get the equivalent ideal containments.
-/
theorem idealOrder_eq_top_iff (I : Ideal R) :
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by
  constructor
  · intro h n
    rw [← le_idealOrder_iff, h]
    exact le_top
  · intro h
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (le_idealOrder_iff I n).mpr (h n)

/- English proof (authored)
Apply the finite-exponent criterion at one. The first power of the maximal ideal is the maximal ideal itself.
-/
theorem one_le_idealOrder_iff (I : Ideal R) :
    1 ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R := by
  have h := le_idealOrder_iff I 1
  rw [Nat.cast_one, pow_one] at h
  exact h

/- English proof (authored)
Order at least one is equivalent to containment in the maximal ideal. Every proper ideal of a local ring lies in the maximal ideal, and any ideal contained there is proper. This gives the equivalence.
-/
theorem one_le_idealOrder_iff_ne_top (I : Ideal R) :
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by
  rw [one_le_idealOrder_iff]
  constructor
  · intro h hI
    rw [hI] at h
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp h)
  · intro h
    exact IsLocalRing.le_maximalIdeal h

/- English proof (authored)
An extended natural number is zero exactly when it is less than one. By the order-one criterion, failure of order at least one is equivalent to failure of containment in the maximal ideal.
-/
theorem idealOrder_eq_zero_iff (I : Ideal R) :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by
  rw [← one_le_idealOrder_iff, not_le, Order.lt_one_iff]

/- English proof (authored)
The unit ideal is not contained in the proper maximal ideal, so the order-zero criterion gives order zero.
-/
theorem idealOrder_top : idealOrder (⊤ : Ideal R) = 0 := by
  by_contra h
  have h1 : (1 : ℕ∞) ≤ idealOrder (⊤ : Ideal R) := by
    rw [Order.one_le_iff_ne_zero]
    exact h
  rw [one_le_idealOrder_iff_ne_top] at h1
  exact h1 rfl

/- English proof (authored)
The zero ideal is contained in every power of the maximal ideal. The criterion for infinite order therefore applies.
-/
theorem idealOrder_bot : idealOrder (⊥ : Ideal R) = ⊤ := by
  rw [idealOrder_eq_top_iff]
  intro n
  exact bot_le

/- English proof (authored)
If the order were infinite, the ideal would lie in every power of the maximal ideal. Their intersection is zero by the Krull intersection theorem for Noetherian local rings. This would make the ideal zero, contrary to the hypothesis.
-/
theorem idealOrder_ne_top_of_ne_bot [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    idealOrder I ≠ ⊤ := by
  intro h
  rw [idealOrder_eq_top_iff] at h
  have key : (⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hle : I ≤ ⊥ := by
    rw [← key]
    exact le_iInf h
  exact hI (le_bot_iff.mp hle)

/- English proof (authored)
A nonzero ideal of a Noetherian local ring has order different from infinity by the Krull intersection argument. Every finite extended natural number is represented by an ordinary natural number.
-/
theorem exists_idealOrder_eq_coe [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ n : ℕ, idealOrder I = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (idealOrder_ne_top_of_ne_bot hI)
  exact ⟨n, hn.symm⟩

/- English proof (authored)
If a power of the maximal ideal contains J, it also contains I because I is contained in J. The set of exponents defining the order of J is therefore contained in the set defining the order of I. Taking suprema gives the inequality.
-/
theorem idealOrder_le_of_le {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by
  have hI : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  have hJ : idealOrder J
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | J ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  rw [hI, hJ]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  have hn' : I ≤ IsLocalRing.maximalIdeal R ^ n := le_trans h hn
  exact le_sSup ⟨n, hn', rfl⟩

/- English proof (authored)
The sum of the ideals is contained in a given power of the maximal ideal exactly when both summands are contained in that power. Thus an ordinary exponent is at most the order of the sum precisely when it is at most both individual orders. These finite lower bounds determine the extended order, so it is the minimum.
-/
theorem idealOrder_sup (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by
  apply le_antisymm
  · exact le_min (idealOrder_le_of_le (le_sup_left : I ≤ I ⊔ J))
      (idealOrder_le_of_le (le_sup_right : J ≤ I ⊔ J))
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [le_min_iff] at hn
    rw [le_idealOrder_iff]
    exact sup_le ((le_idealOrder_iff I n).mp hn.1) ((le_idealOrder_iff J n).mp hn.2)

/- English proof (authored)
If either a or b is infinite, take the finite bound on that argument arbitrarily large and take zero on the other. The hypothesis then makes c infinite, giving the inequality. If both are finite, take their actual values as m and n and apply the hypothesis.
-/
private theorem enat_add_le_of_forall_natCast_add_le {a b c : ℕ∞}
    (h : ∀ m n : ℕ, (m : ℕ∞) ≤ a → (n : ℕ∞) ≤ b → ((m + n : ℕ) : ℕ∞) ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h n 0 le_top (by simp)
      simpa using hn
    rw [hc]
    exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h 0 n (by simp) le_top
      simpa using hn
    rw [hc]
    exact le_top
  lift a to ℕ using ha
  lift b to ℕ using hb
  have hab := h a b le_rfl le_rfl
  simpa using hab

/- English proof (authored)
For any finite m and n bounded by the orders of I and J, the two ideals lie in the corresponding powers of the maximal ideal. Their product therefore lies in the power with exponent m + n. Hence every such sum is bounded by the order of the product. The extended-natural addition criterion gives the inequality.
-/
theorem add_idealOrder_le_idealOrder_mul (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by
  refine enat_add_le_of_forall_natCast_add_le (fun m n hm hn => ?_)
  rw [le_idealOrder_iff] at hm hn ⊢
  rw [pow_add]
  exact Ideal.mul_mono hm hn

/- English proof (authored)
For exponent zero the lower bound is zero. For a positive exponent, if I has infinite order then its power is contained in I and also has infinite order. If the order of I is finite, say n, then I lies in the n-th power of the maximal ideal. Taking c-th powers yields containment in the power with exponent cn, which gives the bound.
-/
theorem mul_idealOrder_le_idealOrder_pow (I : Ideal R) (c : ℕ) :
    (c : ℕ∞) * idealOrder I ≤ idealOrder (I ^ c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_mul]
    exact zero_le
  · have hc1 : 1 ≤ c := hc
    rcases eq_or_ne (idealOrder I) ⊤ with hI | hI
    · have hIall : ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n :=
        (idealOrder_eq_top_iff I).mp hI
      have htop : idealOrder (I ^ c) = ⊤ := by
        rw [idealOrder_eq_top_iff]
        intro n
        have h1 : I ^ c ≤ I ^ 1 := Ideal.pow_le_pow_right hc1
        rw [pow_one] at h1
        exact le_trans h1 (hIall n)
      rw [htop]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hI
      have hIk : I ≤ IsLocalRing.maximalIdeal R ^ k := (le_idealOrder_iff I k).mp hk.le
      rw [← hk, ← Nat.cast_mul, le_idealOrder_iff]
      calc I ^ c ≤ (IsLocalRing.maximalIdeal R ^ k) ^ c :=
            Ideal.pow_right_mono hIk c
        _ = IsLocalRing.maximalIdeal R ^ (c * k) := by rw [← pow_mul, mul_comm k c]

/- English proof (authored)
Extension of ideals commutes with ideal products. For exponent zero the inequality is automatic because the target is the unit ideal. At a successor use the product formula, the previous inequality for the lower power, and the assumed containment for the image of the maximal ideal.
-/
private theorem map_maximalIdeal_pow_le_pow (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (n : ℕ) :
    ((IsLocalRing.maximalIdeal R) ^ n).map f ≤ (IsLocalRing.maximalIdeal S) ^ n := by
  induction n with
  | zero =>
      have hS : (IsLocalRing.maximalIdeal S) ^ 0 = (⊤ : Ideal S) := by
        rw [pow_zero, Ideal.one_eq_top]
      rw [hS]
      exact le_top
  | succ n ih =>
      rw [pow_succ, pow_succ, Ideal.map_mul]
      exact Ideal.mul_mono ih hf

/- English proof (authored)
Take any finite exponent bounded by the order of I. Extend the containment of I in that power of the source maximal ideal. The image of this power lies in the corresponding power of the target maximal ideal, so the same exponent is bounded by the order of the extended ideal. Comparing all finite lower bounds gives the claim.
-/
theorem idealOrder_le_idealOrder_map (f : R →+* S)
    (hf : (IsLocalRing.maximalIdeal R).map f ≤ IsLocalRing.maximalIdeal S) (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map f) := by
  refine ENat.forall_natCast_le_iff_le.mp (fun n hn => ?_)
  rw [le_idealOrder_iff] at hn ⊢
  exact le_trans (Ideal.map_mono hn) (map_maximalIdeal_pow_le_pow f hf n)

end FunctorialResolution.EmbeddedResolution
