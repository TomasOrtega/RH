import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal

namespace FunctorialResolution.EmbeddedResolution

def tuningWeight (m : ℕ) (c : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range m, (m - j) * c j

/- English proof (authored)
The tuning weight is defined by summing each exponent below the mark multiplied by the mark minus its index. This is the displayed sum.
-/
theorem tuningWeight_eq_sum (m : ℕ) (c : ℕ → ℕ) :
    tuningWeight m c = ∑ j ∈ Finset.range m, (m - j) * c j := rfl

/- English proof (authored)
Distribute multiplication by each weight over the sum of the two exponents. Summing and grouping the contributions of the two exponent functions gives the two separate weights.
-/
theorem tuningWeight_fun_add (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by
  simp [tuningWeight, Nat.mul_add, Finset.sum_add_distrib]

/- English proof (authored)
Addition of exponent functions is pointwise. The weight of their sum is therefore the sum of their weights by the weighted-sum addition rule.
-/
theorem tuningWeight_add (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (c + d) = tuningWeight m c + tuningWeight m d :=
  tuningWeight_fun_add m c d

/- English proof (authored)
Each exponent is multiplied by the same scalar. Move that scalar outside each weighted term and then outside the finite sum, giving the corresponding multiple of the original weight.
-/
theorem tuningWeight_mul_left (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by
  simp [tuningWeight, Finset.mul_sum, Nat.mul_left_comm]

/- English proof (authored)
Natural-number scalar multiplication of exponent functions multiplies every exponent by that number. Apply the rule for pulling a common scalar out of the weighted sum.
-/
theorem tuningWeight_nsmul (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (n • c) = n * tuningWeight m c := by
  have : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this, tuningWeight_mul_left]

/- English proof (authored)
Only the chosen index has a nonzero exponent, namely one. Its contribution to the weighted sum is the mark minus that index.
-/
theorem tuningWeight_single (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningWeight m (Pi.single i 1) = m - i := by
  rw [tuningWeight_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

/- English proof (authored)
The empty range gives the identity for both products. Increasing the range by one appends the same factor to the list product and to the finite-set product, so induction gives equality.
-/
theorem listProd_map_range_eq_prod {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f (List.range m)).prod = ∏ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp

section

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tuningMonomial (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) : Ideal S :=
  ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j

/- English proof (authored)
The tuning monomial is defined as the product of the indicated powers of the derivative iterates. This gives the stated formula.
-/
theorem tuningMonomial_eq_prod (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j := rfl

/- English proof (authored)
Every exponent is zero, so each factor is the unit ideal. Their product is the unit ideal.
-/
theorem tuningMonomial_zero (J : Ideal S) (m : ℕ) :
    tuningMonomial k J m (fun _ => 0) = ⊤ := by
  simp [tuningMonomial_eq_prod, Ideal.one_eq_top]

/- English proof (authored)
Group factors with the same derivative index from the two products. Commutativity allows the grouping, and multiplying the corresponding powers adds their exponents. This gives the product for the pointwise sum.
-/
theorem tuningMonomial_mul_fun_add (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (fun j => c j + d j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (pow_add _ _ _).symm

/- English proof (authored)
The sum of the two exponent functions adds their values at each index. The product formula therefore gives the monomial for that sum.
-/
theorem tuningMonomial_mul (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (c + d) :=
  tuningMonomial_mul_fun_add k J m c d

/- English proof (authored)
Powers of a finite product in a commutative monoid distribute over its factors. A power of each individual ideal power multiplies the exponents. Reorder the two integer factors of the exponent to obtain the formula.
-/
private theorem prod_derivIdealIterate_pow_pow (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    (∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j) ^ n
      = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ (n * c j) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, mul_pow, ih, Finset.prod_range_succ, ← pow_mul,
        Nat.mul_comm (c m) n]

/- English proof (authored)
Expand the monomial as its product of derivative powers. Taking a power distributes over this finite product and multiplies each exponent by the power, giving the monomial for the scaled function.
-/
theorem tuningMonomial_pow_fun_mul (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (fun j => n * c j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod]
  exact prod_derivIdealIterate_pow_pow k J m n c

/- English proof (authored)
Natural-number scalar multiplication scales the exponent function at each index. The monomial for this function is the stated power by the product-of-powers formula.
-/
theorem tuningMonomial_pow (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (n • c) := by
  have h : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h, tuningMonomial_pow_fun_mul]

/- English proof (authored)
Each factor away from the selected index has exponent zero and equals the unit ideal. At the selected index the exponent is one, so the product gives that derivative iterate.
-/
theorem tuningMonomial_single (J : Ideal S) (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningMonomial k J m (Pi.single i 1) = derivIdealIterate k i J := by
  rw [tuningMonomial_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni

def tunedIdeal (J : Ideal S) (m s : ℕ) : Ideal S :=
  ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c

/- English proof (authored)
By definition the tuned ideal is the supremum of all tuning monomial ideals whose weights reach the stated threshold. The displayed supremum enumerates precisely those terms.
-/
theorem tunedIdeal_eq_iSup (J : Ideal S) (m s : ℕ) :
    tunedIdeal k J m s = ⨆ c : ℕ → ℕ, ⨆ _ : s ≤ tuningWeight m c, tuningMonomial k J m c := rfl

/- English proof (authored)
Since the exponent function meets the weight threshold, its monomial ideal occurs among the ideals defining the tuned ideal. Each such ideal is contained in their supremum.
-/
theorem tuningMonomial_le_tunedIdeal (J : Ideal S) (m s : ℕ) (c : ℕ → ℕ)
    (hc : s ≤ tuningWeight m c) : tuningMonomial k J m c ≤ tunedIdeal k J m s :=
  le_iSup_of_le c (le_iSup_of_le hc le_rfl)

/- English proof (authored)
Containment of the supremum implies containment of each contributing ideal. Conversely, if all ideals with qualifying weight lie in the target, their supremum lies there as well.
-/
theorem tunedIdeal_le_iff (J : Ideal S) (m s : ℕ) (K : Ideal S) :
    tunedIdeal k J m s ≤ K ↔ ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (tuningMonomial_le_tunedIdeal k J m s c hc) h
  · intro h
    exact iSup_le fun c => iSup_le fun hc => h c hc

/- English proof (authored)
The zero exponent function qualifies at threshold zero. Its product is the unit ideal, so the tuned ideal contains the unit ideal and is therefore equal to it.
-/
theorem tunedIdeal_zero (J : Ideal S) (m : ℕ) : tunedIdeal k J m 0 = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tuningMonomial_zero k J m]
  exact tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) (Nat.zero_le _)

/- English proof (authored)
Every exponent function admitted by the higher threshold also satisfies the lower threshold. The corresponding monomial is contained in the tuned ideal for the lower threshold. Take the supremum over the higher threshold.
-/
theorem tunedIdeal_antitone (J : Ideal S) (m : ℕ) {s t : ℕ} (h : s ≤ t) :
    tunedIdeal k J m t ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_le_iff]
  intro c hc
  exact tuningMonomial_le_tunedIdeal k J m s c (le_trans h hc)

/- English proof (authored)
Multiplication of ideals distributes over suprema, so it suffices to multiply one contributing monomial from each tuned ideal. Their product is the monomial with the pointwise sum of exponents. Its weight is the sum of their weights, hence at least the sum of the thresholds. The product is therefore contained in the target tuned ideal.
-/
theorem tunedIdeal_mul_le (J : Ideal S) (m s t : ℕ) :
    tunedIdeal k J m s * tunedIdeal k J m t ≤ tunedIdeal k J m (s + t) := by
  rw [tunedIdeal_eq_iSup, tunedIdeal_eq_iSup, Submodule.iSup_mul]
  refine iSup_le fun c => ?_
  rw [Submodule.iSup_mul]
  refine iSup_le fun hc => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun d => ?_
  rw [Submodule.mul_iSup]
  refine iSup_le fun hd => ?_
  rw [tuningMonomial_mul_fun_add]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_fun_add]
  exact Nat.add_le_add hc hd

/- English proof (authored)
An element of the sum of the two ideals is a sum of one element from each. Multiplying by an element of the common factor distributes over this sum. Both products belong to the target ideal by hypothesis, so their sum also belongs. Such products generate the left-hand ideal.
-/
private theorem mul_sup_le {R : Type*} [CommRing R] (B X Y T : Ideal R)
    (hX : B * X ≤ T) (hY : B * Y ≤ T) : B * (X ⊔ Y) ≤ T := by
  refine Ideal.mul_le.mpr ?_
  intro b hb z hz
  rcases Submodule.mem_sup.mp hz with ⟨x, hx, y, hy, rfl⟩
  rw [mul_add]
  exact Submodule.add_mem T (hX (Ideal.mul_mem_mul hb hx)) (hY (Ideal.mul_mem_mul hb hy))

/- English proof (authored)
The multiplicative identity for ideals is the unit ideal. The derivative ideal contains its input, so the derivative of the unit ideal is still the unit ideal.
-/
private theorem derivIdeal_one {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] : derivIdeal A (1 : Ideal R) = 1 := by
  rw [Ideal.one_eq_top]
  exact derivIdeal_top A

/- English proof (authored)
Separate the contribution at the chosen index from each weighted sum. The remaining terms are unchanged. The exponent at the chosen index is larger by one in the first function, so its contribution is larger by exactly the weight of that index.
-/
private theorem tuningWeight_eq_add_sub_of_succ (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) :
    tuningWeight m c = tuningWeight m d + (m - i) := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyc : tuningWeight m c
      = (m - i) * c i + ∑ j ∈ (Finset.range m).erase i, (m - j) * c j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * c j) hmem).symm
  have keyd : tuningWeight m d
      = (m - i) * d i + ∑ j ∈ (Finset.range m).erase i, (m - j) * d j := by
    rw [tuningWeight_eq_sum]
    exact (Finset.add_sum_erase (Finset.range m) (fun j => (m - j) * d j) hmem).symm
  have h3 : ∑ j ∈ (Finset.range m).erase i, (m - j) * d j
      = ∑ j ∈ (Finset.range m).erase i, (m - j) * c j :=
    Finset.sum_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyc, keyd, h3, ← hdi]
  ring

/- English proof (authored)
Separate the factor at the chosen index in each monomial. All other factors agree. The exponent at that index increases by one, so the changed factor is the original factor multiplied by the corresponding derivative iterate.
-/
private theorem tuningMonomial_eq_derivIdealIterate_mul_of_succ {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J : Ideal R) (m i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i = c i + 1) :
    tuningMonomial A J m d = derivIdealIterate A i J * tuningMonomial A J m c := by
  have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
  have keyd : tuningMonomial A J m d
      = derivIdealIterate A i J ^ d i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ d j) hmem).symm
  have keyc : tuningMonomial A J m c
      = derivIdealIterate A i J ^ c i *
        ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j := by
    rw [tuningMonomial_eq_prod]
    exact (Finset.mul_prod_erase (Finset.range m) (fun j => derivIdealIterate A j J ^ c j) hmem).symm
  have h3 : ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ d j
      = ∏ j ∈ (Finset.range m).erase i, derivIdealIterate A j J ^ c j :=
    Finset.prod_congr rfl fun j hj => by rw [hne j (Finset.ne_of_mem_erase hj)]
  rw [keyd, keyc, h3, hdi, pow_succ]
  simp only [mul_comm, mul_assoc]

/- English proof (authored)
Removing a copy of the factor at the chosen index reduces the total weight by its weight. If the next derivative index is still below the mark, adding one factor there raises the total by one less than the removed weight, so the new monomial loses exactly one unit of weight and qualifies at the desired threshold. If the next index is at least the mark, the removed weight was one. The remaining monomial already qualifies, and multiplying it by any ideal stays inside it.
-/
private theorem derivIdealIterate_succ_mul_tuningMonomial_le {A : Type*} [CommRing A] {R : Type*}
    [CommRing R] [Algebra A R] (J : Ideal R) (m s i : ℕ) (hi : i < m) (c d : ℕ → ℕ)
    (hne : ∀ j, j ≠ i → d j = c j) (hdi : d i + 1 = c i) (hc : s + 1 ≤ tuningWeight m c) :
    derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tunedIdeal A J m s := by
  have hw : tuningWeight m c = tuningWeight m d + (m - i) :=
    tuningWeight_eq_add_sub_of_succ m i hi c d hne hdi
  rcases Nat.lt_or_ge (i + 1) m with hlt | hge
  · have hmono : tuningMonomial A J m (fun j => if j = i + 1 then d j + 1 else d j)
        = derivIdealIterate A (i + 1) J * tuningMonomial A J m d :=
      tuningMonomial_eq_derivIdealIterate_mul_of_succ J m (i + 1) hlt d (fun j => if j = i + 1 then d j + 1 else d j)
        (fun j hj => by simp [hj]) (by simp)
    have hw' : tuningWeight m (fun j => if j = i + 1 then d j + 1 else d j)
        = tuningWeight m d + (m - (i + 1)) :=
      tuningWeight_eq_add_sub_of_succ m (i + 1) hlt (fun j => if j = i + 1 then d j + 1 else d j) d
        (fun j hj => by simp [hj]) (by simp)
    refine le_trans (le_of_eq hmono.symm)
      (tuningMonomial_le_tunedIdeal A J m s (fun j => if j = i + 1 then d j + 1 else d j) ?_)
    omega
  · have hle : derivIdealIterate A (i + 1) J * tuningMonomial A J m d ≤ tuningMonomial A J m d :=
      Ideal.mul_le.mpr fun r _ t ht => Ideal.mul_mem_left _ r ht
    refine le_trans hle (tuningMonomial_le_tunedIdeal A J m s d ?_)
    omega

/- English proof (authored)
Induct on the number of factors in the product. The empty product has unit derivative ideal, giving the first hypothesis directly. For a nonempty product, the Leibniz estimate bounds its derivative by the sum of the terms from differentiating the last factor and from differentiating the earlier product. In the last-factor term, exponent zero leaves the product unchanged and the first hypothesis applies. A positive exponent is reduced by one and accompanied by the next derivative ideal, by the power derivative estimate. This is one of the terms covered by the second hypothesis. For the earlier-product term, absorb the last factor into the fixed multiplier and apply induction. The hypotheses for the shorter product follow from the original ones because changes at earlier indices leave the last exponent unchanged. Adding the two containments gives the result.
-/
private theorem mul_derivIdeal_prod_le {A : Type*} [CommRing A] {R : Type*} [CommRing R]
    [Algebra A R] (J T : Ideal R) (c : ℕ → ℕ) :
    ∀ (n : ℕ) (B : Ideal R),
      B * (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T →
      (∀ i, i < n → ∀ d : ℕ → ℕ, (∀ j, j ≠ i → d j = c j) → d i + 1 = c i →
        B * (derivIdealIterate A (i + 1) J *
          ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ d j) ≤ T) →
      B * derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) ≤ T := by
  intro n
  induction n with
  | zero =>
      intro B h1 _
      rw [Finset.range_zero, Finset.prod_empty, derivIdeal_one, mul_one]
      rw [Finset.range_zero, Finset.prod_empty, mul_one] at h1
      exact h1
  | succ n ih =>
      intro B h1 h2
      rw [Finset.prod_range_succ] at h1
      rw [Finset.prod_range_succ]
      refine le_trans (Ideal.mul_mono le_rfl (derivIdeal_mul_le A _ _)) ?_
      refine mul_sup_le B _ _ T ?_ ?_
      · rcases Nat.eq_zero_or_pos (c n) with h0 | hpos
        · rw [h0, pow_zero, mul_one] at h1
          rw [h0, pow_zero, derivIdeal_one, mul_one]
          exact h1
        · obtain ⟨e, he⟩ : ∃ e, c n = e + 1 := ⟨c n - 1, by omega⟩
          have hq1 : (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ (if j = n then e else c j))
              = ∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j :=
            Finset.prod_congr rfl fun j hj => by
              rw [if_neg (Nat.ne_of_lt (Finset.mem_range.mp hj))]
          have hq2 : derivIdealIterate A n J ^ (if n = n then e else c n)
              = derivIdealIterate A n J ^ e := by simp
          have hprod : (∏ j ∈ Finset.range (n + 1),
                derivIdealIterate A j J ^ (if j = n then e else c j))
              = (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e := by
            rw [Finset.prod_range_succ, hq1, hq2]
          have hd : B * (derivIdealIterate A (n + 1) J *
              ((∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) *
                derivIdealIterate A n J ^ e)) ≤ T := by
            rw [← hprod]
            exact h2 n (Nat.lt_succ_self n) (fun j => if j = n then e else c j)
              (fun j hj => by simp [hj]) (by simp [he])
          have hstep : derivIdeal A (derivIdealIterate A n J ^ c n)
              ≤ derivIdealIterate A n J ^ e * derivIdealIterate A (n + 1) J := by
            rw [he, derivIdealIterate_succ]
            exact derivIdeal_pow_succ_le A (derivIdealIterate A n J) e
          refine le_trans (Ideal.mul_mono le_rfl (Ideal.mul_mono le_rfl hstep)) ?_
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]
      · have heq : B * (derivIdealIterate A n J ^ c n *
            derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j))
            = (B * derivIdealIterate A n J ^ c n) *
              derivIdeal A (∏ j ∈ Finset.range n, derivIdealIterate A j J ^ c j) :=
          (mul_assoc _ _ _).symm
        rw [heq]
        refine ih (B * derivIdealIterate A n J ^ c n) ?_ ?_
        · refine le_trans (le_of_eq ?_) h1
          simp only [mul_comm, mul_assoc]
        · intro i hi d hne hdi
          have hd := h2 i (Nat.lt_succ_of_lt hi) d hne hdi
          rw [Finset.prod_range_succ, hne n (by omega : n ≠ i)] at hd
          refine le_trans (le_of_eq ?_) hd
          simp only [mul_comm, mul_left_comm, mul_assoc]

/- English proof (authored)
The derivative of the supremum lies in the supremum of the derivatives of its contributing terms. For each qualifying monomial, the unchanged product qualifies at the preceding threshold. The Leibniz terms replace one factor by its next derivative, which lowers the weight by at most one under the monomial estimate. Thus all required terms are contained in the tuned ideal at the preceding threshold.
-/
theorem derivIdeal_tunedIdeal_succ_le (J : Ideal S) (m s : ℕ) :
    derivIdeal k (tunedIdeal k J m (s + 1)) ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_eq_iSup k J m (s + 1)]
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro c
  refine (derivIdeal_iSup_le k _).trans (iSup_le ?_)
  intro hc
  rw [tuningMonomial_eq_prod]
  refine le_trans (le_of_eq (one_mul _).symm) ?_
  refine mul_derivIdeal_prod_le J (tunedIdeal k J m s) c m 1 ?_ ?_
  · rw [one_mul]
    exact tuningMonomial_le_tunedIdeal k J m s c (by omega)
  · intro i hi d hne hdi
    rw [one_mul]
    exact derivIdealIterate_succ_mul_tuningMonomial_le J m s i hi c d hne hdi hc

/- English proof (authored)
Induct on the derivative count. Zero steps leave the ideal unchanged. At the next step, use monotonicity to differentiate the induction bound. If the threshold remaining in that bound is positive, the one-step estimate reduces it by one. If it is zero, the new target is still the unit ideal. Both cases give the bound with truncated subtraction.
-/
theorem derivIdealIterate_tunedIdeal_le (J : Ideal S) (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by
  induction j with
  | zero =>
      simp only [derivIdealIterate_zero, Nat.sub_zero]
      exact le_rfl
  | succ j ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      rcases Nat.eq_zero_or_pos (s - j) with h | h
      · have hsj : s - (j + 1) = 0 := by omega
        rw [hsj, tunedIdeal_zero]
        exact le_top
      · obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - j - 1, by omega⟩
        have hsj : s - (j + 1) = t := by omega
        rw [ht, hsj]
        exact derivIdeal_tunedIdeal_succ_le k J m t

/- English proof (authored)
One fewer derivative step than the positive threshold is bounded by the tuned ideal at threshold one. A single derivative step is bounded by the tuned ideal at the threshold decreased by one. Multiplying these two bounds and applying the product rule adds the thresholds back to the original threshold.
-/
theorem derivIdealIterate_mul_derivIdeal_tunedIdeal_le (J : Ideal S) (m s : ℕ) (hs : 1 ≤ s) :
    derivIdealIterate k (s - 1) (tunedIdeal k J m s) * derivIdeal k (tunedIdeal k J m s) ≤
      tunedIdeal k J m s := by
  have hss : s - (s - 1) = 1 := by omega
  have hsum : 1 + (s - 1) = s := by omega
  have h1 : derivIdealIterate k (s - 1) (tunedIdeal k J m s) ≤ tunedIdeal k J m 1 := by
    have h := derivIdealIterate_tunedIdeal_le k J m s (s - 1)
    rwa [hss] at h
  have h2 : derivIdeal k (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - 1) := by
    have h := derivIdealIterate_tunedIdeal_le k J m s 1
    rwa [derivIdealIterate_one] at h
  refine le_trans (Ideal.mul_mono h1 h2) ?_
  have h3 := tunedIdeal_mul_le k J m 1 (s - 1)
  rwa [hsum] at h3

/- English proof (authored)
If every exponent in the range were zero, all weighted contributions would vanish and the total weight would be zero. This contradicts the positive lower bound.
-/
private theorem exists_ne_zero_of_one_le_tuningWeight {m : ℕ} {c : ℕ → ℕ}
    (hc : 1 ≤ tuningWeight m c) : ∃ j ∈ Finset.range m, c j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : tuningWeight m c = 0 := by
    rw [tuningWeight_eq_sum]
    exact Finset.sum_eq_zero fun j hj => by rw [hcon j hj, Nat.mul_zero]
  rw [hz] at hc
  exact Nat.not_succ_le_zero 0 hc

/- English proof (authored)
Every monomial qualifying at threshold one has a nonzero exponent at some index in the range. The product is contained in that factor, and its positive power is contained in the corresponding derivative iterate. This derivative index is at most one below the mark. Monotonicity of derivative iterations puts the factor in the iterate one below the mark. Hence every contributing monomial lies in that iterate.
-/
theorem tunedIdeal_one_le_derivIdealIterate (J : Ideal S) (m : ℕ) (_hm : 1 ≤ m) :
    tunedIdeal k J m 1 ≤ derivIdealIterate k (m - 1) J := by
  rw [tunedIdeal_le_iff]
  intro c hc
  obtain ⟨j, hj, hcj⟩ := exists_ne_zero_of_one_le_tuningWeight hc
  have hjm : j ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  refine le_trans ?_ (derivIdealIterate_le_of_le k hjm J)
  have hsplit : derivIdealIterate k j J ^ c j *
      ∏ x ∈ (Finset.range m).erase j, derivIdealIterate k x J ^ c x =
      ∏ x ∈ Finset.range m, derivIdealIterate k x J ^ c x :=
    Finset.mul_prod_erase (Finset.range m) (fun x => derivIdealIterate k x J ^ c x) hj
  rw [tuningMonomial_eq_prod, ← hsplit]
  exact le_trans Ideal.mul_le_left (Ideal.pow_le_self hcj)

/- English proof (authored)
The tuned ideal is the supremum of its qualifying monomial ideals. Multiplication by the fixed ideal distributes over this supremum. The resulting supremum is contained in the target exactly when every product term is contained there.
-/
theorem mul_tunedIdeal_le_iff (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (Ideal.mul_mono le_rfl (tuningMonomial_le_tunedIdeal k J m s c hc)) h
  · intro h
    rw [tunedIdeal_eq_iSup, Submodule.mul_iSup]
    refine iSup_le fun c => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun hc => h c hc

/- English proof (authored)
The given element belongs to the derivative ideal one below the mark. Its specified power therefore generates an ideal contained in the same power of that derivative ideal, which is a tuning monomial supported at this single index. That index has weight one. Multiplying by the original monomial adds the power to its weight, so the product is contained in the tuned ideal at the increased threshold.
-/
theorem span_pow_mul_tuningMonomial_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n : ℕ) (c : ℕ → ℕ) :
    Ideal.span {x ^ n} * tuningMonomial k J m c ≤ tunedIdeal k J m (tuningWeight m c + n) := by
  have hmem : (m - 1) ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have hspan : Ideal.span {x ^ n} ≤ tuningMonomial k J m (n • Pi.single (m - 1) 1) := by
    rw [← tuningMonomial_pow, tuningMonomial_single k J m (m - 1) hmem,
      Ideal.span_singleton_le_iff_mem]
    exact Ideal.pow_mem_pow hx n
  refine le_trans (Ideal.mul_mono hspan le_rfl) ?_
  rw [tuningMonomial_mul]
  refine tuningMonomial_le_tunedIdeal k J m _ _ ?_
  rw [tuningWeight_add, tuningWeight_nsmul, tuningWeight_single m (m - 1) hmem]
  have hmm : m - (m - 1) = 1 := by omega
  rw [hmm]
  omega

/- English proof (authored)
Distribute the product with the principal power over the monomials qualifying for the original tuned ideal. The monomial estimate bounds each product by the tuned ideal at its weight plus the power. This threshold is at least the original threshold plus the power, so monotonicity gives the required bound.
-/
theorem span_pow_mul_tunedIdeal_le (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by
  rw [mul_tunedIdeal_le_iff]
  intro c hc
  refine le_trans (span_pow_mul_tuningMonomial_le k J m hm hx n c) ?_
  exact tunedIdeal_antitone k J m (Nat.add_le_add_right hc n)

section

variable [Algebra ℚ S]

/- English proof (authored)
The positive integer coefficient is nonzero in the rationals, so its image in the rational algebra is a unit with inverse the image of its rational reciprocal. Multiplying the given ideal element by this inverse shows the original element belongs to the ideal.
-/
private theorem mem_of_natCast_add_one_mul_mem {A : Type*} [CommRing A] [Algebra ℚ A] (n : ℕ)
    (I : Ideal A) (y : A) (h : ((n : A) + 1) * y ∈ I) : y ∈ I := by
  have hpos : (0 : ℚ) < (n : ℚ) + 1 := by positivity
  have hq : ((n : ℚ) + 1) ≠ 0 := hpos.ne'
  have hmap : algebraMap ℚ A ((n : ℚ) + 1) = (n : A) + 1 := by
    rw [map_add, map_one, map_natCast]
  have h1 : algebraMap ℚ A ((n : ℚ) + 1)⁻¹ * (((n : A) + 1) * y) ∈ I :=
    Ideal.mul_mem_left I _ h
  rw [← hmap, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul] at h1
  exact h1

/- English proof (authored)
The derivative iterate of the tuned ideal lies in the tuned ideal with threshold reduced by the derivative count. Multiplying by the specified power of the maximal-contact element raises that threshold by the exponent, by the principal-power product bound.
-/
private theorem pow_mul_mem_tunedIdeal (R : Type*) [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (s n p : ℕ) {g : A}
    (hg : g ∈ derivIdealIterate R n (tunedIdeal R J m s)) :
    x ^ p * g ∈ tunedIdeal R J m ((s - n) + p) := by
  have hg' : g ∈ tunedIdeal R J m (s - n) := derivIdealIterate_tunedIdeal_le R J m s n hg
  exact span_pow_mul_tunedIdeal_le R J m hm hx p (s - n)
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self (x ^ p)) hg')

/- English proof (authored)
Induct on the additional index in the bound. If it is zero, the derivative count already reaches the successor threshold. The principal-power product bound puts the element in that successor-threshold ideal and hence in its derivative ideal. In the inductive case, the product with one extra power of the contact element lies in the successor-threshold ideal. Its derivative therefore lies in the desired derivative ideal. The Leibniz rule expresses this derivative as the requested product times the positive integer one above the derivative count, plus the extra-power product of the derivative of the given element. The latter product lies in the target by induction, since the differentiated element belongs to the next derivative iterate and the increased count preserves the required bound. Subtract it and divide by the positive integer, which is a unit in the rational algebra.
-/
private theorem pow_mul_mem_derivIdeal_tunedIdeal_succ (R : Type*) [CommRing R] {A : Type*}
    [CommRing A] [Algebra R A] [Algebra ℚ A] (J : Ideal A) (m : ℕ) (hm : 1 ≤ m) {x : A}
    (hx : x ∈ derivIdealIterate R (m - 1) J) (δ : Derivation R A A) (hδ : δ x = 1) (s : ℕ) :
    ∀ d n : ℕ, s + 1 ≤ n + d → ∀ g : A, g ∈ derivIdealIterate R n (tunedIdeal R J m s) →
      x ^ n * g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) := by
  intro d
  induction d with
  | zero =>
      intro n hn g hg
      have h1 : x ^ n * g ∈ tunedIdeal R J m ((s - n) + n) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n n hg
      have h2 : s + 1 ≤ (s - n) + n := by omega
      exact le_derivIdeal R _ (tunedIdeal_antitone R J m h2 h1)
  | succ d ih =>
      intro n hn g hg
      have h1 : x ^ (n + 1) * g ∈ tunedIdeal R J m ((s - n) + (n + 1)) :=
        pow_mul_mem_tunedIdeal R J m hm hx s n (n + 1) hg
      have h2 : s + 1 ≤ (s - n) + (n + 1) := by omega
      have h3 : x ^ (n + 1) * g ∈ tunedIdeal R J m (s + 1) :=
        tunedIdeal_antitone R J m h2 h1
      have h4 : δ (x ^ (n + 1) * g) ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        derivation_apply_mem_derivIdeal R (tunedIdeal R J m (s + 1)) δ h3
      have h5 : δ g ∈ derivIdealIterate R (n + 1) (tunedIdeal R J m s) := by
        rw [derivIdealIterate_succ]
        exact derivation_apply_mem_derivIdeal R (derivIdealIterate R n (tunedIdeal R J m s)) δ hg
      have h6 : x ^ (n + 1) * δ g ∈ derivIdeal R (tunedIdeal R J m (s + 1)) :=
        ih (n + 1) (by omega) (δ g) h5
      have hd1 : δ (x ^ (n + 1)) = ((n : A) + 1) * x ^ n := by
        have hpow := δ.leibniz_pow x (n + 1)
        rw [hδ] at hpow
        simpa using hpow
      have hkey : ((n : A) + 1) * (x ^ n * g)
          = δ (x ^ (n + 1) * g) - x ^ (n + 1) * δ g := by
        rw [Derivation.leibniz, hd1]
        simp only [smul_eq_mul]
        ring
      refine mem_of_natCast_add_one_mul_mem n (derivIdeal R (tunedIdeal R J m (s + 1)))
        (x ^ n * g) ?_
      rw [hkey]
      exact Submodule.sub_mem _ h4 h6

/- English proof (authored)
Take an element of the tuned ideal as an element of its zeroth derivative iterate. Apply the principal-power induction with derivative count zero and additional index equal to the successor threshold. The resulting zeroth power is one, so the given element belongs to the derivative of the successor-threshold tuned ideal.
-/
theorem tunedIdeal_le_derivIdeal_tunedIdeal_succ (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (δ : Derivation k S S) (hδ : δ x = 1) (s : ℕ) :
    tunedIdeal k J m s ≤ derivIdeal k (tunedIdeal k J m (s + 1)) := by
  intro g hg
  have h := pow_mul_mem_derivIdeal_tunedIdeal_succ k J m hm hx δ hδ s (s + 1) 0 (by omega) g
    (by rw [derivIdealIterate_zero]; exact hg)
  rwa [pow_zero, one_mul] at h

end

end

end FunctorialResolution.EmbeddedResolution
