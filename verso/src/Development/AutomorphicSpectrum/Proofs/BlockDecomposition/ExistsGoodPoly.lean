import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.TraceJac

open Polynomial in
/- English proof (translation)
Proceed by induction on `G using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨s1, h1, e1⟩` from `hp`. Take `⟨s2, h2, e2⟩` from `hq`. Use `⟨s1 + s2, I.add_mem h1 h2, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, derivative_add, e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `monomial n a`. Take `⟨s, hs, es⟩` from `hI a`. Use `⟨b ^ n * s, I.mul_mem_left _ hs, ?_⟩` and prove the remaining obligations.

Establish `h1 : algebraMap S L (aeval b (monomial n a)) = algebraMap R L a * (algebraMap S L b) ^ n`. Rewrite using `[aeval_monomial, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]`. Establish `h2 : algebraMap S L (aeval b (derivative (monomial n a))) = algebraMap R L a * ((n : L) * (algebraMap S L b) ^ (n - 1))`. Rewrite using `[derivative_monomial, aeval_monomial, map_mul, map_pow, map_mul, map_natCast, map_mul, ← IsScalarTower.algebraMap_apply, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1, h2, Derivation.leibniz, Derivation.leibniz_pow, es]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_aeval {R S L : Type*} [CommRing R] [CommRing S] [Field L] [Algebra R S] [Algebra S L]
    [Algebra R L] [IsScalarTower R S L] (E : Derivation ℤ L L) (I : Ideal S)
    (hI : ∀ r : R, ∃ s ∈ I, E (algebraMap R L r) = algebraMap S L s) (G : R[X]) (b : S) :
    ∃ s ∈ I, E (algebraMap S L (aeval b G)) =
      algebraMap S L s + algebraMap S L (aeval b (derivative G)) * E (algebraMap S L b) := by
  induction G using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨s1, h1, e1⟩ := hp
    obtain ⟨s2, h2, e2⟩ := hq
    refine ⟨s1 + s2, I.add_mem h1 h2, ?_⟩
    simp only [map_add, derivative_add, e1, e2]
    ring
  | monomial n a =>
    obtain ⟨s, hs, es⟩ := hI a
    refine ⟨b ^ n * s, I.mul_mem_left _ hs, ?_⟩
    have h1 : algebraMap S L (aeval b (monomial n a)) = algebraMap R L a * (algebraMap S L b) ^ n := by
      rw [aeval_monomial, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap S L (aeval b (derivative (monomial n a))) =
        algebraMap R L a * ((n : L) * (algebraMap S L b) ^ (n - 1)) := by
      rw [derivative_monomial, aeval_monomial, map_mul, map_pow, map_mul, map_natCast, map_mul,
        ← IsScalarTower.algebraMap_apply, map_natCast]
      ring
    rw [h1, h2, Derivation.leibniz, Derivation.leibniz_pow, es]
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_pow]
    ring

open Polynomial in
/- English proof (translation)
Establish `hex : ∃ n : ℕ, ∃ G : R[X], G.Monic ∧ G.natDegree = n ∧ aeval b G ∈ P`. Take `⟨G, hG, h0⟩` from `Algebra.IsIntegral.isIntegral (R := R) b`. Conclude with `⟨_, G, hG, rfl, by`. Establish `: aeval b G = 0` using `by rw [aeval_def]; exact h0`. Rewrite using `[this]`.

Conclude with `P.zero_mem⟩`. Take `⟨G, hG, hdeg, hmem⟩` from `Nat.find_spec hex`. Use `⟨G, hmem, fun hd => ?_⟩` and prove the remaining obligations. Use `set n := Nat.find hex with hn`. Establish `hn0 : n ≠ 0`.

Introduce `h0`. Rewrite `hdeg` using `[h0]`. Establish `: G = 1` using `hG.natDegree_eq_zero.1 hdeg`. Rewrite `hmem` using `[this, map_one]`. Conclude with `hP ((Ideal.eq_top_iff_one _).2 hmem)`.

Take `⟨u, hu⟩` from `hnat n hn0`. Set `G1 : R[X]` to `C (↑u⁻¹ : R) * derivative G`. Establish `hG1 : G1.Monic`. Apply `Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n - 1)` to reduce the goal to its premises. Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[← hdeg]`. Conclude with `natDegree_derivative_le G`. Establish `: n - 1 + 1 = n` using `Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)`. Simplify using `only [G1, coeff_C_mul, coeff_derivative, this]`. Rewrite using `[← hdeg, hG.coeff_natDegree, hdeg]`.

Simplify using `only [one_mul, Nat.cast_sub (Nat.pos_of_ne_zero hn0), Nat.cast_one, sub_add_cancel]`. Rewrite using `[← hu]`. Simplify using the standard rewrite rules. Establish `hlt : G1.natDegree < n`. Establish `: G1.natDegree ≤ n - 1`.

Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← hdeg]`. Conclude with `natDegree_derivative_le G`. Use linear arithmetic over natural numbers and integers. Use `Nat.find_min hex hlt ⟨G1, hG1, rfl, ?_⟩` and prove the remaining obligations.

Simplify using `only [G1, map_mul, aeval_C]`. Conclude with `P.mul_mem_left _ hd`.
-/
theorem exists_good_poly {R S : Type*} [CommRing R] [CommRing S] [Nontrivial R] [Algebra R S]
    [Algebra.IsIntegral R S] (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (P : Ideal S) (hP : P ≠ ⊤)
    (b : S) : ∃ G : R[X], aeval b G ∈ P ∧ aeval b (derivative G) ∉ P := by
  classical
  have hex : ∃ n : ℕ, ∃ G : R[X], G.Monic ∧ G.natDegree = n ∧ aeval b G ∈ P := by
    obtain ⟨G, hG, h0⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    exact ⟨_, G, hG, rfl, by
      have : aeval b G = 0 := by rw [aeval_def]; exact h0
      rw [this]; exact P.zero_mem⟩
  obtain ⟨G, hG, hdeg, hmem⟩ := Nat.find_spec hex
  refine ⟨G, hmem, fun hd => ?_⟩
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    have : G = 1 := hG.natDegree_eq_zero.1 hdeg
    rw [this, map_one] at hmem
    exact hP ((Ideal.eq_top_iff_one _).2 hmem)
  obtain ⟨u, hu⟩ := hnat n hn0
  let G1 : R[X] := C (↑u⁻¹ : R) * derivative G
  have hG1 : G1.Monic := by
    apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n - 1)
    · refine (natDegree_C_mul_le _ _).trans ?_
      rw [← hdeg]; exact natDegree_derivative_le G
    · have : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)
      simp only [G1, coeff_C_mul, coeff_derivative, this]
      rw [← hdeg, hG.coeff_natDegree, hdeg]
      simp only [one_mul, Nat.cast_sub (Nat.pos_of_ne_zero hn0), Nat.cast_one, sub_add_cancel]
      rw [← hu]; simp
  have hlt : G1.natDegree < n := by
    have : G1.natDegree ≤ n - 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [← hdeg]; exact natDegree_derivative_le G
    omega
  refine Nat.find_min hex hlt ⟨G1, hG1, rfl, ?_⟩
  simp only [G1, map_mul, aeval_C]
  exact P.mul_mem_left _ hd

section core
variable {R S L Γ : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S] [WfDvdMonoid S]
  [Field L] [Algebra R S] [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
  [Algebra.IsIntegral R S] [LinearOrderedCommGroupWithZero Γ]

/- English proof (translation)
Establish `inj` using `IsFractionRing.injective S L`. Use `set ι := algebraMap S L with hι`. Establish `hne : ∀ x : S, x ≠ 0 → ι x ≠ 0` using `fun x hx h => hx (inj (by simpa using h))`. Establish `hϖ0 : ϖ ≠ 0` using `fun h => hπ0 (by simpa [h] using hπ)`. Establish `hϖu : ¬ IsUnit ϖ` using `fun h => by`.

Use `(hlt 1).2 (h.dvd)` as an intermediate fact. Simplify using `at this`. Establish `hone : ∀ x : S, ¬ ϖ ∣ x → v (ι x) = 1` using `fun x hx => le_antisymm (hS x) (not_lt.1 (fun h => hx ((hlt x).1 h)))`. Use `set c := v (ι ϖ) with hc`. Establish `hc1 : c < 1` using `(hlt ϖ).2 dvd_rfl`.

Establish `hc0 : c ≠ 0`. Rewrite using `[hc, Valuation.ne_zero_iff]`. Conclude with `hne _ hϖ0`. Establish `hle_c : ∀ x : S, ϖ ∣ x → v (ι x) ≤ c`. Introduce and unpack `x ⟨z, rfl⟩`.

Rewrite using `[map_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' (hS z)`. Take `⟨e, w, hw, hπw⟩` from `WfDvdMonoid.max_power_factor' hπ0 hϖu`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`.

Apply `hw` to reduce the goal to its premises. Rewrite `hπw` using `[pow_zero, one_mul]`. Rewrite using `[← hπw]` and apply the resulting hypothesis. Take `⟨e', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero he`. Establish `hw0 : ι w ≠ 0` using `hne _ (fun h => hw (by simp [h]))`.

Establish `hvw : v (ι w) = 1` using `hone w hw`. Establish `hnatv : ∀ n : ℕ, n ≠ 0 → v (n : L) = 1`. Introduce `n hn`. Establish `hu : IsUnit (n : S)`. Use `(hnat n hn).map (algebraMap R S)` as an intermediate fact.

Simplify using `using this`. Establish `: ¬ ϖ ∣ (n : S)` using `fun h => hϖu (isUnit_of_dvd_unit h hu)`. Use `hone _ this` as an intermediate fact. Simplify `this` using `[hι]`. Establish `stepA : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → v (E (ι ϖ)) ≤ c * T`.

Introduce `T hT hb`. Take `⟨s, hs⟩` from `hEπ`. Establish `h1 : E (ι π) = (ι ϖ) ^ (e' + 1) * E (ι w) + ι w * (((e' + 1 : ℕ) : L) * (ι ϖ) ^ e' * E (ι ϖ))`. Rewrite using `[hπw, map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow]`. Simplify using `only [smul_eq_mul, nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ι w * (((e' + 1 : ℕ) : L) * E (ι ϖ)) = ι ϖ * (ι w * ι s - E (ι w))`. Establish `h3 : (ι ϖ) ^ e' ≠ 0` using `pow_ne_zero _ (hne _ hϖ0)`. Apply `mul_left_cancel₀ h3` to reduce the goal to its premises.

Establish `h4 : ι π = (ι ϖ) ^ (e' + 1) * ι w` using `by rw [hπw, map_mul, map_pow]`. Establish `h5 : E (ι π) = (ι ϖ) ^ (e' + 1) * ι w * ι s` using `by rw [hs, map_mul, h4]`. Rewrite `h1` using `[h5]`. Take the linear combination `-h1`. Establish `h3` using `congrArg v h2`.

Rewrite `h3` using `[map_mul, map_mul, map_mul, hvw, hnatv _ (Nat.succ_ne_zero e'), one_mul, one_mul]`. Rewrite using `[h3]`. Use `gcongr`. Use `(Valuation.map_sub _ _ _).trans (max_le ?_ (hb w))` and prove the remaining obligations. Rewrite using `[map_mul, hvw, one_mul]`.

Conclude with `(hS s).trans hT`. Establish `stepB : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ y : S, ϖ ∣ y → v (E (ι y)) ≤ c * T`. Introduce and unpack `T hT hb y ⟨z, rfl⟩`. Rewrite using `[map_mul, Derivation.leibniz]`. Simplify using `only [smul_eq_mul]`.

Use `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `gcongr`. Conclude with `hb z`. Rewrite using `[map_mul]`.

Conclude with `(mul_le_of_le_one_left' (hS z)).trans (stepA T hT hb)`. Establish `stepC : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ b : S, v (E (ι b)) ≤ max (c * T) 1 ∧ (I ≤ Ideal.span {ϖ} → v (E (ι b)) ≤ c * T)`. Introduce `T hT hb b`. Establish `hP : Ideal.span {ϖ} ≠ ⊤` using `by rwa [Ne, Ideal.span_singleton_eq_top]`. Take `⟨G, hG1, hG2⟩` from `exists_good_poly (R := R) hnat (Ideal.span {ϖ}) hP b`.

Rewrite `hG1`, `hG2` using `[Ideal.mem_span_singleton]`. Take `⟨s, hsI, hs⟩` from `deriv_aeval (R := R) E I hI G b`. Establish `hu` using `hone _ hG2`. Establish `h1 : v (E (ι b)) = v (E (ι (Polynomial.aeval b G)) - ι s)`. Establish `: E (ι (Polynomial.aeval b G)) - ι s = ι (Polynomial.aeval b (Polynomial.derivative G)) * E (ι b)` using `by rw [hs]; ring`.

Rewrite using `[this, map_mul, hu, one_mul]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[h1]`. Use `(Valuation.map_sub _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `(stepB T hT hb _ hG1).trans (le_max_left _ _)`.

Conclude with `(hS s).trans (le_max_right _ _)`. Introduce `hIle`. Rewrite using `[h1]`. Use `(Valuation.map_sub _ _ _).trans (max_le (stepB T hT hb _ hG1) ?_)` and prove the remaining obligations. Use `Ideal.mem_span_singleton.1 (hIle hsI)` as an intermediate fact.

Conclude with `(hle_c s this).trans (le_mul_of_one_le_right' hT)`. Establish `hbase : ∃ m : ℕ, ∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m`. Take `⟨m, δ', hδ', hδm⟩` from `WfDvdMonoid.max_power_factor' hδ hϖu`. Use `⟨m, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hδE x`.

Establish `h1` using `congrArg v hy`. Rewrite `h1` using `[map_mul, hδm, map_mul, map_mul, map_pow, map_pow, hone _ hδ', mul_one]`. Establish `h2 : v (E (ι x)) = (c⁻¹) ^ m * v (ι y)`. Rewrite using `[← h1, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hc0)]`. Rewrite using `[h2]`.

Conclude with `mul_le_of_le_one_right' (hS y)`. Establish `hcinv : 1 ≤ c⁻¹` using `(one_le_inv₀ (zero_lt_iff.2 hc0)).2 hc1.le`. Establish `hdesc : ∀ m : ℕ, (∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m) → ∀ x : S, v (E (ι x)) ≤ 1`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simpa using id`. Consider the case `succ m ih`. Introduce `h`. Apply `ih` to reduce the goal to its premises. Introduce `x`.

Establish `h1` using `(stepC _ (one_le_pow₀ hcinv) h x).1`. Establish `h2 : c * (c⁻¹) ^ (m + 1) = (c⁻¹) ^ m`. Rewrite using `[pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hc0, mul_one]`. Rewrite `h1` using `[h2]`. Conclude with `h1.trans (max_le le_rfl (one_le_pow₀ hcinv))`.

Take `⟨m, hm⟩` from `hbase`. Establish `hb1` using `hdesc m hm`. Use `⟨hb1, fun x hx => ?_, fun hIle x => ?_⟩` and prove the remaining obligations. Use `stepB 1 le_rfl hb1 x hx` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Conclude with `this.trans_lt hc1`. Use `(stepC 1 le_rfl hb1 x).2 hIle` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this.trans_lt hc1`.
-/
theorem core (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (v : Valuation L Γ) (ϖ : S)
    (hS : ∀ x : S, v (algebraMap S L x) ≤ 1)
    (hlt : ∀ x : S, v (algebraMap S L x) < 1 ↔ ϖ ∣ x)
    (E : Derivation ℤ L L) (I : Ideal S)
    (hI : ∀ r : R, ∃ s ∈ I, E (algebraMap R L r) = algebraMap S L s)
    (π : S) (hπ0 : π ≠ 0) (hπ : ϖ ∣ π)
    (hEπ : ∃ s : S, E (algebraMap S L π) = algebraMap S L (π * s))
    (δ : S) (hδ : δ ≠ 0) (hδE : ∀ x : S, ∃ y : S, algebraMap S L δ * E (algebraMap S L x) = algebraMap S L y) :
    (∀ x : S, v (E (algebraMap S L x)) ≤ 1) ∧ (∀ x : S, ϖ ∣ x → v (E (algebraMap S L x)) < 1) ∧
      (I ≤ Ideal.span {ϖ} → ∀ x : S, v (E (algebraMap S L x)) < 1) := by
  classical
  have inj := IsFractionRing.injective S L
  set ι := algebraMap S L with hι
  have hne : ∀ x : S, x ≠ 0 → ι x ≠ 0 := fun x hx h => hx (inj (by simpa using h))
  have hϖ0 : ϖ ≠ 0 := fun h => hπ0 (by simpa [h] using hπ)
  have hϖu : ¬ IsUnit ϖ := fun h => by
    have := (hlt 1).2 (h.dvd)
    simp at this
  have hone : ∀ x : S, ¬ ϖ ∣ x → v (ι x) = 1 := fun x hx =>
    le_antisymm (hS x) (not_lt.1 (fun h => hx ((hlt x).1 h)))
  set c := v (ι ϖ) with hc
  have hc1 : c < 1 := (hlt ϖ).2 dvd_rfl
  have hc0 : c ≠ 0 := by
    rw [hc, Valuation.ne_zero_iff]; exact hne _ hϖ0
  have hle_c : ∀ x : S, ϖ ∣ x → v (ι x) ≤ c := by
    rintro x ⟨z, rfl⟩
    rw [map_mul, map_mul]
    exact mul_le_of_le_one_right' (hS z)

  obtain ⟨e, w, hw, hπw⟩ := WfDvdMonoid.max_power_factor' hπ0 hϖu
  have he : e ≠ 0 := by
    rintro rfl
    apply hw
    rw [pow_zero, one_mul] at hπw
    rwa [← hπw]
  obtain ⟨e', rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  have hw0 : ι w ≠ 0 := hne _ (fun h => hw (by simp [h]))
  have hvw : v (ι w) = 1 := hone w hw
  have hnatv : ∀ n : ℕ, n ≠ 0 → v (n : L) = 1 := by
    intro n hn
    have hu : IsUnit (n : S) := by
      have := (hnat n hn).map (algebraMap R S)
      simpa using this
    have : ¬ ϖ ∣ (n : S) := fun h => hϖu (isUnit_of_dvd_unit h hu)
    have := hone _ this
    simpa [hι] using this

  have stepA : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → v (E (ι ϖ)) ≤ c * T := by
    intro T hT hb
    obtain ⟨s, hs⟩ := hEπ
    have h1 : E (ι π) = (ι ϖ) ^ (e' + 1) * E (ι w) +
        ι w * (((e' + 1 : ℕ) : L) * (ι ϖ) ^ e' * E (ι ϖ)) := by
      rw [hπw, map_mul, map_pow, Derivation.leibniz, Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.succ_eq_add_one, Nat.add_sub_cancel]
      push_cast
      ring
    have h2 : ι w * (((e' + 1 : ℕ) : L) * E (ι ϖ)) = ι ϖ * (ι w * ι s - E (ι w)) := by
      have h3 : (ι ϖ) ^ e' ≠ 0 := pow_ne_zero _ (hne _ hϖ0)
      apply mul_left_cancel₀ h3
      have h4 : ι π = (ι ϖ) ^ (e' + 1) * ι w := by rw [hπw, map_mul, map_pow]
      have h5 : E (ι π) = (ι ϖ) ^ (e' + 1) * ι w * ι s := by rw [hs, map_mul, h4]
      rw [h5] at h1
      linear_combination -h1
    have h3 := congrArg v h2
    rw [map_mul, map_mul, map_mul, hvw, hnatv _ (Nat.succ_ne_zero e'), one_mul, one_mul] at h3
    rw [h3]
    gcongr
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ (hb w))
    rw [map_mul, hvw, one_mul]
    exact (hS s).trans hT
  have stepB : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ y : S, ϖ ∣ y → v (E (ι y)) ≤ c * T := by
    rintro T hT hb y ⟨z, rfl⟩
    rw [map_mul, Derivation.leibniz]
    simp only [smul_eq_mul]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; gcongr; exact hb z
    · rw [map_mul]
      exact (mul_le_of_le_one_left' (hS z)).trans (stepA T hT hb)
  have stepC : ∀ T : Γ, 1 ≤ T → (∀ x : S, v (E (ι x)) ≤ T) → ∀ b : S, v (E (ι b)) ≤ max (c * T) 1 ∧
      (I ≤ Ideal.span {ϖ} → v (E (ι b)) ≤ c * T) := by
    intro T hT hb b
    have hP : Ideal.span {ϖ} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
    obtain ⟨G, hG1, hG2⟩ := exists_good_poly (R := R) hnat (Ideal.span {ϖ}) hP b
    rw [Ideal.mem_span_singleton] at hG1 hG2
    obtain ⟨s, hsI, hs⟩ := deriv_aeval (R := R) E I hI G b
    have hu := hone _ hG2
    have h1 : v (E (ι b)) = v (E (ι (Polynomial.aeval b G)) - ι s) := by
      have : E (ι (Polynomial.aeval b G)) - ι s =
          ι (Polynomial.aeval b (Polynomial.derivative G)) * E (ι b) := by rw [hs]; ring
      rw [this, map_mul, hu, one_mul]
    constructor
    · rw [h1]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · exact (stepB T hT hb _ hG1).trans (le_max_left _ _)
      · exact (hS s).trans (le_max_right _ _)
    · intro hIle
      rw [h1]
      refine (Valuation.map_sub _ _ _).trans (max_le (stepB T hT hb _ hG1) ?_)
      have := Ideal.mem_span_singleton.1 (hIle hsI)
      exact (hle_c s this).trans (le_mul_of_one_le_right' hT)

  have hbase : ∃ m : ℕ, ∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m := by
    obtain ⟨m, δ', hδ', hδm⟩ := WfDvdMonoid.max_power_factor' hδ hϖu
    refine ⟨m, fun x => ?_⟩
    obtain ⟨y, hy⟩ := hδE x
    have h1 := congrArg v hy
    rw [map_mul, hδm, map_mul, map_mul, map_pow, map_pow, hone _ hδ', mul_one] at h1
    have h2 : v (E (ι x)) = (c⁻¹) ^ m * v (ι y) := by
      rw [← h1, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero _ hc0)]
    rw [h2]
    exact mul_le_of_le_one_right' (hS y)
  have hcinv : 1 ≤ c⁻¹ := (one_le_inv₀ (zero_lt_iff.2 hc0)).2 hc1.le
  have hdesc : ∀ m : ℕ, (∀ x : S, v (E (ι x)) ≤ (c⁻¹) ^ m) → ∀ x : S, v (E (ι x)) ≤ 1 := by
    intro m
    induction m with
    | zero => simpa using id
    | succ m ih =>
      intro h
      apply ih
      intro x
      have h1 := (stepC _ (one_le_pow₀ hcinv) h x).1
      have h2 : c * (c⁻¹) ^ (m + 1) = (c⁻¹) ^ m := by
        rw [pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      rw [h2] at h1
      exact h1.trans (max_le le_rfl (one_le_pow₀ hcinv))
  obtain ⟨m, hm⟩ := hbase
  have hb1 := hdesc m hm
  refine ⟨hb1, fun x hx => ?_, fun hIle x => ?_⟩
  · have := stepB 1 le_rfl hb1 x hx
    rw [mul_one] at this
    exact this.trans_lt hc1
  · have := (stepC 1 le_rfl hb1 x).2 hIle
    rw [mul_one] at this
    exact this.trans_lt hc1
end core

end GlobalTheory.CompanionTheory.TraceJac
