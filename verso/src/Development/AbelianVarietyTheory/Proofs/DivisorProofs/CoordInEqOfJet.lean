import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped Classical

namespace GlobalTheory.LatConjOne

/- English proof (translation)
Use `⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']`. Simplify using `[Multiset.count_singleton]`.
-/
theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) : ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
  simp [Multiset.count_singleton]

/- English proof (translation)
Establish `e : ∀ i x, φ i (algebraMap K E x) = ι x` using `fun i x => by rw [← RingHom.comp_apply, hK]`. Establish `h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j`. Introduce `i`. Take `⟨j, hj, -⟩` from `hφ ((g : ℂ →+* ℂ).comp (φ i))`. Break down `hj with hj | hj` into its components or cases.

Conclude with `⟨j, hj⟩`. It suffices to derive a contradiction. Take `⟨x, hx⟩` from `hr`. Use `congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj` as an intermediate fact. Simplify using `only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this`.

Rewrite `this` using `[RingEquiv.coe_toRingHom, hg]`. Conclude with `hx this.symm`. Use `choose π hπ using h1`. Establish `hinj : Function.Injective π`. Introduce `i i' h`.

Establish `h2 : φ i = φ i'`. Establish `h3` using `(hπ i).trans ((congrArg φ h).trans (hπ i').symm)`. Use extensionality with `x`. Use `congrArg (fun f : E →+* ℂ => f x) h3` as an intermediate fact. Simplify using `using g.injective this`.

Take `⟨j, -, hj⟩` from `hφ (φ i)`. Rewrite using `[hj i (Or.inl rfl), hj i' (Or.inl h2)]`. Conclude with `⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩`.
-/
theorem exists_perm {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (ι : K →+* ℂ) (φ : I → E →+* ℂ) (g : ℂ ≃+* ℂ) (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (hg : ∀ x, g (ι x) = ι x) (hr : ∃ x, starRingEnd ℂ (ι x) ≠ ι x) :
    ∃ π : I ≃ I, ∀ i, (g : ℂ →+* ℂ).comp (φ i) = φ (π i) := by
  have e : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hK]
  have h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j := by
    intro i
    obtain ⟨j, hj, -⟩ := hφ ((g : ℂ →+* ℂ).comp (φ i))
    rcases hj with hj | hj
    · exact ⟨j, hj⟩
    · exfalso
      obtain ⟨x, hx⟩ := hr
      have := congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this
      rw [RingEquiv.coe_toRingHom, hg] at this
      exact hx this.symm
  choose π hπ using h1
  have hinj : Function.Injective π := by
    intro i i' h
    have h2 : φ i = φ i' := by
      have h3 := (hπ i).trans ((congrArg φ h).trans (hπ i').symm)
      ext x
      have := congrArg (fun f : E →+* ℂ => f x) h3
      simpa using g.injective this
    obtain ⟨j, -, hj⟩ := hφ (φ i)
    rw [hj i (Or.inl rfl), hj i' (Or.inl h2)]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩

/- English proof (translation)
Introduce `σ`. Take `⟨j, hj, hu⟩` from `hφ σ`. Use `⟨π.symm j, by simpa using hj, fun i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[← hu (π i) hi]`. Simplify using the standard rewrite rules.
-/
theorem isCMType_comp {E : Type} [Field E] [NumberField E] {I : Type} {φ : I → E →+* ℂ} (hφ : IsCMType φ) (π : I ≃ I) :
    IsCMType (fun i => φ (π i)) := by
  intro σ
  obtain ⟨j, hj, hu⟩ := hφ σ
  refine ⟨π.symm j, by simpa using hj, fun i hi => ?_⟩
  rw [← hu (π i) hi]; simp

/- English proof (translation)
Establish `h : ∀ σ x, term φ' k κ σ x = term φ k κ' σ x`. Introduce `σ x`. Simplify using `only [term]`. Conclude with `Fintype.prod_equiv π _ _ (fun i => by rw [hπ, hκ])`. Simplify using `only [IsLatSum, h]`.
-/
theorem isLatSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ φ' : I → E →+* ℂ) (π : I ≃ I)
    (hπ : ∀ i, φ' i = φ (π i)) (κ κ' : I → ℕ) (hκ : ∀ i, κ' (π i) = κ i) (k : ℕ) (L : Set E) (S : ℂ → ℂ) :
    IsLatSum φ' k κ L S ↔ IsLatSum φ k κ' L S := by
  have h : ∀ σ x, term φ' k κ σ x = term φ k κ' σ x := by
    intro σ x
    simp only [term]
    exact Fintype.prod_equiv π _ _ (fun i => by rw [hπ, hκ])
  simp only [IsLatSum, h]

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Establish `hpos : 0 < Module.finrank ℚ (maximalRealSubfield E)` using `Module.finrank_pos`. Establish `h1 : Module.finrank ℚ (maximalRealSubfield E) = 1` using `by omega`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hE : Module.finrank ℚ E = 2`.

Rewrite using `[← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h1, h2]`. Establish `hgt` using `NumberField.abs_discr_gt_two (K := E) (by omega)`. Establish `hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤` using `Subalgebra.bot_eq_top_of_finrank_eq_one h1`. Set `f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ` to `AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))`. Establish `hF : NumberField.discr (maximalRealSubfield E) = 1`.

Rewrite using `[NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]`. Establish `key` using `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)`. Establish `hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤` using `h`. Rewrite `key` using `[hU, Ideal.absNorm_top, hF]`. Simplify using `at key`.

Rewrite `hgt` using `[Int.abs_eq_natAbs, key]`. Evaluate the numerical expressions using `at hgt`.
-/
theorem two_le_finrank_of_unramFin (E : Type) [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by omega
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hE : Module.finrank ℚ E = 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E, h1, h2]
  have hgt := NumberField.abs_discr_gt_two (K := E) (by omega)
  have hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  let f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ :=
    AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm
      ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))
  have hF : NumberField.discr (maximalRealSubfield E) = 1 := by
    rw [NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]
  have key := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, hF] at key
  simp at key
  rw [Int.abs_eq_natAbs, key] at hgt
  norm_num at hgt

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Simplify using `only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]`. Use `Real.Gamma_nat_eq_factorial (k - 1)` as an intermediate fact. Rewrite `this` using `[Nat.cast_sub hk, Nat.cast_one, sub_add_cancel]`. Then use the resulting hypothesis.

Consider the case `succ m ih`. Establish `h0 : (k : ℝ) + m ≠ 0`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `: (0 : ℝ) ≤ m` using `m.cast_nonneg`. Conclude with `ne_of_gt (by linarith)`.

Rewrite using `[Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gamma_nat_add (k m : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + m) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range m, ((k : ℝ) + j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    have := Real.Gamma_nat_eq_factorial (k - 1)
    rwa [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at this
  | succ m ih =>
    have h0 : (k : ℝ) + m ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ne_of_gt (by linarith)
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]; ring

/- English proof (translation)
Rewrite using `[cmValueConst_eq]`. Simplify using `only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Finset.prod_pow_eq_pow_sum]`. Establish `h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1` using `by rw [← mul_pow]; norm_num`. Use `push_cast`. Take the linear combination `(-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) * (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i)) …`.
-/
theorem cmPeriodConstant_eq_of_card_cmType (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) :
    (C0 E d k κ : ℂ) = (cWt E k : ℂ) * risingFactor k κ * (-1) ^ (∑ i, κ i) *
      ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) := by
  rw [cmValueConst_eq]
  simp only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Finset.prod_pow_eq_pow_sum]
  have h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination (-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
    ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) *
    (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i))) * h1

/- English proof (translation)
Establish `hk : 1 ≤ 2 * s` using `by omega`. Establish `hC0` using `cmPeriodConstant_eq_of_card_cmType E d hk hcard κ`. Establish `hcW : (cWt E (2 * s) : ℂ) ≠ 0`. Establish `h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)|` using `abs_pos.2 (by exact_mod_cast discr_ne_zero _)`. Establish `h2 : (0 : ℝ) < ((2 * s - 1).factorial : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`.

Establish `: (0 : ℝ) < cWt E (2 * s)` using `mul_pos (pow_pos h2 _) (Real.rpow_pos_of_pos h1 _)`. Conclude with `this.ne'` after adjusting the coercions. Establish `hρ : risingFactor (2 * s) κ ≠ 0`. Unfold `risingFactor`. Use `Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.2 fun j _ => ?_)` and prove the remaining obligations.

Rewrite using `[← Nat.cast_add]; exact Nat.cast_ne_zero.2 (by omega)`. Establish `hPA0 : ∏ i, A i ^ κ i ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hA i)`. Establish `hε1 : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1`. Apply the tactic sequence `rcases Int.units_eq_one_or ε with h | h <;> simp [h]`. Establish `hε : ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i) = 1` using `by rw [← mul_pow, hε1, one_pow]`.

Establish `hε0 : ((ε : ℤ) : ℂ) ^ (∑ i, κ i) ≠ 0`. Introduce `h0`. Rewrite `hε` using `[h0, zero_mul]`. Conclude with `zero_ne_one hε`. Establish `hPA : ∏ i, (((ε : ℤ) : ℂ) * A i) ^ κ i = ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ∏ i, A i ^ κ i`.

Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `hPB : ∏ i, (A i * Ω ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i = (∏ i, A i ^ κ i) * (Ω ^ 2) ^ (∑ i, κ i) * (((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i)`. Simplify using `only [mul_div_assoc, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Rewrite `h` using `[hPA]`. Establish `hSv : Sv = C ^ (2 * s) * x / ((cWt E (2 * s) : ℂ) * risingFactor (2 * s) κ * (((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ∏ i, A i ^ κ i))`.

Rewrite using `[eq_div_iff (mul_ne_zero (mul_ne_zero hcW hρ) (mul_ne_zero hε0 hPA0)), h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq : ((Real.sqrt d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Unfold `coordIn`.

Establish `hΩe : Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) = (Ω ^ Fintype.card I) ^ (2 * s) * (Ω ^ 2) ^ (∑ i, κ i)`. Rewrite using `[← pow_mul, ← pow_mul, ← pow_add]`. Put the polynomial expressions in normal form. Establish `hq : ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) = ((((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i))⁻¹`. Rewrite using `[← inv_pow, inv_div]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hq0 : (((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i) ≠ 0` using `pow_ne_zero _ (div_ne_zero hsq (mul_ne_zero two_ne_zero hpi))`. Establish `hw : (Ω ^ 2) ^ (∑ i, κ i) ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hΩ)`. Establish `ho : Ω ^ Fintype.card I ≠ 0` using `pow_ne_zero _ hΩ`.

Rewrite using `[hC0, hPB, hSv, hΩe, hq, neg_pow, div_pow]`. Generalize the expression as in `(((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i) = q at *`. Generalize the expression as in `(Ω ^ 2) ^ (∑ i, κ i) = w at *`. Generalize the expression as in `Ω ^ Fintype.card I = o at *`. Generalize the expression as in `(∏ i, A i ^ κ i) = P at *`.

Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Establish `ho2 : o ^ (s * 2) * o⁻¹ ^ (s * 2) = 1` using `by rw [← mul_pow, mul_inv_cancel₀ ho, one_pow]`. Take the linear combination `(-(C ^ (s * 2) * x * (-1) ^ ∑ i, κ i)) * hε + (-(C ^ (s * 2) * x * (-1) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i))) * ho2`.
-/
theorem coordIn_eq_of_jet (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) (ε : ℤˣ) {C x Sv Ω : ℂ} {A : I → ℂ}
    (hΩ : Ω ≠ 0) (hA : ∀ i, A i ≠ 0)
    (h : C ^ (2 * s) * x = 1 * ((cWt E (2 * s) : ℂ) * risingFactor (2 * s) κ * Sv) * ∏ i, (((ε : ℤ) : ℂ) * A i) ^ κ i) :
    coordIn E d s κ Ω Sv = (-((ε : ℤ) : ℂ)) ^ (∑ i, κ i) * x * (C / Ω ^ Fintype.card I) ^ (2 * s) /
      ∏ i, (A i * Ω ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i := by
  have hk : 1 ≤ 2 * s := by omega
  have hC0 := cmPeriodConstant_eq_of_card_cmType E d hk hcard κ
  have hcW : (cWt E (2 * s) : ℂ) ≠ 0 := by
    have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
    have h2 : (0 : ℝ) < ((2 * s - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have : (0 : ℝ) < cWt E (2 * s) := mul_pos (pow_pos h2 _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hρ : risingFactor (2 * s) κ ≠ 0 := by
    unfold risingFactor
    refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.2 fun j _ => ?_)
    rw [← Nat.cast_add]; exact Nat.cast_ne_zero.2 (by omega)
  have hPA0 : ∏ i, A i ^ κ i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hA i)
  have hε1 : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hε : ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i) = 1 := by rw [← mul_pow, hε1, one_pow]
  have hε0 : ((ε : ℤ) : ℂ) ^ (∑ i, κ i) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hε; exact zero_ne_one hε
  have hPA : ∏ i, (((ε : ℤ) : ℂ) * A i) ^ κ i = ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ∏ i, A i ^ κ i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hPB : ∏ i, (A i * Ω ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i =
      (∏ i, A i ^ κ i) * (Ω ^ 2) ^ (∑ i, κ i) * (((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i) := by
    simp only [mul_div_assoc, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hPA] at h
  have hSv : Sv = C ^ (2 * s) * x / ((cWt E (2 * s) : ℂ) * risingFactor (2 * s) κ *
      (((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ∏ i, A i ^ κ i)) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hcW hρ) (mul_ne_zero hε0 hPA0)), h]; ring
  have hsq : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold coordIn
  have hΩe : Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i) = (Ω ^ Fintype.card I) ^ (2 * s) * (Ω ^ 2) ^ (∑ i, κ i) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  have hq : ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) =
      ((((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i))⁻¹ := by
    rw [← inv_pow, inv_div]; push_cast; ring
  have hq0 : (((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i) ≠ 0 :=
    pow_ne_zero _ (div_ne_zero hsq (mul_ne_zero two_ne_zero hpi))
  have hw : (Ω ^ 2) ^ (∑ i, κ i) ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hΩ)
  have ho : Ω ^ Fintype.card I ≠ 0 := pow_ne_zero _ hΩ
  rw [hC0, hPB, hSv, hΩe, hq, neg_pow, div_pow]
  generalize (((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi)) ^ (∑ i, κ i) = q at *
  generalize (Ω ^ 2) ^ (∑ i, κ i) = w at *
  generalize Ω ^ Fintype.card I = o at *
  generalize (∏ i, A i ^ κ i) = P at *
  field_simp
  ring_nf
  have ho2 : o ^ (s * 2) * o⁻¹ ^ (s * 2) = 1 := by rw [← mul_pow, mul_inv_cancel₀ ho, one_pow]
  linear_combination (-(C ^ (s * 2) * x * (-1) ^ ∑ i, κ i)) * hε +
    (-(C ^ (s * 2) * x * (-1) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i) * ((ε : ℤ) : ℂ) ^ (∑ i, κ i))) * ho2
end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

/- English proof (translation)
Take `⟨ε, hJ⟩` from `hJ`. Introduce `K _ _ d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E _ _ _ _ I _ φ s 𝔣 Q hD κ κ' hκ y S S' hSS hSS'`. Take `⟨hU, hφ, hφK, hs, hb, hQ⟩` from `hD`. Establish `hf : 2 ≤ Module.finrank ℚ (FR E)` using `two_le_finrank_of_unramFin E hU`. Establish `hc : condQ 𝔣 Q ≠ ⊥`.

Unfold `condQ`. Use `mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)` and prove the remaining obligations. Take `⟨𝔠, X₀, δ₀, N, T, hAdm, hOver, -, hA⟩` from `hMA K d δ ι hK2 hd hδ Λ₀ Ω₀ hTT.2.2.2.1 hΩ₀ E I φ hφ hφK (condQ 𝔣 Q) y hc`. Take `⟨T', hOver', hC, hB⟩` from `hMC K d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E I φ hφ hφK (condQ 𝔣 Q) y hc 𝔠 X₀ δ₀ N T hOver`. Take `⟨z, hz⟩` from `(hZ E s hs).1`.

Set `R₀ : Subring ℂ` to `(algebraMap ℚ ℂ).range`. Establish `hzR : ∀ C, (1 : ℂ) * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R₀` using `fun C => ⟨z C / 2 ^ Module.finrank ℚ (FR E), by simp⟩`. Take `⟨r, hr⟩` from `hE E hf 𝔠 s hs z hz R₀ 1 R₀.one_mem hzR`. Establish `hmem : ∀ a : R₀, (a : ℂ) ∈ algebraicClosure ℚ ℂ`. Introduce and unpack `⟨a, q, rfl⟩`.

Conclude with `(algebraicClosure ℚ ℂ).algebraMap_mem q`. Set `f : R₀ →+* Qb` to `{ toFun := fun a => ⟨a, hmem a⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Use `letI : Algebra R₀ Qb := f.toAlgebra`. Take `⟨x, hx⟩` from `hJ E I 𝔠 hf R₀ s r hs Qb X₀ δ₀ N hAdm κ`. Take `⟨u, hu⟩` from `exists_list_count κ`.

Establish `hgq : ∀ a : R₀, g (a : ℂ) = a`. Introduce and unpack `⟨a, q, rfl⟩`. Conclude with `congrArg (fun h : ℚ →+* ℂ => h q) (Subsingleton.elim ((g : ℂ →+* ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ))`. Establish `hr0 : ∃ x : K, starRingEnd ℂ (ι x) ≠ ι x`. Use `⟨δ, fun h => ?_⟩` and prove the remaining obligations.

Establish `h2 : (ι δ) ^ 2 = -(d : ℂ)` using `by rw [← map_pow, hδ]; simp`. Take `⟨rr, hrr⟩` from `Complex.conj_eq_iff_real.1 h`. Rewrite `h2` using `[hrr]`. Establish `h3` using `congrArg Complex.re h2`. Establish `h4 : rr ^ 2 = -(d : ℝ)`.

Simplify using `only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h3`. Conclude with `h3`. Establish `: (0 : ℝ) < d` using `by exact_mod_cast hd`. Use polynomial arithmetic with `[sq_nonneg rr]`. Take `⟨π, hπ⟩` from `exists_perm ι φ g hφ hφK hTT.2.2.1 hr0`.

Establish `hφ' : IsCMType (fun i => (g : ℂ →+* ℂ).comp (φ i))`. Establish `: (fun i => (g : ℂ →+* ℂ).comp (φ i)) = fun i => φ (π i)` using `funext hπ`. Rewrite using `[this]`. Conclude with `isCMType_comp hφ π`. Establish `hκπ : ∀ i, κ' (π i) = κ i` using `fun i => hκ i (π i) (fun x => by`.

Use `congrArg (fun h : E →+* ℂ => h x) (hπ i)` as an intermediate fact. Simplify using `using this)`. Establish `hSS'' : IsLatSum (fun i => (g : ℂ →+* ℂ).comp (φ i)) (2 * s) κ (lattice (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹)) S'` using `(isLatSum_iff φ _ π hπ κ κ' hκπ _ _ _).2 hSS'`. Establish `hSt` using `hS E I φ hf hφ`. Establish `hSt'` using `hS E I _ hf hφ'`.

Take `⟨⟨g₁, hg₁⟩, hD1⟩` from `((hSt.1 s hs).1 (condQ 𝔣 Q) y hc).1`. Take `⟨⟨g₂, hg₂⟩, hD2⟩` from `((hSt'.1 s hs).1 (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹) hc).1`. Establish `e1` using `((hD1 g₁ hg₁).2 κ u hu).1 S hSS`. Establish `e2` using `((hD2 g₂ hg₂).2 κ u hu).1 S' hSS''`. Establish `j1` using `hx (algebraMap Qb ℂ) (fun a => rfl) φ (condQ 𝔣 Q) y 1 hφ hc (hr I φ _ y hφ hc) T hOver g₁ u hg₁ hu`.

Establish `j2` using `hx ((g : ℂ →+* ℂ).comp (algebraMap Qb ℂ)) (fun a => hgq a) _ (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹) 1 hφ' hc (hr I _ _ _ hφ' hc) T' hOver' g₂ u hg₂ hu`. Rewrite `j1` using `[e1]`. Rewrite `j2` using `[e2]`. Establish `hcard : Fintype.card I = Module.finrank ℚ (FR E)` using `(Fintype.card_congr T.U.e).symm.trans (Fintype.card_fin _)`. Establish `hΩ0 : Ω₀ ≠ 0` using `hTT.1`.

Establish `hΩ1 : Ω₁ ≠ 0` using `hTT.2.1`. Establish `hAi : ∀ i, T.A i ≠ 0` using `fun i => (hA i).1`. Establish `hsq : ((Real.sqrt d : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `hB0 : ∀ i, T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi) ≠ 0` using `fun i => div_ne_zero (mul_ne_zero (mul_ne_zero (hAi i) (pow_ne_zero _ hΩ0)) hsq) (mul_ne_zero two_ne_zero hpi)`.

Establish `hA' : ∀ i, T'.A i ≠ 0`. Introduce `i h0`. Apply `hB0 i` to reduce the goal to its premises. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[hB i, h0]`.

Simplify using the standard rewrite rules. Establish `E1` using `coordIn_eq_of_jet E hd hs hcard κ ε hΩ0 hAi j1`. Establish `E2` using `coordIn_eq_of_jet E hd hs hcard κ ε hΩ1 hA' j2`. Establish `lin : ∀ a b, coordIn E d s κ Ω₁ (a * b) = a * coordIn E d s κ Ω₁ b` using `fun a b => by unfold coordIn; ring`. Establish `hP : g (∏ i, (T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i) = ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) * ∏ i, (T'.A i * Ω₁ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i`.

Rewrite using `[map_prod]`. Simplify using `only [map_pow, hB, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Establish `hQ2 : g (T.C / Ω₀ ^ Fintype.card I) ^ (2 * s) = (T'.C / Ω₁ ^ Fintype.card I) ^ (2 * s)`. Rewrite using `[pow_mul, hC, ← pow_mul]`. Establish `hsg : g ((-((ε : ℤ) : ℂ)) ^ (∑ i, κ i)) = (-((ε : ℤ) : ℂ)) ^ (∑ i, κ i)` using `by simp`.

Rewrite using `[lin, E2, E1, map_div₀, map_mul, map_mul, map_pow g (T.C / _), hQ2, hsg, hP, RingHom.comp_apply, RingEquiv.coe_toRingHom]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latConj (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hS : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement) (hE : EisRule) (hJ : JetCore)
    (hMA : ModelAlg) (hMC : ModelConj) : LatConj := by
  obtain ⟨ε, hJ⟩ := hJ
  intro K _ _ d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E _ _ _ _ I _ φ s 𝔣 Q hD κ κ' hκ y S S' hSS hSS'
  obtain ⟨hU, hφ, hφK, hs, hb, hQ⟩ := hD
  have hf : 2 ≤ Module.finrank ℚ (FR E) := two_le_finrank_of_unramFin E hU
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    unfold condQ
    refine mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  obtain ⟨𝔠, X₀, δ₀, N, T, hAdm, hOver, -, hA⟩ :=
    hMA K d δ ι hK2 hd hδ Λ₀ Ω₀ hTT.2.2.2.1 hΩ₀ E I φ hφ hφK (condQ 𝔣 Q) y hc
  obtain ⟨T', hOver', hC, hB⟩ :=
    hMC K d δ ι hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ hΩ₀ hTT E I φ hφ hφK (condQ 𝔣 Q) y hc 𝔠 X₀ δ₀ N T hOver
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  let R₀ : Subring ℂ := (algebraMap ℚ ℂ).range
  have hzR : ∀ C, (1 : ℂ) * ((z C / 2 ^ Module.finrank ℚ (FR E) : ℚ) : ℂ) ∈ R₀ := fun C => ⟨z C / 2 ^ Module.finrank ℚ (FR E), by simp⟩
  obtain ⟨r, hr⟩ := hE E hf 𝔠 s hs z hz R₀ 1 R₀.one_mem hzR
  have hmem : ∀ a : R₀, (a : ℂ) ∈ algebraicClosure ℚ ℂ := by
    rintro ⟨a, q, rfl⟩
    exact (algebraicClosure ℚ ℂ).algebraMap_mem q
  let f : R₀ →+* Qb :=
    { toFun := fun a => ⟨a, hmem a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra R₀ Qb := f.toAlgebra
  obtain ⟨x, hx⟩ := hJ E I 𝔠 hf R₀ s r hs Qb X₀ δ₀ N hAdm κ
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hgq : ∀ a : R₀, g (a : ℂ) = a := by
    rintro ⟨a, q, rfl⟩
    exact congrArg (fun h : ℚ →+* ℂ => h q) (Subsingleton.elim ((g : ℂ →+* ℂ).comp (algebraMap ℚ ℂ)) (algebraMap ℚ ℂ))
  have hr0 : ∃ x : K, starRingEnd ℂ (ι x) ≠ ι x := by
    refine ⟨δ, fun h => ?_⟩
    have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    obtain ⟨rr, hrr⟩ := Complex.conj_eq_iff_real.1 h
    rw [hrr] at h2
    have h3 := congrArg Complex.re h2
    have h4 : rr ^ 2 = -(d : ℝ) := by
      simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at h3; exact h3
    have : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg rr]
  obtain ⟨π, hπ⟩ := exists_perm ι φ g hφ hφK hTT.2.2.1 hr0
  have hφ' : IsCMType (fun i => (g : ℂ →+* ℂ).comp (φ i)) := by
    have : (fun i => (g : ℂ →+* ℂ).comp (φ i)) = fun i => φ (π i) := funext hπ
    rw [this]; exact isCMType_comp hφ π
  have hκπ : ∀ i, κ' (π i) = κ i := fun i => hκ i (π i) (fun x => by
    have := congrArg (fun h : E →+* ℂ => h x) (hπ i); simpa using this)
  have hSS'' : IsLatSum (fun i => (g : ℂ →+* ℂ).comp (φ i)) (2 * s) κ (lattice (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹)) S' :=
    (isLatSum_iff φ _ π hπ κ κ' hκπ _ _ _).2 hSS'
  have hSt := hS E I φ hf hφ
  have hSt' := hS E I _ hf hφ'
  obtain ⟨⟨g₁, hg₁⟩, hD1⟩ := ((hSt.1 s hs).1 (condQ 𝔣 Q) y hc).1
  obtain ⟨⟨g₂, hg₂⟩, hD2⟩ := ((hSt'.1 s hs).1 (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹) hc).1
  have e1 := ((hD1 g₁ hg₁).2 κ u hu).1 S hSS
  have e2 := ((hD2 g₂ hg₂).2 κ u hu).1 S' hSS''
  have j1 := hx (algebraMap Qb ℂ) (fun a => rfl) φ (condQ 𝔣 Q) y 1 hφ hc (hr I φ _ y hφ hc) T hOver g₁ u hg₁ hu
  have j2 := hx ((g : ℂ →+* ℂ).comp (algebraMap Qb ℂ)) (fun a => hgq a) _ (condQ 𝔣 Q) (y * (upIdele K E t)⁻¹) 1 hφ' hc
    (hr I _ _ _ hφ' hc) T' hOver' g₂ u hg₂ hu
  rw [e1] at j1
  rw [e2] at j2
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := (Fintype.card_congr T.U.e).symm.trans (Fintype.card_fin _)
  have hΩ0 : Ω₀ ≠ 0 := hTT.1
  have hΩ1 : Ω₁ ≠ 0 := hTT.2.1
  have hAi : ∀ i, T.A i ≠ 0 := fun i => (hA i).1
  have hsq : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hB0 : ∀ i, T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi) ≠ 0 := fun i =>
    div_ne_zero (mul_ne_zero (mul_ne_zero (hAi i) (pow_ne_zero _ hΩ0)) hsq) (mul_ne_zero two_ne_zero hpi)
  have hA' : ∀ i, T'.A i ≠ 0 := by
    intro i h0
    apply hB0 i
    apply g.injective
    rw [hB i, h0]; simp
  have E1 := coordIn_eq_of_jet E hd hs hcard κ ε hΩ0 hAi j1
  have E2 := coordIn_eq_of_jet E hd hs hcard κ ε hΩ1 hA' j2
  have lin : ∀ a b, coordIn E d s κ Ω₁ (a * b) = a * coordIn E d s κ Ω₁ b := fun a b => by unfold coordIn; ring
  have hP : g (∏ i, (T.A i * Ω₀ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i) =
      ((modF t : ℝ) : ℂ) ^ (∑ i, κ i) * ∏ i, (T'.A i * Ω₁ ^ 2 * (Real.sqrt d : ℝ) / (2 * Real.pi)) ^ κ i := by
    rw [map_prod]
    simp only [map_pow, hB, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hQ2 : g (T.C / Ω₀ ^ Fintype.card I) ^ (2 * s) = (T'.C / Ω₁ ^ Fintype.card I) ^ (2 * s) := by
    rw [pow_mul, hC, ← pow_mul]
  have hsg : g ((-((ε : ℤ) : ℂ)) ^ (∑ i, κ i)) = (-((ε : ℤ) : ℂ)) ^ (∑ i, κ i) := by simp
  rw [lin, E2, E1, map_div₀, map_mul, map_mul, map_pow g (T.C / _), hQ2, hsg, hP, RingHom.comp_apply,
    RingEquiv.coe_toRingHom]
  ring

end GlobalTheory.LatConjOne
