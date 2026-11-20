import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDehomCharpolyForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace DehomCharpolyForms

def homog {D : ℕ} (k : Fin (D + 1)) (N : ℕ) (G : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial (Fin (D + 1)) ℚ :=
  ∑ e ∈ Finset.range (N + 1), X k ^ (N - e) * homogeneousComponent e G

/- English proof (translation)
Use `conv_rhs => rw [← sum_homogeneousComponent G]`. Use `symm`. Use `Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun e he he' => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_range, not_lt] at he he'`. Apply `homogeneousComponent_eq_zero` to reduce the goal to its premises.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_homogeneousComponent_range {σ : Type*} (G : MvPolynomial σ ℚ) {N : ℕ} (hN : G.totalDegree ≤ N) :
    ∑ e ∈ Finset.range (N + 1), homogeneousComponent e G = G := by
  conv_rhs => rw [← sum_homogeneousComponent G]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun e he he' => ?_
  simp only [Finset.mem_range, not_lt] at he he'
  apply homogeneousComponent_eq_zero
  omega

/- English proof (translation)
Use `IsHomogeneous.sum _ _ _ fun e he => ?_` and prove the remaining obligations. Establish `he' : e ≤ N` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp he)`. Use `(isHomogeneous_X_pow (R := ℚ) k (N - e)).mul (homogeneousComponent_isHomogeneous e G)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel he']`. Then use the resulting hypothesis.
-/
theorem isHomogeneous_homog {D : ℕ} (k : Fin (D + 1)) (N : ℕ) (G : MvPolynomial (Fin (D + 1)) ℚ) :
    (homog k N G).IsHomogeneous N := by
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have he' : e ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  have := (isHomogeneous_X_pow (R := ℚ) k (N - e)).mul (homogeneousComponent_isHomogeneous e G)
  rwa [Nat.sub_add_cancel he'] at this

/- English proof (translation)
Rewrite using `[← FibreNormCharpoly.aeval_mul_of_isHomogeneous hF (l k)⁻¹ l]`. Simplify using `only [div_eq_inv_mul]`.
-/
theorem aeval_div_of_isHomogeneous {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} (l : Fin (D + 1) → Ω)
    (k : Fin (D + 1)) {F : MvPolynomial (Fin (D + 1)) ℚ} {e : ℕ} (hF : F.IsHomogeneous e) :
    aeval (fun i => l i / l k) F = (l k)⁻¹ ^ e * aeval l F := by
  rw [← FibreNormCharpoly.aeval_mul_of_isHomogeneous hF (l k)⁻¹ l]
  simp only [div_eq_inv_mul]

/- English proof (translation)
Use `conv_rhs => rw [← sum_homogeneousComponent_range G hN]`. Simplify using `only [homog, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e he => ?_` and prove the remaining obligations. Establish `he' : e ≤ N` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp he)`. Establish `hpow : l k ^ N = l k ^ (N - e) * l k ^ e` using `by rw [← pow_add, Nat.sub_add_cancel he']`.

Rewrite using `[aeval_div_of_isHomogeneous l k (homogeneousComponent_isHomogeneous e G), map_mul, map_pow, aeval_X, hpow, inv_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem aeval_homog {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} (l : Fin (D + 1) → Ω) (k : Fin (D + 1))
    (hk : l k ≠ 0) (G : MvPolynomial (Fin (D + 1)) ℚ) {N : ℕ} (hN : G.totalDegree ≤ N) :
    aeval l (homog k N G) = l k ^ N * aeval (fun i => l i / l k) G := by
  conv_rhs => rw [← sum_homogeneousComponent_range G hN]
  simp only [homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
  have hpow : l k ^ N = l k ^ (N - e) * l k ^ e := by rw [← pow_add, Nat.sub_add_cancel he']
  rw [aeval_div_of_isHomogeneous l k (homogeneousComponent_isHomogeneous e G), map_mul, map_pow, aeval_X, hpow,
    inv_pow]
  field_simp

/- English proof (translation)
Use `conv_rhs => rw [← sum_homogeneousComponent_range G hN]`. Simplify using `[PullFormsGeneric.dehom, homog, map_sum]`.
-/
theorem dehom_homog {D : ℕ} (k : Fin (D + 1)) {N : ℕ} (G : MvPolynomial (Fin (D + 1)) ℚ)
    (hN : G.totalDegree ≤ N) : PullFormsGeneric.dehom k (homog k N G) = PullFormsGeneric.dehom k G := by
  conv_rhs => rw [← sum_homogeneousComponent_range G hN]
  simp [PullFormsGeneric.dehom, homog, map_sum]

/- English proof (translation)
Introduce `h` and use `X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X, h]))`.
-/
theorem ne_zero_of_generic {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (k : Fin (D + 1)) : l k ≠ 0 := fun h =>
  X_ne_zero (R := ℚ) k (hgen 1 (X k) (isHomogeneous_X ℚ k) (by rw [aeval_X, h]))

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `G hG`. Use `set G' : MvPolynomial (Fin (D + 1)) ℚ := rename Subtype.val G with hG'`. Establish `h1 : aeval (fun i => l i / l k) G' = 0` using `by rw [hG', aeval_rename]; exact hG`. Establish `h2 : homog k G'.totalDegree G' = 0` using `hgen _ _ (isHomogeneous_homog k _ G') (by rw [aeval_homog l k (ne_zero_of_generic hgen k) G' le_rfl, h1, mul_zero])`.

Establish `h3 : PullFormsGeneric.dehom k G' = G`. Establish `: (bind₁ (fun i : Fin (D + 1) => if h : i = k then (1 : MvPolynomial {i // i ≠ k} ℚ) else X ⟨i, h⟩)).comp (rename (R` using `ℚ) (Subtype.val : {i // i ≠ k} → Fin (D + 1))) = AlgHom.id ℚ _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[i.2]`.

Conclude with `congrArg (fun φ => φ G) this`. Rewrite using `[← h3, ← dehom_homog k G' le_rfl, h2]`. Simplify using `[PullFormsGeneric.dehom]`.
-/
theorem injective_chart {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (k : Fin (D + 1)) :
    Function.Injective (aeval (R := ℚ) (fun i : {i // i ≠ k} => l i / l k)) := by
  rw [injective_iff_map_eq_zero]
  intro G hG
  set G' : MvPolynomial (Fin (D + 1)) ℚ := rename Subtype.val G with hG'
  have h1 : aeval (fun i => l i / l k) G' = 0 := by rw [hG', aeval_rename]; exact hG
  have h2 : homog k G'.totalDegree G' = 0 :=
    hgen _ _ (isHomogeneous_homog k _ G')
      (by rw [aeval_homog l k (ne_zero_of_generic hgen k) G' le_rfl, h1, mul_zero])
  have h3 : PullFormsGeneric.dehom k G' = G := by
    have : (bind₁ (fun i : Fin (D + 1) => if h : i = k then (1 : MvPolynomial {i // i ≠ k} ℚ)
        else X ⟨i, h⟩)).comp (rename (R := ℚ) (Subtype.val : {i // i ≠ k} → Fin (D + 1))) = AlgHom.id ℚ _ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [i.2]
    exact congrArg (fun φ => φ G) this
  rw [← h3, ← dehom_homog k G' le_rfl, h2]
  simp [PullFormsGeneric.dehom]

/- English proof (translation)
Introduce `μ hμ`. Establish `h1 : coeff (μ + Finsupp.single k a) (X k ^ a * H) = coeff μ H`. Rewrite using `[X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]`. Establish `h2` using `h (by rw [h1]; exact hμ)`. Simplify using `only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at h2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem isHomogeneous_of_X_pow_mul {σ : Type*} {k : σ} {a d : ℕ} {H : MvPolynomial σ ℚ}
    (h : (X k ^ a * H).IsHomogeneous (a + d)) : H.IsHomogeneous d := by
  intro μ hμ
  have h1 : coeff (μ + Finsupp.single k a) (X k ^ a * H) = coeff μ H := by
    rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]
  have h2 := h (by rw [h1]; exact hμ)
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at h2
  omega

/- English proof (translation)
Use `le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, k', -, rfl⟩`. Establish `: l i / l k' = (l i / l k) / (l k' / l k)` using `(div_div_div_cancel_right₀ (hl k) _ _).symm`. Rewrite using `[this]`. Conclude with `div_mem (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨k', rfl⟩)`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨i, k, hl k, rfl⟩`.
-/
theorem adjoin_ratios_eq {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω} (hl : ∀ k, l k ≠ 0)
    (k : Fin (D + 1)) :
    IntermediateField.adjoin ℚ {x | ∃ i k', l k' ≠ 0 ∧ x = l i / l k'} =
      IntermediateField.adjoin ℚ (Set.range fun i => l i / l k) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_) (IntermediateField.adjoin_le_iff.mpr ?_)
  · rintro _ ⟨i, k', -, rfl⟩
    have : l i / l k' = (l i / l k) / (l k' / l k) := (div_div_div_cancel_right₀ (hl k) _ _).symm
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨k', rfl⟩)
  · rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨i, k, hl k, rfl⟩

/- English proof (translation)
Use `le_antisymm (Algebra.adjoin_mono ?_) (Algebra.adjoin_le ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨i.1, rfl⟩`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `h : i = k`.

Substitute `h show l i / l i ∈ _` using the available equality. Rewrite using `[div_self (hl i)]`. Conclude with `one_mem _`. Conclude with `Algebra.subset_adjoin ⟨⟨i, h⟩, rfl⟩`.
-/
theorem adjoin_chart_eq {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω} (hl : ∀ k, l k ≠ 0)
    (k : Fin (D + 1)) :
    Algebra.adjoin ℚ (Set.range fun i : {i // i ≠ k} => l i / l k) =
      Algebra.adjoin ℚ (Set.range fun i => l i / l k) := by
  refine le_antisymm (Algebra.adjoin_mono ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨i, rfl⟩
    exact ⟨i.1, rfl⟩
  · rintro _ ⟨i, rfl⟩
    by_cases h : i = k
    · subst h
      show l i / l i ∈ _
      rw [div_self (hl i)]
      exact one_mem _
    · exact Algebra.subset_adjoin ⟨⟨i, h⟩, rfl⟩

/- English proof (translation)
Establish `hr : (aeval (R` using `ℚ) (fun i : {i // i ≠ k} => l i / l k)).range = Algebra.adjoin ℚ (Set.range fun i => l i / l k) := by`. Rewrite using `[← Algebra.adjoin_range_eq_range_aeval, adjoin_chart_eq (ne_zero_of_generic hgen) k]`. Set `e` to `(AlgEquiv.ofInjective _ (injective_chart hgen k)).trans (Subalgebra.equivOfEq _ _ hr)`. Establish `: UniqueFactorizationMonoid (Algebra.adjoin ℚ (Set.range fun i => l i / l k))` using `e.toMulEquiv.uniqueFactorizationMonoid inferInstance`. Use `infer_instance`.
-/
theorem isIntegrallyClosed_chart {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (k : Fin (D + 1)) : IsIntegrallyClosed (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) := by
  have hr : (aeval (R := ℚ) (fun i : {i // i ≠ k} => l i / l k)).range =
      Algebra.adjoin ℚ (Set.range fun i => l i / l k) := by
    rw [← Algebra.adjoin_range_eq_range_aeval, adjoin_chart_eq (ne_zero_of_generic hgen) k]
  let e := (AlgEquiv.ofInjective _ (injective_chart hgen k)).trans (Subalgebra.equivOfEq _ _ hr)
  have : UniqueFactorizationMonoid (Algebra.adjoin ℚ (Set.range fun i => l i / l k)) :=
    e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  infer_instance

/- English proof (translation)
Establish `hl` using `ne_zero_of_generic hgen`. Establish `hG : ∀ k, ∃ G : MvPolynomial (Fin (D + 1)) ℚ, aeval (fun i => l i / l k) G = x * (l j / l k) ^ d`. Introduce `k`. Use `hx k` as an intermediate fact. Rewrite `this` using `[Algebra.adjoin_range_eq_range_aeval]`.

Take `⟨G, hG⟩` from `this`. Conclude with `⟨G, hG⟩`. Use `choose G hG using hG`. Distinguish the cases in `hD : ∃ k, k ≠ j`. Take `⟨k, hkj⟩` from `hD set Nj := (G j).totalDegree set Nk := (G k).totalDegree`.

Establish `hFj : aeval l (homog j Nj (G j)) = l j ^ Nj * x`. Rewrite using `[aeval_homog l j (hl j) (G j) le_rfl, hG j, div_self (hl j), one_pow, mul_one]`. Establish `hFk : aeval l (homog k Nk (G k)) = l k ^ Nk * (x * (l j / l k) ^ d)`. Rewrite using `[aeval_homog l k (hl k) (G k) le_rfl, hG k]`. Establish `hEq : homog j Nj (G j) * X j ^ d * X k ^ Nk = homog k Nk (G k) * X k ^ d * X j ^ Nj`.

Use `sub_eq_zero.mp (hgen (Nj + d + Nk) _ ?_ ?_)` and prove the remaining obligations. Use `IsHomogeneous.sub (((isHomogeneous_homog j Nj _).mul (isHomogeneous_X_pow j d)).mul (isHomogeneous_X_pow k Nk)) ?_` and prove the remaining obligations. Use `((isHomogeneous_homog k Nk (G k)).mul (isHomogeneous_X_pow (R := ℚ) k d)).mul (isHomogeneous_X_pow (R := ℚ) j Nj)` as an intermediate fact. Rewrite `this` using `[show Nk + d + Nj = Nj + d + Nk by ring]`. Then use the resulting hypothesis. Simplify using `only [map_sub, map_mul, map_pow, aeval_X, hFj, hFk]`.

Establish `h3 : (l j / l k) ^ d * l k ^ d = l j ^ d`. Rewrite using `[div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hl k))]`. Take the linear combination `(-(l k ^ Nk * x * l j ^ Nj)) * h3`. Establish `hnd : ¬ (X j : MvPolynomial (Fin (D + 1)) ℚ) ∣ X k ^ Nk` using `fun h => hkj ((X_dvd_X.mp (X_prime.dvd_of_dvd_pow h)).symm)`. Establish `hdvd : (X j : MvPolynomial (Fin (D + 1)) ℚ) ^ Nj ∣ homog j Nj (G j) * X j ^ d` using `X_prime.pow_dvd_of_dvd_mul_right Nj hnd (by rw [hEq]; exact Dvd.intro_left _ rfl)`.

Take `⟨H, hH⟩` from `hdvd`. Establish `hHhom : H.IsHomogeneous d`. Apply `isHomogeneous_of_X_pow_mul (k := j) (a := Nj)` to reduce the goal to its premises. Rewrite using `[← hH]`. Conclude with `(isHomogeneous_homog j Nj _).mul (isHomogeneous_X_pow j d)`.

Establish `hHl : aeval l H = x * l j ^ d`. Establish `h1` using `congrArg (aeval l) hH`. Simplify using `only [map_mul, map_pow, aeval_X, hFj] at h1`. Establish `h2 : l j ^ Nj ≠ 0` using `pow_ne_zero _ (hl j)`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises.

Rewrite using `[← h1]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨H, hHhom, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_div_of_isHomogeneous l j hHhom, hHl, inv_pow, ← mul_assoc, mul_comm _ x, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (hl j)), mul_one]`. Use `push Not at hD`.

Establish `hx'` using `hx j`. Rewrite `hx'` using `[div_self (hl j), one_pow, mul_one]`. Establish `hbot : Algebra.adjoin ℚ (Set.range fun i => l i / l j) ≤ ⊥`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `show l i / l j ∈ _`. Rewrite using `[hD i, div_self (hl j)]`. Conclude with `one_mem _`. Take `⟨q, hq⟩` from `Algebra.mem_bot.mp (hbot hx')`. Use `⟨C q * X j ^ d, isHomogeneous_C_mul_X_pow q j d, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, aeval_C, map_pow, aeval_X, div_self (hl j), one_pow, mul_one, hq]`.
-/
theorem exists_form_of_charts {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (j : Fin (D + 1)) (d : ℕ) (x : Ω)
    (hx : ∀ k, x * (l j / l k) ^ d ∈ Algebra.adjoin ℚ (Set.range fun i => l i / l k)) :
    ∃ c : MvPolynomial (Fin (D + 1)) ℚ, c.IsHomogeneous d ∧ aeval (fun i => l i / l j) c = x := by
  classical
  have hl := ne_zero_of_generic hgen
  have hG : ∀ k, ∃ G : MvPolynomial (Fin (D + 1)) ℚ, aeval (fun i => l i / l k) G = x * (l j / l k) ^ d := by
    intro k
    have := hx k
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    obtain ⟨G, hG⟩ := this
    exact ⟨G, hG⟩
  choose G hG using hG
  by_cases hD : ∃ k, k ≠ j
  · obtain ⟨k, hkj⟩ := hD
    set Nj := (G j).totalDegree
    set Nk := (G k).totalDegree
    have hFj : aeval l (homog j Nj (G j)) = l j ^ Nj * x := by
      rw [aeval_homog l j (hl j) (G j) le_rfl, hG j, div_self (hl j), one_pow, mul_one]
    have hFk : aeval l (homog k Nk (G k)) = l k ^ Nk * (x * (l j / l k) ^ d) := by
      rw [aeval_homog l k (hl k) (G k) le_rfl, hG k]
    have hEq : homog j Nj (G j) * X j ^ d * X k ^ Nk = homog k Nk (G k) * X k ^ d * X j ^ Nj := by
      refine sub_eq_zero.mp (hgen (Nj + d + Nk) _ ?_ ?_)
      · refine IsHomogeneous.sub (((isHomogeneous_homog j Nj _).mul (isHomogeneous_X_pow j d)).mul
          (isHomogeneous_X_pow k Nk)) ?_
        have := ((isHomogeneous_homog k Nk (G k)).mul (isHomogeneous_X_pow (R := ℚ) k d)).mul
          (isHomogeneous_X_pow (R := ℚ) j Nj)
        rwa [show Nk + d + Nj = Nj + d + Nk by ring] at this
      · simp only [map_sub, map_mul, map_pow, aeval_X, hFj, hFk]
        have h3 : (l j / l k) ^ d * l k ^ d = l j ^ d := by
          rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hl k))]
        linear_combination (-(l k ^ Nk * x * l j ^ Nj)) * h3
    have hnd : ¬ (X j : MvPolynomial (Fin (D + 1)) ℚ) ∣ X k ^ Nk := fun h =>
      hkj ((X_dvd_X.mp (X_prime.dvd_of_dvd_pow h)).symm)
    have hdvd : (X j : MvPolynomial (Fin (D + 1)) ℚ) ^ Nj ∣ homog j Nj (G j) * X j ^ d :=
      X_prime.pow_dvd_of_dvd_mul_right Nj hnd (by rw [hEq]; exact Dvd.intro_left _ rfl)
    obtain ⟨H, hH⟩ := hdvd
    have hHhom : H.IsHomogeneous d := by
      apply isHomogeneous_of_X_pow_mul (k := j) (a := Nj)
      rw [← hH]
      exact (isHomogeneous_homog j Nj _).mul (isHomogeneous_X_pow j d)
    have hHl : aeval l H = x * l j ^ d := by
      have h1 := congrArg (aeval l) hH
      simp only [map_mul, map_pow, aeval_X, hFj] at h1
      have h2 : l j ^ Nj ≠ 0 := pow_ne_zero _ (hl j)
      apply mul_left_cancel₀ h2
      rw [← h1]
      ring
    refine ⟨H, hHhom, ?_⟩
    rw [aeval_div_of_isHomogeneous l j hHhom, hHl, inv_pow, ← mul_assoc, mul_comm _ x, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ (hl j)), mul_one]
  · push Not at hD
    have hx' := hx j
    rw [div_self (hl j), one_pow, mul_one] at hx'
    have hbot : Algebra.adjoin ℚ (Set.range fun i => l i / l j) ≤ ⊥ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      show l i / l j ∈ _
      rw [hD i, div_self (hl j)]
      exact one_mem _
    obtain ⟨q, hq⟩ := Algebra.mem_bot.mp (hbot hx')
    refine ⟨C q * X j ^ d, isHomogeneous_C_mul_X_pow q j d, ?_⟩
    rw [map_mul, aeval_C, map_pow, aeval_X, div_self (hl j), one_pow, mul_one, hq]

/- English proof (translation)
Establish `hinj : Set.InjOn (fun q : ℕ => (q : K)) (Finset.range (n + 1) : Set ℕ)` using `Nat.cast_injective.injOn`. Establish `hlt : g.degree < (Finset.range (n + 1)).card`. Rewrite using `[Finset.card_range]`. Conclude with `Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hdeg)`. Establish `hg` using `Lagrange.eq_interpolate hinj hlt`.

Establish `hmemR : ∀ c ∈ B, Polynomial.C c ∈ Polynomial.liftsRing B.subtype` using `fun c hc => (Polynomial.lifts_iff_liftsRing _ _).mp (by simpa using Polynomial.C_mem_lifts B.subtype ⟨c, hc⟩)`. Establish `hXR : (Polynomial.X : Polynomial K) ∈ Polynomial.liftsRing B.subtype` using `(Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.X_mem_lifts _)`. Establish `hmem : g ∈ Polynomial.liftsRing B.subtype`. Rewrite using `[hg, Lagrange.interpolate_apply]`. Use `Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hmemR _ (hval a)) ?_` and prove the remaining obligations.

Rewrite using `[Lagrange.basis]`. Use `Subring.prod_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Lagrange.basisDivisor]`. Use `Subring.mul_mem _ (hmemR _ ?_) (Subring.sub_mem _ hXR (hmemR _ ?_))` and prove the remaining obligations. Use `hQ (((a : ℚ) - b)⁻¹)` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Use `hQ (b : ℚ)` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.

Rewrite `hmem` using `[← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]`. Take `⟨c, hc⟩` from `hmem i`. Rewrite using `[← hc]`. Conclude with `c.2`.
-/
theorem coeff_mem_of_eval_mem {K : Type*} [Field K] [CharZero K] (B : Subring K) {g : Polynomial K} {n : ℕ}
    (hdeg : g.natDegree ≤ n) (hval : ∀ q : ℕ, g.eval (q : K) ∈ B) (hQ : ∀ q : ℚ, (q : K) ∈ B) (i : ℕ) :
    g.coeff i ∈ B := by
  classical
  have hinj : Set.InjOn (fun q : ℕ => (q : K)) (Finset.range (n + 1) : Set ℕ) := Nat.cast_injective.injOn
  have hlt : g.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hdeg)
  have hg := Lagrange.eq_interpolate hinj hlt
  have hmemR : ∀ c ∈ B, Polynomial.C c ∈ Polynomial.liftsRing B.subtype := fun c hc =>
    (Polynomial.lifts_iff_liftsRing _ _).mp (by simpa using Polynomial.C_mem_lifts B.subtype ⟨c, hc⟩)
  have hXR : (Polynomial.X : Polynomial K) ∈ Polynomial.liftsRing B.subtype :=
    (Polynomial.lifts_iff_liftsRing _ _).mp (Polynomial.X_mem_lifts _)
  have hmem : g ∈ Polynomial.liftsRing B.subtype := by
    rw [hg, Lagrange.interpolate_apply]
    refine Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hmemR _ (hval a)) ?_
    rw [Lagrange.basis]
    refine Subring.prod_mem _ fun b _ => ?_
    rw [Lagrange.basisDivisor]
    refine Subring.mul_mem _ (hmemR _ ?_) (Subring.sub_mem _ hXR (hmemR _ ?_))
    · have := hQ (((a : ℚ) - b)⁻¹)
      push_cast at this
      exact this
    · have := hQ (b : ℚ)
      push_cast at this
      exact this
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hmem
  obtain ⟨c, hc⟩ := hmem i
  rw [← hc]
  exact c.2

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (IntermediateField.adjoin ℚ S) hy)`. Rewrite using `[← ha]`. Conclude with `a.2`.
-/
theorem norm_mem_adjoin {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) [IsIntegrallyClosed (Algebra.adjoin ℚ S)]
    {y : Ω} (hy : IsIntegral (Algebra.adjoin ℚ S) y) :
    ((Algebra.norm (IntermediateField.adjoin ℚ S) y : IntermediateField.adjoin ℚ S) : Ω) ∈
      Algebra.adjoin ℚ S := by
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm (IntermediateField.adjoin ℚ S) hy)
  rw [← ha]
  exact a.2

/- English proof (translation)
Use `set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf`. Establish `hdeg : f.natDegree = Module.finrank P Ω` using `LinearMap.charpoly_natDegree _`. Rewrite using `[← hdeg, ← Polynomial.coeff_scaleRoots]`. Set `B : Subring P` to `(Subalgebra.comap P.val (Algebra.adjoin ℚ S)).toSubring`. Establish `hB : ∀ z : P, z ∈ B ↔ (z : Ω) ∈ Algebra.adjoin ℚ S` using `fun z => Iff.rfl`.

Rewrite using `[← hB]`. Use `coeff_mem_of_eval_mem B (n := f.natDegree) (Polynomial.natDegree_scaleRoots _ _).le ?_ ?_ i` and prove the remaining obligations. Introduce `q`. Establish `heq : (f.scaleRoots s).eval (q : P) = Algebra.norm P ((q : Ω) - (s : Ω) * u)`. Establish `h1 : (q : P) = s * ((q : P) / s)` using `by rw [mul_comm, div_mul_cancel₀ _ hs]`.

Establish `h2 : f.eval ((q : P) / s) = Algebra.norm P (algebraMap P Ω ((q : P) / s) - u)`. Rewrite using `[hf, LinearMap.eval_charpoly, Algebra.norm_apply, map_sub (Algebra.lmul P Ω), AlgHom.commutes]`. Rewrite using `[h1, Polynomial.scaleRoots_eval_mul, h2, hdeg, ← Algebra.norm_algebraMap (S := Ω), ← map_mul]`. Use `congr 1`. Rewrite using `[mul_sub, ← map_mul, ← h1]`.

Simplify using the standard rewrite rules. Rewrite using `[hB, heq]`. Substitute `hP` using the available equality. Use `norm_mem_adjoin S (IsIntegral.sub ?_ hint)` and prove the remaining obligations. Use `isIntegral_algebraMap (R := Algebra.adjoin ℚ S) (A := Ω) (x := (q : Algebra.adjoin ℚ S))` as an intermediate fact.

Simplify using `using this`. Introduce `q`. Rewrite using `[hB]`. Use `(Algebra.adjoin ℚ S).algebraMap_mem q` as an intermediate fact. Simplify using `using this`.
-/
theorem coeff_mul_pow_mem {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω] (hP : P = IntermediateField.adjoin ℚ S) [IsIntegrallyClosed (Algebra.adjoin ℚ S)]
    (u : Ω) (s : P) (hs : s ≠ 0) (hint : IsIntegral (Algebra.adjoin ℚ S) ((s : Ω) * u)) (i : ℕ) :
    (((LinearMap.charpoly (Algebra.lmul P Ω u)).coeff i * s ^ (Module.finrank P Ω - i) : P) : Ω) ∈
      Algebra.adjoin ℚ S := by
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf
  have hdeg : f.natDegree = Module.finrank P Ω := LinearMap.charpoly_natDegree _
  rw [← hdeg, ← Polynomial.coeff_scaleRoots]
  let B : Subring P := (Subalgebra.comap P.val (Algebra.adjoin ℚ S)).toSubring
  have hB : ∀ z : P, z ∈ B ↔ (z : Ω) ∈ Algebra.adjoin ℚ S := fun z => Iff.rfl
  rw [← hB]
  refine coeff_mem_of_eval_mem B (n := f.natDegree) (Polynomial.natDegree_scaleRoots _ _).le ?_ ?_ i
  · intro q
    have heq : (f.scaleRoots s).eval (q : P) = Algebra.norm P ((q : Ω) - (s : Ω) * u) := by
      have h1 : (q : P) = s * ((q : P) / s) := by rw [mul_comm, div_mul_cancel₀ _ hs]
      have h2 : f.eval ((q : P) / s) = Algebra.norm P (algebraMap P Ω ((q : P) / s) - u) := by
        rw [hf, LinearMap.eval_charpoly, Algebra.norm_apply, map_sub (Algebra.lmul P Ω), AlgHom.commutes]
      rw [h1, Polynomial.scaleRoots_eval_mul, h2, hdeg, ← Algebra.norm_algebraMap (S := Ω), ← map_mul]
      congr 1
      rw [mul_sub, ← map_mul, ← h1]
      simp
    rw [hB, heq]
    subst hP
    refine norm_mem_adjoin S (IsIntegral.sub ?_ hint)
    have := isIntegral_algebraMap (R := Algebra.adjoin ℚ S) (A := Ω) (x := (q : Algebra.adjoin ℚ S))
    simpa using this
  · intro q
    rw [hB]
    have := (Algebra.adjoin ℚ S).algebraMap_mem q
    simpa using this

end DehomCharpolyForms

open DehomCharpolyForms in

/- English proof (translation)
Introduce `Ω _ _ D l P _ hP hgen j m u hu`. Establish `hl` using `ne_zero_of_generic hgen`. Establish `hPk : ∀ k, P = IntermediateField.adjoin ℚ (Set.range fun i => l i / l k)` using `fun k => hP.trans (adjoin_ratios_eq hl k)`. Use `set n := Module.finrank P Ω with hn`. Use `set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf`.

Establish `hmem : ∀ i ≤ n, ∀ k, ((f.coeff (n - i) : P) : Ω) * (l j / l k) ^ (i * m) ∈ Algebra.adjoin ℚ (Set.range fun i' => l i' / l k)`. Introduce `i hi k`. Establish `hsP : (l j / l k) ^ m ∈ P`. Establish `h1 : l j / l k ∈ {x : Ω | ∃ i k, l k ≠ 0 ∧ x = l i / l k}` using `⟨j, k, hl k, rfl⟩`. Rewrite using `[hP]`.

Conclude with `pow_mem (IntermediateField.subset_adjoin ℚ _ h1) m`. Establish `hs0 : (⟨(l j / l k) ^ m, hsP⟩ : ↥P) ≠ 0` using `fun h => pow_ne_zero m (div_ne_zero (hl j) (hl k)) (congrArg Subtype.val h)`. Establish `hint : IsIntegral (Algebra.adjoin ℚ (Set.range fun i' => l i' / l k)) (((⟨(l j / l k) ^ m, hsP⟩ : ↥P) : Ω) * u)`. Rewrite using `[mul_comm]`. Conclude with `(mem_integralClosure_iff _ _).mp (hu k)`.

Use `isIntegrallyClosed_chart hgen k` as an intermediate fact. Establish `key` using `coeff_mul_pow_mem _ P (hPk k) u _ hs0 hint (n - i)`. Rewrite `key` using `[Nat.sub_sub_self hi]`. Establish `e : (l j / l k) ^ (i * m) = ((l j / l k) ^ m) ^ i` using `by rw [← pow_mul, mul_comm]`. Rewrite using `[e]`.

Conclude with `key`. Establish `hc : ∀ i ≤ n, ∃ c : MvPolynomial (Fin (D + 1)) ℚ, c.IsHomogeneous (i * m) ∧ aeval (fun i' => l i' / l j) c = ((f.coeff (n - i) : P) : Ω)` using `fun i hi => exists_form_of_charts hgen j (i * m) _ (hmem i hi)`. Use `choose! c hchom hceval using hc`. Establish `hmon : f.Monic` using `LinearMap.charpoly_monic _`. Establish `hdeg : f.natDegree = n` using `LinearMap.charpoly_natDegree _`.

Establish `heval : ∀ i ≤ n, aeval (fun i' => l i' / l j) (if i = 0 then 1 else c i) = ((f.coeff (n - i) : P) : Ω)`. Introduce `i hi`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[map_one, Nat.sub_zero, ← hdeg, hmon.coeff_natDegree, IntermediateField.coe_one]`.

Conclude with `hceval i hi`. Use `⟨fun i => if i = 0 then 1 else c i, by simp, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi dsimp only split_ifs with h`. Substitute `h` using the available equality. Simplify using `using isHomogeneous_one (σ := Fin (D + 1)) (R := ℚ)`.

Conclude with `hchom i hi`. Use `conv_lhs => rw [f.as_sum_range_C_mul_X_pow, hdeg]`. Rewrite using `[Polynomial.map_sum, ← Finset.sum_range_reflect]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`.

Rewrite using `[heval i hi', Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, show n + 1 - 1 - i = n - i by omega]`. Both sides reduce to the same expression. Introduce `hu0 hcn`. Establish `hn0 : n ≠ 0` using `Module.finrank_pos.ne'`. Establish `h0 : ((f.coeff 0 : P) : Ω) = 0`.

Establish `hcn' : c n = 0` using `by simpa [hn0] using hcn`. Use `heval n le_rfl` as an intermediate fact. Rewrite `this` using `[if_neg hn0, hcn', map_zero, Nat.sub_self]`. Conclude with `this.symm`. Establish `hdet` using `LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)`.

Rewrite `hdet` using `[← Algebra.norm_apply, ← hf]`. Establish `hN : Algebra.norm P u ≠ 0` using `Algebra.norm_ne_zero_iff.mpr hu0`. Apply `hN` to reduce the goal to its premises. Rewrite using `[hdet, show f.coeff 0 = 0 from Subtype.ext h0, mul_zero]`.
-/
theorem DehomCharpolyForms.proof : DehomCharpolyForms.Statement := by
  intro Ω _ _ D l P _ hP hgen j m u hu
  classical
  have hl := ne_zero_of_generic hgen
  have hPk : ∀ k, P = IntermediateField.adjoin ℚ (Set.range fun i => l i / l k) := fun k =>
    hP.trans (adjoin_ratios_eq hl k)
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf
  have hmem : ∀ i ≤ n, ∀ k, ((f.coeff (n - i) : P) : Ω) * (l j / l k) ^ (i * m) ∈
      Algebra.adjoin ℚ (Set.range fun i' => l i' / l k) := by
    intro i hi k
    have hsP : (l j / l k) ^ m ∈ P := by
      have h1 : l j / l k ∈ {x : Ω | ∃ i k, l k ≠ 0 ∧ x = l i / l k} := ⟨j, k, hl k, rfl⟩
      rw [hP]
      exact pow_mem (IntermediateField.subset_adjoin ℚ _ h1) m
    have hs0 : (⟨(l j / l k) ^ m, hsP⟩ : ↥P) ≠ 0 := fun h =>
      pow_ne_zero m (div_ne_zero (hl j) (hl k)) (congrArg Subtype.val h)
    have hint : IsIntegral (Algebra.adjoin ℚ (Set.range fun i' => l i' / l k))
        (((⟨(l j / l k) ^ m, hsP⟩ : ↥P) : Ω) * u) := by
      rw [mul_comm]
      exact (mem_integralClosure_iff _ _).mp (hu k)
    have := isIntegrallyClosed_chart hgen k
    have key := coeff_mul_pow_mem _ P (hPk k) u _ hs0 hint (n - i)
    rw [Nat.sub_sub_self hi] at key
    have e : (l j / l k) ^ (i * m) = ((l j / l k) ^ m) ^ i := by rw [← pow_mul, mul_comm]
    rw [e]
    exact key
  have hc : ∀ i ≤ n, ∃ c : MvPolynomial (Fin (D + 1)) ℚ, c.IsHomogeneous (i * m) ∧
      aeval (fun i' => l i' / l j) c = ((f.coeff (n - i) : P) : Ω) := fun i hi =>
    exists_form_of_charts hgen j (i * m) _ (hmem i hi)
  choose! c hchom hceval using hc
  have hmon : f.Monic := LinearMap.charpoly_monic _
  have hdeg : f.natDegree = n := LinearMap.charpoly_natDegree _
  have heval : ∀ i ≤ n, aeval (fun i' => l i' / l j) (if i = 0 then 1 else c i) = ((f.coeff (n - i) : P) : Ω) := by
    intro i hi
    split_ifs with h
    · subst h
      rw [map_one, Nat.sub_zero, ← hdeg, hmon.coeff_natDegree, IntermediateField.coe_one]
    · exact hceval i hi
  refine ⟨fun i => if i = 0 then 1 else c i, by simp, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only
    split_ifs with h
    · subst h
      simpa using isHomogeneous_one (σ := Fin (D + 1)) (R := ℚ)
    · exact hchom i hi
  · conv_lhs => rw [f.as_sum_range_C_mul_X_pow, hdeg]
    rw [Polynomial.map_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [heval i hi', Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
      show n + 1 - 1 - i = n - i by omega]
    rfl
  · intro hu0 hcn
    have hn0 : n ≠ 0 := Module.finrank_pos.ne'
    have h0 : ((f.coeff 0 : P) : Ω) = 0 := by
      have hcn' : c n = 0 := by simpa [hn0] using hcn
      have := heval n le_rfl
      rw [if_neg hn0, hcn', map_zero, Nat.sub_self] at this
      exact this.symm
    have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)
    rw [← Algebra.norm_apply, ← hf] at hdet
    have hN : Algebra.norm P u ≠ 0 := Algebra.norm_ne_zero_iff.mpr hu0
    apply hN
    rw [hdet, show f.coeff 0 = 0 from Subtype.ext h0, mul_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
