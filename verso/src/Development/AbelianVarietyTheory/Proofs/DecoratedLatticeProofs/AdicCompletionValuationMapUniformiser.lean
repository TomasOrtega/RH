import Mathlib
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ v k _ _ _ _ φ hφ ϖ hϖ`. Establish `hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c`. Introduce `c hc hu`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `hw' : φ (c : k) * φ (w : k) = 1`.

Rewrite using `[← map_mul, ← map_one φ]`. Use `congr 1`. Conclude with `congrArg (fun t : 𝒪[k] => (t : k)) hw` after adjusting the coercions. Establish `h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1`. Rewrite using `[← map_mul, hw', map_one]`.

Establish `h2 : Valued.v (φ (w : k)) ≤ 1` using `(hφ _).2 w.2`. Establish `h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1` using `by gcongr`. Rewrite `h3` using `[h1, mul_one]`. Conclude with `absurd hc (not_lt.2 h3)`. Use `set x := φ (ϖ : k) with hxdef`.

Establish `hϖ0 : (ϖ : k) ≠ 0`. Introduce `h`. Conclude with `hϖ.ne_zero (Subtype.ext h)`. Establish `hx0 : x ≠ 0`. Simplify `hϖ0` using `[hxdef]`.

Establish `hvx0 : Valued.v x ≠ 0`. Simplify using `using hx0`. Establish `hvx1 : Valued.v x < 1`. Establish `hle : Valued.v x ≤ 1` using `(hφ _).2 ϖ.2`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations.

Introduce `heq`. Apply `hϖ.not_isUnit` to reduce the goal to its premises. Establish `hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k]`. Use `(hφ _).1 ?_` and prove the remaining obligations. Rewrite using `[map_inv₀, map_inv₀, ← hxdef, heq, inv_one]`.

Use `IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[mul_inv_cancel₀ hϖ0]`. Take `⟨π₀, hπ₀⟩` from `HeightOneSpectrum.valuedAdicCompletion_surjective F v ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Establish `hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1`.

Rewrite using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Use `show (-1 : ℤ) < 0`. Evaluate the numerical expressions. Establish `hvπ0 : Valued.v π₀ ≠ 0` using `by rw [hπ₀]; exact WithZero.coe_ne_zero`. Establish `hπ0 : π₀ ≠ 0`.

Introduce `h`. Apply `hvπ0` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Use `set a := φ.symm π₀ with hadef`. Establish `hφa : φ a = π₀` using `by simp [hadef]`.

Establish `ha0 : a ≠ 0`. Introduce `h`. Apply `hπ0` to reduce the goal to its premises. Rewrite using `[← hφa, h, map_zero]`. Establish `ha : a ∈ 𝒪[k]` using `(hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)`.

Apply `le_antisymm` to reduce the goal to its premises. Take `⟨m, hm⟩` from `WithZero.ne_zero_iff_exists.1 hvx0`. Rewrite `hvx1`, the goal using `[← hm]`. Rewrite `hvx1` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Rewrite using `[WithZero.coe_le_coe]`.

Establish `h1 : Multiplicative.toAdd m < 0` using `hvx1`. Use `show Multiplicative.toAdd m ≤ -1`. Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_le]`.

Use `set b := (ϖ : k) / a with hbdef`. Establish `hφb : Valued.v (φ b) < 1`. Rewrite using `[hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]`. Conclude with `hcon`. Establish `hb : b ∈ 𝒪[k]` using `(hφ b).1 hφb.le`.

Establish `hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (ϖ : k) = a * ((ϖ : k) / a)`. Rewrite using `[mul_div_cancel₀ _ ha0]`. Break down `hϖ.isUnit_or_isUnit hprod with h | h` into its components or cases.

Conclude with `hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h`. Conclude with `hnu ⟨b, hb⟩ hφb h`.
-/
theorem adicCompletion_valuation_map_uniformiser : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  intro F _ _ v k _ _ _ _ φ hφ ϖ hϖ

  have hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c := by
    intro c hc hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : φ (c : k) * φ (w : k) = 1 := by
      rw [← map_mul, ← map_one φ]
      congr 1
      exact_mod_cast congrArg (fun t : 𝒪[k] => (t : k)) hw
    have h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1 := by
      rw [← map_mul, hw', map_one]
    have h2 : Valued.v (φ (w : k)) ≤ 1 := (hφ _).2 w.2
    have h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1 :=
      by gcongr
    rw [h1, mul_one] at h3
    exact absurd hc (not_lt.2 h3)
  set x := φ (ϖ : k) with hxdef
  have hϖ0 : (ϖ : k) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    simpa [hxdef] using hϖ0
  have hvx0 : Valued.v x ≠ 0 := by
    simpa using hx0
  have hvx1 : Valued.v x < 1 := by
    have hle : Valued.v x ≤ 1 := (hφ _).2 ϖ.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hϖ.not_isUnit
    have hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k] := by
      refine (hφ _).1 ?_
      rw [map_inv₀, map_inv₀, ← hxdef, heq, inv_one]
    refine IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_
    apply Subtype.ext
    simp [mul_inv_cancel₀ hϖ0]
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  have hvπ0 : Valued.v π₀ ≠ 0 := by rw [hπ₀]; exact WithZero.coe_ne_zero
  have hπ0 : π₀ ≠ 0 := by
    intro h; apply hvπ0; rw [h, map_zero]
  set a := φ.symm π₀ with hadef
  have hφa : φ a = π₀ := by simp [hadef]
  have ha0 : a ≠ 0 := by
    intro h; apply hπ0; rw [← hφa, h, map_zero]
  have ha : a ∈ 𝒪[k] := (hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)
  apply le_antisymm
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 hvx0
    rw [← hm] at hvx1 ⊢
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hvx1
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := hvx1
    show Multiplicative.toAdd m ≤ -1
    omega
  · by_contra hcon
    rw [not_le] at hcon
    set b := (ϖ : k) / a with hbdef
    have hφb : Valued.v (φ b) < 1 := by
      rw [hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]
      exact hcon
    have hb : b ∈ 𝒪[k] := (hφ b).1 hφb.le
    have hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩ := by
      apply Subtype.ext
      show (ϖ : k) = a * ((ϖ : k) / a)
      rw [mul_div_cancel₀ _ ha0]
    rcases hϖ.isUnit_or_isUnit hprod with h | h
    · exact hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h
    · exact hnu ⟨b, hb⟩ hφb h

end GlobalTheory
