import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HigherUnitsLeSquaresHigherUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits

open NumberField IsDedekindDomain IsLocalRing Polynomial

namespace GlobalTheory.QNorm

/- English proof (translation)
Use `Fintype.ofFinite k` as an intermediate fact. Establish `hc : ringChar k ≠ 2`. Introduce `h`. Apply `h2` to reduce the goal to its premises. Use `ringChar.Nat.cast_ringChar (R := k)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `this` after adjusting the coercions. Establish `hodd` using `FiniteField.odd_card_of_char_ne_two hc`. Establish `hf : (X ^ 2 : k[X]).degree = 2` using `by simp`. Establish `hg : (-(C δ) * X ^ 2 - C u : k[X]).degree = 2`.

Establish `h1 : (-(C δ) * X ^ 2 : k[X]).degree = 2` using `by simp [hδ]`. Rewrite using `[degree_sub_eq_left_of_degree_lt (by rw [h1]; exact degree_C_le.trans_lt (by norm_num)), h1]`. Take `⟨a, b, hab⟩` from `FiniteField.exists_root_sum_quadratic hf hg hodd`. Use `⟨a, b, ?_⟩` and prove the remaining obligations. Simplify using `at hab`.

Take the linear combination `-hab`.
-/
theorem exists_eq_sq_sub_mul_sq_finite {k : Type} [Field k] [Finite k] (h2 : (2 : k) ≠ 0)
    {δ : k} (hδ : δ ≠ 0) (u : k) : ∃ a b : k, u = a ^ 2 - δ * b ^ 2 := by
  classical
  have := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  have hodd := FiniteField.odd_card_of_char_ne_two hc
  have hf : (X ^ 2 : k[X]).degree = 2 := by simp
  have hg : (-(C δ) * X ^ 2 - C u : k[X]).degree = 2 := by
    have h1 : (-(C δ) * X ^ 2 : k[X]).degree = 2 := by simp [hδ]
    rw [degree_sub_eq_left_of_degree_lt (by rw [h1]; exact degree_C_le.trans_lt (by norm_num)), h1]
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination -hab

/- English proof (translation)
Introduce `F _ _ v δ u h2 hδ hu`. Use `set O := v.adicCompletionIntegers F with hO`. Establish `hmem : ∀ x : v.adicCompletion F, x ∈ O ↔ Valued.v x ≤ 1`. Introduce `x`. Rewrite using `[hO]`.

Conclude with `HeightOneSpectrum.mem_adicCompletionIntegers ..`. Establish `hval1 : ∀ z : O, IsUnit z → Valued.v (z : v.adicCompletion F) = 1`. Introduce `z hz`. Take `⟨w, hw⟩` from `hz.exists_right_inv`. Establish `h1 : Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) = 1`.

Rewrite using `[← map_mul, ← Subring.coe_mul, hw]`. Simplify using the standard rewrite rules. Establish `hz1` using `(hmem _).1 z.2`. Establish `hw1` using `(hmem _).1 w.2`. Use `le_antisymm hz1 ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `: Finite (IsLocalRing.ResidueField O)` using `SelfDualGenus.finite_residueField_adicCompletionIntegers v`. Establish `hres_ne : ∀ z : O, Valued.v (z : v.adicCompletion F) = 1 → IsLocalRing.residue O z ≠ 0`. Introduce `z hz`. Rewrite using `[IsLocalRing.residue_ne_zero_iff_isUnit]`.

Establish `hz0 : (z : v.adicCompletion F) ≠ 0`. Introduce `h`. Rewrite `hz` using `[h, map_zero]`. Conclude with `zero_ne_one hz`. Use `IsUnit.of_mul_eq_one (a := z) ⟨(z : v.adicCompletion F)⁻¹, (hmem _).2 (by rw [map_inv₀, hz, inv_one])⟩ ?_` and prove the remaining obligations.

Conclude with `Subtype.ext (by simp [hz0])`. Set `uO : O` to `⟨u, (hmem _).2 hu.le⟩`. Set `δO : O` to `⟨δ, (hmem _).2 hδ.le⟩`. Establish `hc2 : ((2 : O) : v.adicCompletion F) = 2` using `map_ofNat O.subtype 2`. Establish `h2O : IsLocalRing.residue O (2 : O) ≠ 0` using `hres_ne 2 (by rw [hc2]; exact h2)`.

Establish `hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0` using `by rwa [map_ofNat] at h2O`. Take `⟨a, b, hab⟩` from `exists_eq_sq_sub_mul_sq_finite hk2 (hres_ne δO hδ) (IsLocalRing.residue O uO)`. Take `⟨a', rfl⟩` from `IsLocalRing.residue_surjective a`. Take `⟨b', rfl⟩` from `IsLocalRing.residue_surjective b`. Set `N : O` to `a' ^ 2 - δO * b' ^ 2`.

Establish `hresN : IsLocalRing.residue O N = IsLocalRing.residue O uO`. Simplify using `only [N, map_sub, map_mul, map_pow]`. Conclude with `hab.symm`. Establish `hvN : Valued.v (N : v.adicCompletion F) = 1` using `hval1 N ((IsLocalRing.residue_ne_zero_iff_isUnit N).1 (hresN ▸ hres_ne uO hu))`. Establish `hN0 : (N : v.adicCompletion F) ≠ 0`.

Introduce `h`. Rewrite `hvN` using `[h, map_zero]`. Conclude with `zero_ne_one hvN`. Establish `hz1 : Valued.v (u / (N : v.adicCompletion F)) = 1` using `by rw [map_div₀, hu, hvN, div_one]`. Set `z : O` to `⟨u / (N : v.adicCompletion F), (hmem _).2 hz1.le⟩`.

Establish `hzN : z * N = uO` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `u / (N : v.adicCompletion F) * (N : v.adicCompletion F) = u`. Use the proof step `field_simp)`. Establish `hresz : IsLocalRing.residue O z = 1`. Establish `h` using `congrArg (IsLocalRing.residue O) hzN`.

Rewrite `h` using `[map_mul, hresN]`. Establish `hne : IsLocalRing.residue O uO ≠ 0` using `hres_ne uO hu`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ = 1 := by rw [h, div_self hne]`.

Take `⟨s, hs⟩` from `isSquare_of_isSquare_residue_odd F v h2 z hz1 ⟨1, by rw [hresz, mul_one]⟩`. Establish `hvs : Valued.v s ≤ 1`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: Valued.v s ≤ Valued.v s * Valued.v s`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `this` using `[← map_mul, ← hs, hz1]`. Conclude with `absurd (hc.trans_le this) (lt_irrefl _)`. Establish `ha'` using `(hmem _).1 a'.2`. Establish `hb'` using `(hmem _).1 b'.2`.

Use `⟨s * a', (hmem _).2 ?_, s * b', (hmem _).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hvs ha'`. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hvs hb'`.

Establish `hNK : (N : v.adicCompletion F) = (a' : v.adicCompletion F) ^ 2 - δ * (b' : v.adicCompletion F) ^ 2`. Simplify using `[N, δO]`. Establish `hzK : (z : v.adicCompletion F) = u / (N : v.adicCompletion F)` using `rfl`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_integral_sq_sub_mul_sq_of_unit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (δ u : v.adicCompletion F), Valued.v (2 : v.adicCompletion F) = 1 → Valued.v δ = 1 → Valued.v u = 1 → ∃ x ∈ v.adicCompletionIntegers F, ∃ y ∈ v.adicCompletionIntegers F, u = x ^ 2 - δ * y ^ 2 := by
  intro F _ _ v δ u h2 hδ hu
  set O := v.adicCompletionIntegers F with hO
  have hmem : ∀ x : v.adicCompletion F, x ∈ O ↔ Valued.v x ≤ 1 := by
    intro x; rw [hO]; exact HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hval1 : ∀ z : O, IsUnit z → Valued.v (z : v.adicCompletion F) = 1 := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_right_inv
    have h1 : Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hw]
      simp
    have hz1 := (hmem _).1 z.2
    have hw1 := (hmem _).1 w.2
    refine le_antisymm hz1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (z : v.adicCompletion F) * Valued.v (w : v.adicCompletion F) := h1.symm
      _ ≤ Valued.v (z : v.adicCompletion F) * 1 := mul_le_mul_right hw1 _
      _ = _ := mul_one _
  have : Finite (IsLocalRing.ResidueField O) := SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres_ne : ∀ z : O, Valued.v (z : v.adicCompletion F) = 1 → IsLocalRing.residue O z ≠ 0 := by
    intro z hz
    rw [IsLocalRing.residue_ne_zero_iff_isUnit]
    have hz0 : (z : v.adicCompletion F) ≠ 0 := by
      intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    refine IsUnit.of_mul_eq_one (a := z) ⟨(z : v.adicCompletion F)⁻¹, (hmem _).2 (by rw [map_inv₀, hz, inv_one])⟩ ?_
    exact Subtype.ext (by simp [hz0])
  let uO : O := ⟨u, (hmem _).2 hu.le⟩
  let δO : O := ⟨δ, (hmem _).2 hδ.le⟩
  have hc2 : ((2 : O) : v.adicCompletion F) = 2 := map_ofNat O.subtype 2
  have h2O : IsLocalRing.residue O (2 : O) ≠ 0 := hres_ne 2 (by rw [hc2]; exact h2)
  have hk2 : (2 : IsLocalRing.ResidueField O) ≠ 0 := by rwa [map_ofNat] at h2O
  obtain ⟨a, b, hab⟩ := exists_eq_sq_sub_mul_sq_finite hk2 (hres_ne δO hδ) (IsLocalRing.residue O uO)
  obtain ⟨a', rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective b
  let N : O := a' ^ 2 - δO * b' ^ 2
  have hresN : IsLocalRing.residue O N = IsLocalRing.residue O uO := by
    simp only [N, map_sub, map_mul, map_pow]; exact hab.symm
  have hvN : Valued.v (N : v.adicCompletion F) = 1 :=
    hval1 N ((IsLocalRing.residue_ne_zero_iff_isUnit N).1 (hresN ▸ hres_ne uO hu))
  have hN0 : (N : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hvN; exact zero_ne_one hvN
  have hz1 : Valued.v (u / (N : v.adicCompletion F)) = 1 := by rw [map_div₀, hu, hvN, div_one]
  let z : O := ⟨u / (N : v.adicCompletion F), (hmem _).2 hz1.le⟩
  have hzN : z * N = uO := Subtype.ext (by
    change u / (N : v.adicCompletion F) * (N : v.adicCompletion F) = u
    field_simp)
  have hresz : IsLocalRing.residue O z = 1 := by
    have h := congrArg (IsLocalRing.residue O) hzN
    rw [map_mul, hresN] at h
    have hne : IsLocalRing.residue O uO ≠ 0 := hres_ne uO hu
    calc IsLocalRing.residue O z = IsLocalRing.residue O z * IsLocalRing.residue O uO / IsLocalRing.residue O uO := by
          field_simp
      _ = 1 := by rw [h, div_self hne]
  obtain ⟨s, hs⟩ := isSquare_of_isSquare_residue_odd F v h2 z hz1 ⟨1, by rw [hresz, mul_one]⟩
  have hvs : Valued.v s ≤ 1 := by
    by_contra hc
    push Not at hc
    have : Valued.v s ≤ Valued.v s * Valued.v s := by
      calc Valued.v s = Valued.v s * 1 := (mul_one _).symm
        _ ≤ Valued.v s * Valued.v s := mul_le_mul_right hc.le _
    rw [← map_mul, ← hs, hz1] at this
    exact absurd (hc.trans_le this) (lt_irrefl _)
  have ha' := (hmem _).1 a'.2
  have hb' := (hmem _).1 b'.2
  refine ⟨s * a', (hmem _).2 ?_, s * b', (hmem _).2 ?_, ?_⟩
  · rw [map_mul]; exact mul_le_one' hvs ha'
  · rw [map_mul]; exact mul_le_one' hvs hb'
  · have hNK : (N : v.adicCompletion F) = (a' : v.adicCompletion F) ^ 2 - δ * (b' : v.adicCompletion F) ^ 2 := by
      simp [N, δO]
    have hzK : (z : v.adicCompletion F) = u / (N : v.adicCompletion F) := rfl
    calc u = (z : v.adicCompletion F) * (N : v.adicCompletion F) := by rw [hzK]; field_simp
      _ = _ := by rw [hs, hNK]; ring

end GlobalTheory.QNorm
