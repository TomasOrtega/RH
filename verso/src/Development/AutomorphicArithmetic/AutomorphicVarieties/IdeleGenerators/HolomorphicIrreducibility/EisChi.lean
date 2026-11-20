import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.TsumNormEisensteinTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisCoef

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

/- English proof (translation)
Establish `h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1))` using `by conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b, gaussSum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : ℂ)`. Rewrite using `[h1, Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]`.

Rewrite using `[Finset.sum_eq_single (1 : ZMod N)]`. Simplify using the standard rewrite rules. Introduce `a _ ha`. Simplify using `[ha]`. Simplify using the standard rewrite rules.

Introduce `h0`. Rewrite `h2` using `[h0, zero_mul]`. Conclude with `(Nat.cast_ne_zero.2 (NeZero.ne N)) h2.symm`.
-/
private theorem eisChi_gauss_ne {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {ψ : AddChar (ZMod N) ℂ} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ ≠ 0 := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have h2 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : ℂ) := by
    rw [h1, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
    rw [Finset.sum_eq_single (1 : ZMod N)]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  intro h0
  rw [h0, zero_mul] at h2
  exact (Nat.cast_ne_zero.2 (NeZero.ne N)) h2.symm

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Both sides reduce to the same expression.
-/
private theorem eisChi_coe_sum {N : ℕ} {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ModularForm (Gamma1 N) k) :
    ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = ∑ a ∈ s, c a • (F a : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/- English proof (translation)
Establish `hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods`. Simplify using the standard rewrite rules. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [coef, qExpansion_zero]`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih]`. Unfold `coef`. Establish `h1` using `ModularForm.qExpansion_add one_pos hp (c a • F a) (∑ a ∈ s, c a • F a)`. Establish `h2` using `ModularForm.qExpansion_smul one_pos hp (c a) (F a)`. Establish `h3 : ((c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = c a • (F a : ℍ → ℂ)` using `rfl`.

Rewrite `h1` using `[h3, h2]`. Establish `h4 : ((c a • F a + ∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = c a • (F a : ℍ → ℂ) + ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ)` using `rfl`. Rewrite using `[h4, h1]`. Simplify using the standard rewrite rules.
-/
private theorem eisChi_coef_sum {N : ℕ} [NeZero N] {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ModularForm (Gamma1 N) k) (n : ℕ) :
    coef ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) n = ∑ a ∈ s, c a * coef (F a) n := by
  classical
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  induction s using Finset.induction_on with
  | empty => simp [coef, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold coef
    have h1 := ModularForm.qExpansion_add one_pos hp (c a • F a) (∑ a ∈ s, c a • F a)
    have h2 := ModularForm.qExpansion_smul one_pos hp (c a) (F a)
    have h3 : ((c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = c a • (F a : ℍ → ℂ) := rfl
    rw [h3, h2] at h1
    have h4 : ((c a • F a + ∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) =
      c a • (F a : ℍ → ℂ) + ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) := rfl
    rw [h4, h1]
    simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, ← ih, SlashAction.add_slash, ModularForm.SL_smul_slash]`.
-/
private theorem eisChi_slash_sum {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ a ∈ s, c a • F a) ∣[k] γ = ∑ a ∈ s, c a • (F a ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, SlashAction.add_slash, ModularForm.SL_smul_slash]

/- English proof (translation)
Establish `hi : (χ⁻¹).IsPrimitive`. Rewrite using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]`. Conclude with `hχ`. Use `gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := N)) hi e` as an intermediate fact. Rewrite `this` using `[inv_inv]`.

Rewrite using `[← this, gaussSum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[AddChar.mulShift_apply, mul_comm e a]`.
-/
private theorem eisChi_gs {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (e : ZMod N) :
    ∑ a : ZMod N, χ⁻¹ a * (ZMod.stdAddChar (a * e) : ℂ) = χ e * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := N)) hi e
  rw [inv_inv] at this
  rw [← this, gaussSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [AddChar.mulShift_apply, mul_comm e a]

/- English proof (translation)
Introduce `N k _ hN hk χ hχ hpar`. Use `choose F hF using UpperTheory.V.Sd.eisMF N k hk`. Establish `hi : (χ⁻¹).IsPrimitive`. Rewrite using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]`. Conclude with `hχ`.

Establish `hg : gaussSum χ⁻¹ (ZMod.stdAddChar (N` using `N)) ≠ 0 := eisChi_gauss_ne hi (ZMod.isPrimitive_stdAddChar N)`. Use `set g := gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) with hgdef`. Use `haveI : Fact (1 < N) := ⟨hN⟩`. Establish `h0 : χ⁻¹ (0 : ZMod N) = 0` using `MulChar.map_nonunit _ not_isUnit_zero`. Use `⟨∑ a : ZMod N, ((2 * g)⁻¹ * χ⁻¹ a) • F a, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ hγ`. Rewrite using `[eisChi_coe_sum, eisChi_slash_sum, Finset.smul_sum]`. Simplify using `only [hF, UpperTheory.V.Sd.eisSlash N k hk _ γ hγ]`. Establish `hd : IsUnit (((γ 1 1 : ℤ)) : ZMod N)`. Establish `h1` using `γ.det_coe`.

Rewrite `h1` using `[Matrix.det_fin_two]`. Establish `h2 : ((γ 1 0 : ℤ) : ZMod N) = 0` using `Gamma0_mem.1 hγ`. Establish `h3` using `congrArg (Int.cast : ℤ → ZMod N) h1`. Move the coercions through the operations in `at h3`. Rewrite `h3` using `[h2, mul_zero, sub_zero]`.

Conclude with `IsUnit.of_mul_eq_one_right _ h3`. Take `⟨u, hu⟩` from `hd`. Rewrite using `[← hu]`. Use `Fintype.sum_equiv (Units.mulRight u) _ _ fun a => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`.

Use `congr 1`. Establish `: χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1`. Rewrite using `[← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]`. Simplify using `only [Units.mulRight_apply, map_mul]`. Take the linear combination `(-((2 * g)⁻¹ * χ⁻¹ a)) * this`.

Introduce `γ hγ`. Rewrite using `[eisChi_coe_sum, eisChi_slash_sum]`. Use `Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : IsUnit a`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Rewrite using `[hF]`. Conclude with `UpperTheory.V.Sd.eisVan N k hk a ha hN γ hγ`. Rewrite using `[MulChar.map_nonunit _ ha, mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`. Introduce `n hn`.

Rewrite using `[eisChi_coef_sum]`. Establish `h1 : ∀ a : ZMod N, (2 * g)⁻¹ * χ⁻¹ a * coef (F a) n = ∑ e ∈ n.divisors, (2 * g)⁻¹ * (e : ℂ) ^ (k - 1) * (χ⁻¹ a * (ZMod.stdAddChar (a * (e : ZMod N)) : ℂ) + (-1) ^ k * (χ⁻¹ a * (ZMod.stdAddChar (a * (-(e : ZMod N))) : ℂ)))`. Introduce `a`. Distinguish the cases in `ha : a = 0`. Simplify using `[ha, h0]`.

Rewrite using `[hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).2 n hn, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[mul_neg]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h1]`.

Rewrite using `[Finset.sum_comm, sigChi]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, eisChi_gs hχ, eisChi_gs hχ, ← hgdef, ← neg_one_mul (e : ZMod N), map_mul, hpar]`. Establish `h2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; simp`. Establish `h3 : (2 * g)⁻¹ * (2 * g) = 1` using `inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)`.

Take the linear combination `((2 * g)⁻¹ * (e : ℂ) ^ (k - 1) * χ (e : ZMod N) * g) * h2 + ((e : ℂ) ^ (k - 1) * χ (e : ZMod N)) * h3`. Rewrite using `[eisChi_coef_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Simplify using `[ha, h0]`.

Rewrite using `[hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).1]`. Establish `h3 : (2 * g)⁻¹ * (2 * g) = 1` using `inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)`. Take the linear combination `(χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ)) * h3`.
-/
theorem UpperTheory.V.Sd.eisChi :
    UpperTheory.V.Sd.EisChi := by
  intro N k _ hN hk χ hχ hpar
  choose F hF using UpperTheory.V.Sd.eisMF N k hk
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hg : gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) ≠ 0 :=
    eisChi_gauss_ne hi (ZMod.isPrimitive_stdAddChar N)
  set g := gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) with hgdef
  haveI : Fact (1 < N) := ⟨hN⟩
  have h0 : χ⁻¹ (0 : ZMod N) = 0 := MulChar.map_nonunit _ not_isUnit_zero
  refine ⟨∑ a : ZMod N, ((2 * g)⁻¹ * χ⁻¹ a) • F a, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum, Finset.smul_sum]
    simp only [hF, UpperTheory.V.Sd.eisSlash N k hk _ γ hγ]
    have hd : IsUnit (((γ 1 1 : ℤ)) : ZMod N) := by
      have h1 := γ.det_coe
      rw [Matrix.det_fin_two] at h1
      have h2 : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hγ
      have h3 := congrArg (Int.cast : ℤ → ZMod N) h1
      push_cast at h3
      rw [h2, mul_zero, sub_zero] at h3
      exact IsUnit.of_mul_eq_one_right _ h3
    obtain ⟨u, hu⟩ := hd
    rw [← hu]
    refine Fintype.sum_equiv (Units.mulRight u) _ _ fun a => ?_
    rw [smul_smul]
    congr 1
    have : χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    simp only [Units.mulRight_apply, map_mul]
    linear_combination (-((2 * g)⁻¹ * χ⁻¹ a)) * this
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum]
    refine Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun a _ => ?_
    by_cases ha : IsUnit a
    · refine Submodule.smul_mem _ _ ?_
      rw [hF]
      exact UpperTheory.V.Sd.eisVan N k hk a ha hN γ hγ
    · rw [MulChar.map_nonunit _ ha, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · intro n hn
    rw [eisChi_coef_sum]
    have h1 : ∀ a : ZMod N, (2 * g)⁻¹ * χ⁻¹ a * coef (F a) n = ∑ e ∈ n.divisors, (2 * g)⁻¹ * (e : ℂ) ^ (k - 1) *
        (χ⁻¹ a * (ZMod.stdAddChar (a * (e : ZMod N)) : ℂ) +
          (-1) ^ k * (χ⁻¹ a * (ZMod.stdAddChar (a * (-(e : ZMod N))) : ℂ))) := by
      intro a
      by_cases ha : a = 0
      · simp [ha, h0]
      · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).2 n hn, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_neg]; ring
    simp only [h1]
    rw [Finset.sum_comm, sigChi]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, eisChi_gs hχ, eisChi_gs hχ, ← hgdef,
      ← neg_one_mul (e : ZMod N), map_mul, hpar]
    have h2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
    linear_combination ((2 * g)⁻¹ * (e : ℂ) ^ (k - 1) * χ (e : ZMod N) * g) * h2 + ((e : ℂ) ^ (k - 1) * χ (e : ZMod N)) * h3
  · rw [eisChi_coef_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · simp [ha, h0]
    · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).1]
      have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
      linear_combination (χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ)) * h3
