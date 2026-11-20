import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action

open scoped MatrixGroups UpperHalfPlane
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.SiegSep

open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.SiegQ

/- English proof (translation)
Establish `hc : 0 < c` using `by have := hadm.1; omega`. Establish `hM0 : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Use `set ζ : ℂ := ee (1 / (M : ℂ)) with hζ`. Establish `hprim : IsPrimitiveRoot ζ M`. Use `Complex.isPrimitiveRoot_exp M hM.ne'` as an intermediate fact.

Rewrite using `[hζ, ee, mul_one_div]` and apply the resulting hypothesis. Establish `hζ0 : ζ ≠ 0` using `Complex.exp_ne_zero _`. Establish `hv : ‖ζ ^ b‖ = 1` using `by rw [norm_pow, hprim.norm'_eq_one hM.ne', one_pow]`. Establish `hne : M ∣ c * a → (ζ ^ b) ^ c ≠ 1`. Introduce and unpack `⟨k, hk⟩ h`.

Rewrite `h` using `[← pow_mul, hprim.pow_eq_one_iff_dvd]`. Take `⟨l, hl⟩` from `h`. Use `hadm.2.2 ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩` and prove the remaining obligations. Establish `: (c : ℚ) * a = M * k` using `by exact_mod_cast hk`. Simplify using `only [Matrix.cons_val_zero, Int.cast_natCast]`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-this`. Establish `: (b : ℚ) * c = M * l` using `by exact_mod_cast hl`. Simplify using `only [Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_natCast]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-this`. Establish `hK : Good (IntermediateField.adjoin ℚ {ζ}).toSubfield.toSubring (unitPart c M a (ζ ^ b))` using `by set K := IntermediateField.adjoin ℚ {ζ}`. Establish `m1 : ζ ^ b ∈ K` using `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) b`. Establish `m2 : (1 - (ζ ^ b) ^ c)⁻¹ ∈ K` using `inv_mem (sub_mem (one_mem K) (pow_mem m1 c))`. Conclude with `good_unitPart hc hM ha hv m1 (inv_mem m1 : _ ∈ K) (fun _ => (mul_mem (pow_mem (sub_mem (one_mem K) m1) _) m2 : _ ∈ K)) fun _ h => ⟨hne h, m2⟩`.

Use `⟨tc (unitPart c M a (ζ ^ b)), ?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun τ : ℍ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((expo c M a : ℂ) / M) * (τ : ℂ))) = fun τ => unitPart c M a (ζ ^ b) (qv M τ)`. Use function extensionality and compare the values at `τ`. Establish `hz0 : qv M τ ≠ 0` using `Complex.exp_ne_zero _`. Establish `e1 : ee τ = qv M τ ^ M`.

Rewrite using `[ee, qv, ← Complex.exp_nat_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `e2 : ee (pt ![(a : ℚ) / M, (b : ℚ) / M] τ) = qv M τ ^ a * ζ ^ b`. Rewrite using `[hζ, ee, ee, qv, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]`.

Use `congr 1`. Simplify using `only [pt, Matrix.cons_val_one, Matrix.cons_val_zero]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : ee (-((expo c M a : ℂ) / M) * (τ : ℂ)) = qv M τ ^ (-expo c M a)`.

Rewrite using `[ee, qv, ← Complex.exp_int_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sg, e1, e2, e3, cth_eq hM ha hv (norm_qv_lt hM τ) hz0, zpow_neg]`.

Use `zpow_ne_zero (expo c M a) hz0` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `hasQ_tc hK.1 hM`. Rewrite using `[tc_zero]`.

Conclude with `unitPart_zero_ne hc hM ha (pow_ne_zero _ hζ0) hne`.
-/
theorem hasQ_expo (c M a b : ℕ) (hM : 0 < M) (ha : a < M) (hadm : admitted c ![(a : ℚ) / M, (b : ℚ) / M]) :
    ∃ A : ℕ → ℂ, HasQ M (fun τ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ * ee (-((expo c M a : ℂ) / M) * (τ : ℂ))) A ∧
      A 0 ≠ 0 := by
  have hc : 0 < c := by have := hadm.1; omega
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  set ζ : ℂ := ee (1 / (M : ℂ)) with hζ
  have hprim : IsPrimitiveRoot ζ M := by
    have := Complex.isPrimitiveRoot_exp M hM.ne'
    rwa [hζ, ee, mul_one_div]
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hv : ‖ζ ^ b‖ = 1 := by rw [norm_pow, hprim.norm'_eq_one hM.ne', one_pow]
  have hne : M ∣ c * a → (ζ ^ b) ^ c ≠ 1 := by
    rintro ⟨k, hk⟩ h
    rw [← pow_mul, hprim.pow_eq_one_iff_dvd] at h
    obtain ⟨l, hl⟩ := h
    refine hadm.2.2 ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
    · have : (c : ℚ) * a = M * k := by exact_mod_cast hk
      simp only [Matrix.cons_val_zero, Int.cast_natCast]
      field_simp
      linear_combination -this
    · have : (b : ℚ) * c = M * l := by exact_mod_cast hl
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_natCast]
      field_simp
      linear_combination -this
  have hK : Good (IntermediateField.adjoin ℚ {ζ}).toSubfield.toSubring (unitPart c M a (ζ ^ b)) := by
    set K := IntermediateField.adjoin ℚ {ζ}
    have m1 : ζ ^ b ∈ K := pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) b
    have m2 : (1 - (ζ ^ b) ^ c)⁻¹ ∈ K := inv_mem (sub_mem (one_mem K) (pow_mem m1 c))
    exact good_unitPart hc hM ha hv m1 (inv_mem m1 : _ ∈ K)
      (fun _ => (mul_mem (pow_mem (sub_mem (one_mem K) m1) _) m2 : _ ∈ K)) fun _ h => ⟨hne h, m2⟩
  refine ⟨tc (unitPart c M a (ζ ^ b)), ?_, ?_⟩
  · have e : (fun τ : ℍ => sg c ![(a : ℚ) / M, (b : ℚ) / M] τ *
        ee (-((expo c M a : ℂ) / M) * (τ : ℂ))) = fun τ => unitPart c M a (ζ ^ b) (qv M τ) := by
      funext τ
      have hz0 : qv M τ ≠ 0 := Complex.exp_ne_zero _
      have e1 : ee τ = qv M τ ^ M := by
        rw [ee, qv, ← Complex.exp_nat_mul]; congr 1; field_simp
      have e2 : ee (pt ![(a : ℚ) / M, (b : ℚ) / M] τ) = qv M τ ^ a * ζ ^ b := by
        rw [hζ, ee, ee, qv, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        simp only [pt, Matrix.cons_val_one, Matrix.cons_val_zero]
        push_cast
        ring
      have e3 : ee (-((expo c M a : ℂ) / M) * (τ : ℂ)) = qv M τ ^ (-expo c M a) := by
        rw [ee, qv, ← Complex.exp_int_mul]
        congr 1
        push_cast
        ring
      rw [sg, e1, e2, e3, cth_eq hM ha hv (norm_qv_lt hM τ) hz0, zpow_neg]
      have := zpow_ne_zero (expo c M a) hz0
      field_simp
    rw [e]
    exact hasQ_tc hK.1 hM
  · rw [tc_zero]
    exact unitPart_zero_ne hc hM ha (pow_ne_zero _ hζ0) hne

/- English proof (translation)
Rewrite using `[ee, ee, ee, ← Complex.exp_add]`. Put the polynomial expressions in normal form.
-/
theorem ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  rw [ee, ee, ee, ← Complex.exp_add]; ring_nf

/- English proof (translation)
Introduce `τ`. Establish `h1` using `(h τ).mul_right (ee (((d : ℂ) / M) * (τ : ℂ)))`. Establish `e : ∀ n : ℕ, α n * Complex.exp (2 * Real.pi * Complex.I * n * τ / M) * ee (((d : ℂ) / M) * (τ : ℂ)) = α n * Complex.exp (2 * Real.pi * Complex.I * ((n + d : ℕ) : ℂ) * τ / M)` using `fun n => by`. Rewrite using `[mul_assoc, ee, ← Complex.exp_add]`. Use `push_cast`.

Put the polynomial expressions in normal form. Simplify using `only [e] at h1`. Establish `h2` using `(hasSum_extend_zero (f := fun n : ℕ => α n * Complex.exp (2 * Real.pi * Complex.I * ((n + d : ℕ) : ℂ) * τ / M)) (g := fun n : ℕ => n + d) (add_left_injective d)).mpr h1`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`.

Distinguish the cases in `hn : d ≤ n`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hn dsimp only`. Rewrite using `[if_pos hn, show d + m = m + d by ring, (add_left_injective d).extend_apply]`. Simplify using the standard rewrite rules. Simplify using `only`.

Rewrite using `[if_neg hn, zero_mul, Function.extend_apply']`. Both sides reduce to the same expression. Introduce and unpack `⟨m, rfl⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem hasQ_shift {M : ℕ} {f : ℍ → ℂ} {α : ℕ → ℂ} (h : HasQ M f α) (d : ℕ) :
    HasQ M (fun τ => f τ * ee (((d : ℂ) / M) * (τ : ℂ))) (fun n => if d ≤ n then α (n - d) else 0) := by
  intro τ
  have h1 := (h τ).mul_right (ee (((d : ℂ) / M) * (τ : ℂ)))
  have e : ∀ n : ℕ, α n * Complex.exp (2 * Real.pi * Complex.I * n * τ / M) * ee (((d : ℂ) / M) * (τ : ℂ)) =
      α n * Complex.exp (2 * Real.pi * Complex.I * ((n + d : ℕ) : ℂ) * τ / M) := fun n => by
    rw [mul_assoc, ee, ← Complex.exp_add]; push_cast; ring_nf
  simp only [e] at h1
  have h2 := (hasSum_extend_zero (f := fun n : ℕ => α n * Complex.exp (2 * Real.pi * Complex.I * ((n + d : ℕ) : ℂ) * τ / M))
    (g := fun n : ℕ => n + d) (add_left_injective d)).mpr h1
  convert h2 using 1
  funext n
  by_cases hn : d ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    dsimp only
    rw [if_pos hn, show d + m = m + d by ring, (add_left_injective d).extend_apply]
    simp
  · dsimp only
    rw [if_neg hn, zero_mul, Function.extend_apply']
    · rfl
    · rintro ⟨m, rfl⟩; omega

/- English proof (translation)
Take `⟨k, A, hA, hco, hz⟩` from `GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha hadm`. Take `⟨B, hB, hB0⟩` from `hasQ_expo c M a b hM ha hadm`. Use `set e := expo c M a with he`. Use `set f := sg c ![(a : ℚ) / M, (b : ℚ) / M] with hf`. Establish `shift : ∀ (u v : ℤ) (d : ℕ), (d : ℤ) = u - v → (fun τ : ℍ => f τ * ee (-((u : ℂ) / M) * (τ : ℂ)) * ee (((d : ℂ) / M) * (τ : ℂ))) = fun τ => f τ * ee (-((v : ℂ) / M) * (τ : ℂ))`.

Introduce `u v d hd`. Use function extensionality and compare the values at `τ`. Rewrite using `[mul_assoc, ← ee_add]`. Use `congr 2`. Establish `hd' : (d : ℂ) = (u : ℂ) - v` using `by exact_mod_cast hd`.

Rewrite using `[hd']`. Expand and normalize the polynomial expressions, which then agree. Establish `hke : k ≤ e`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Establish `hd : (((k - e).toNat : ℕ) : ℤ) = k - e` using `Int.toNat_of_nonneg (by omega)`. Establish `h1` using `hasQ_shift hA (k - e).toNat`. Rewrite `h1` using `[shift k e _ hd]`. Establish `h2` using `HasQ.coeff_unique hM hB h1`. Establish `h3` using `congrFun h2 0`.

Rewrite `h3` using `[if_neg (by omega)]`. Conclude with `hB0 h3`. Establish `hd : (((e - k).toNat : ℕ) : ℤ) = e - k` using `Int.toNat_of_nonneg (by omega)`. Use `set d := (e - k).toNat with hdd`. Establish `h1` using `hasQ_shift hB d`.

Rewrite `h1` using `[shift e k _ hd]`. Establish `h2` using `HasQ.coeff_unique hM hA h1`. Establish `hAd : A d ≠ 0`. Introduce `h0`. Establish `h3` using `congrFun h2 d`.

Simplify using `only [le_refl, if_true, Nat.sub_self, h0, map_zero] at h3`. Conclude with `hB0 h3.symm`. Establish `hAn : ∀ n, n < d → A n = 0`. Introduce `n hn`. Establish `h3` using `congrFun h2 n`.

Simplify using `only [if_neg (show ¬ d ≤ n by omega)] at h3`. Conclude with `(map_eq_zero ε).1 h3`. Establish `hMq : (0 : ℚ) < M` using `by exact_mod_cast hM`. Establish `hed : (e : ℚ) = (k : ℚ) + d`. Establish `: (e : ℤ) = k + (d : ℤ)` using `by omega`.

Conclude with `this` after adjusting the coercions. Use `⟨?_, fun r hr => ?_⟩` and prove the remaining obligations. Rewrite using `[hed, hco d]`. Conclude with `hAd`. Assume the negation of the conclusion as `hlt push_neg at hlt`.

Distinguish the cases in `hex : ∃ n : ℕ, r = ((k : ℚ) + n) / M`. Take `⟨n, rfl⟩` from `hex`. Rewrite `hr` using `[hco n]`. Establish `hnd : d ≤ n`. Assume the negation of the conclusion as `hnd; exact hr (hAn n (by omega))`.

Rewrite `hlt` using `[hed]`. Establish `: ((k : ℚ) + n) < (k : ℚ) + d` using `(div_lt_div_iff_of_pos_right hMq).1 hlt`. Establish `: (n : ℚ) < d` using `by linarith`. Conclude with `absurd (by exact_mod_cast this : n < d) (by omega)`. Use `push_neg at hex`.

Conclude with `hr (hz r hex)`.
-/
theorem exp_siegel_ord {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c M a b : ℕ) (hM : 0 < M) (ha : a < M) (hadm : admitted c ![(a : ℚ) / M, (b : ℚ) / M]) :
    (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff ((expo c M a : ℚ) / M) ≠ 0 ∧
    ∀ r : ℚ, (T.exp (siegel T c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r ≠ 0 → (expo c M a : ℚ) / M ≤ r := by
  obtain ⟨k, A, hA, hco, hz⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha hadm
  obtain ⟨B, hB, hB0⟩ := hasQ_expo c M a b hM ha hadm
  set e := expo c M a with he
  set f := sg c ![(a : ℚ) / M, (b : ℚ) / M] with hf
  have shift : ∀ (u v : ℤ) (d : ℕ), (d : ℤ) = u - v →
      (fun τ : ℍ => f τ * ee (-((u : ℂ) / M) * (τ : ℂ)) * ee (((d : ℂ) / M) * (τ : ℂ))) =
        fun τ => f τ * ee (-((v : ℂ) / M) * (τ : ℂ)) := by
    intro u v d hd
    funext τ
    rw [mul_assoc, ← ee_add]
    congr 2
    have hd' : (d : ℂ) = (u : ℂ) - v := by exact_mod_cast hd
    rw [hd']; ring
  have hke : k ≤ e := by
    by_contra hlt
    push_neg at hlt
    have hd : (((k - e).toNat : ℕ) : ℤ) = k - e := Int.toNat_of_nonneg (by omega)
    have h1 := hasQ_shift hA (k - e).toNat
    rw [shift k e _ hd] at h1
    have h2 := HasQ.coeff_unique hM hB h1
    have h3 := congrFun h2 0
    rw [if_neg (by omega)] at h3
    exact hB0 h3
  have hd : (((e - k).toNat : ℕ) : ℤ) = e - k := Int.toNat_of_nonneg (by omega)
  set d := (e - k).toNat with hdd
  have h1 := hasQ_shift hB d
  rw [shift e k _ hd] at h1
  have h2 := HasQ.coeff_unique hM hA h1
  have hAd : A d ≠ 0 := by
    intro h0
    have h3 := congrFun h2 d
    simp only [le_refl, if_true, Nat.sub_self, h0, map_zero] at h3
    exact hB0 h3.symm
  have hAn : ∀ n, n < d → A n = 0 := by
    intro n hn
    have h3 := congrFun h2 n
    simp only [if_neg (show ¬ d ≤ n by omega)] at h3
    exact (map_eq_zero ε).1 h3
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hed : (e : ℚ) = (k : ℚ) + d := by
    have : (e : ℤ) = k + (d : ℤ) := by omega
    exact_mod_cast this
  refine ⟨?_, fun r hr => ?_⟩
  · rw [hed, hco d]; exact hAd
  · by_contra hlt
    push_neg at hlt
    by_cases hex : ∃ n : ℕ, r = ((k : ℚ) + n) / M
    · obtain ⟨n, rfl⟩ := hex
      rw [hco n] at hr
      have hnd : d ≤ n := by
        by_contra hnd; exact hr (hAn n (by omega))
      rw [hed] at hlt
      have : ((k : ℚ) + n) < (k : ℚ) + d := (div_lt_div_iff_of_pos_right hMq).1 hlt
      have : (n : ℚ) < d := by linarith
      exact absurd (by exact_mod_cast this : n < d) (by omega)
    · push_neg at hex
      exact hr (hz r hex)

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `h`. Rewrite using `[Finset.sum_range_succ, Nat.cast_add, mul_add, ih (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ n)) h), Nat.cast_sub h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_sub (M K : ℕ) : ∀ n : ℕ, n * M ≤ K →
    2 * ((∑ m ∈ Finset.range n, (K - (m + 1) * M) : ℕ) : ℤ) = 2 * n * K - M * n * (n + 1) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ n)) h),
      Nat.cast_sub h]
    push_cast; ring

/- English proof (translation)
Establish `hdiv : (1 + t * M) * a / M = t * a`. Rewrite using `[show (1 + t * M) * a = a + M * (t * a) by ring, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha, zero_add]`. Establish `hkk : 2 * kk (1 + t * M) = ((1 + t * M : ℕ) : ℤ) - ((1 + t * M : ℕ) : ℤ) ^ 2`. Unfold `kk`. Apply `Int.mul_ediv_cancel'` to reduce the goal to its premises.

Establish `: ((1 + t * M : ℕ) : ℤ) - ((1 + t * M : ℕ) : ℤ) ^ 2 = -((((1 + t * M : ℕ) : ℤ) - 1) * ((((1 + t * M : ℕ) : ℤ) - 1) + 1))` using `by ring`. Rewrite using `[this]`. Conclude with `(Int.even_mul_succ_self _).neg.two_dvd`. Establish `hS` using `sum_sub M ((1 + t * M) * a) (t * a) (by rw [show (1 + t * M) * a = a + M * (t * a) by ring]; nlinarith)`. Unfold `expo`.

Rewrite using `[hdiv]`. Move the coercions through the operations in `at hS hkk ⊢`. Take the linear combination `(a : ℤ) * hkk + hS`.
-/
theorem expo_two (t M a : ℕ) (hM : 0 < M) (ha : a < M) :
    2 * expo (1 + t * M) M a =
      2 * ((M * (((1 + t * M) ^ 2 - 1) / 12) : ℕ) : ℤ) + t * (2 + t * M) * (a * a - M * a) := by
  have hdiv : (1 + t * M) * a / M = t * a := by
    rw [show (1 + t * M) * a = a + M * (t * a) by ring, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha, zero_add]
  have hkk : 2 * kk (1 + t * M) = ((1 + t * M : ℕ) : ℤ) - ((1 + t * M : ℕ) : ℤ) ^ 2 := by
    unfold kk
    apply Int.mul_ediv_cancel'
    have : ((1 + t * M : ℕ) : ℤ) - ((1 + t * M : ℕ) : ℤ) ^ 2 =
        -((((1 + t * M : ℕ) : ℤ) - 1) * ((((1 + t * M : ℕ) : ℤ) - 1) + 1)) := by ring
    rw [this]
    exact (Int.even_mul_succ_self _).neg.two_dvd
  have hS := sum_sub M ((1 + t * M) * a) (t * a)
    (by rw [show (1 + t * M) * a = a + M * (t * a) by ring]; nlinarith)
  unfold expo
  rw [hdiv]
  push_cast at hS hkk ⊢
  linear_combination (a : ℤ) * hkk + hS

/- English proof (translation)
Establish `hM : 0 < M` using `by omega`. Take `⟨t, ht⟩ : M ∣ c - 1` from `(Nat.modEq_iff_dvd' (by omega)).1 hcM.symm`. Establish `hc' : c = 1 + t * M`. Use `Nat.eq_add_of_sub_eq (by omega) ht` as an intermediate fact. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Substitute `hc'` using the available equality. Establish `e1` using `expo_two t M a hM ha`. Establish `e2` using `expo_two t M a' hM ha'`. Rewrite `e1` using `[h]`.

Establish `key : (t : ℤ) * (2 + t * M) * ((a : ℤ) * a - M * a) = t * (2 + t * M) * ((a' : ℤ) * a' - M * a')`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `tpos : 0 < t`. Break down `Nat.eq_zero_or_pos t with h0 | h0` into its components or cases. Substitute `h0` using the available equality.

Simplify using `at hc`. Conclude with `h0`. Establish `hne : (t : ℤ) * (2 + t * M) ≠ 0` using `by positivity`. Establish `h2` using `mul_left_cancel₀ hne key`. Establish `h3 : ((a : ℤ) - a') * (a + a' - M) = 0` using `by linear_combination h2`.

Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Use `left`. Use linear arithmetic over natural numbers and integers. Use `right`. Use linear arithmetic over natural numbers and integers.
-/
theorem expo_inj (c M a a' : ℕ) (hc : 1 < c) (hcM : c ≡ 1 [MOD M]) (ha : a < M) (ha' : a' < M)
    (h : expo c M a = expo c M a') : a = a' ∨ a + a' = M := by
  have hM : 0 < M := by omega
  obtain ⟨t, ht⟩ : M ∣ c - 1 := (Nat.modEq_iff_dvd' (by omega)).1 hcM.symm
  have hc' : c = 1 + t * M := by
    have := Nat.eq_add_of_sub_eq (by omega) ht
    rw [this]; ring
  subst hc'
  have e1 := expo_two t M a hM ha
  have e2 := expo_two t M a' hM ha'
  rw [h] at e1
  have key : (t : ℤ) * (2 + t * M) * ((a : ℤ) * a - M * a) = t * (2 + t * M) * ((a' : ℤ) * a' - M * a') := by
    linarith
  have tpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · subst h0; simp at hc
    · exact h0
  have hne : (t : ℤ) * (2 + t * M) ≠ 0 := by positivity
  have h2 := mul_left_cancel₀ hne key
  have h3 : ((a : ℤ) - a') * (a + a' - M) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

/- English proof (translation)
Use `⟨hc, h6, ?_⟩` and prove the remaining obligations. Establish `hcop : Nat.Coprime M c`. Use `Nat.ModEq.gcd_eq hcM` as an intermediate fact. Rewrite `this` using `[Nat.gcd_one_left]`. Conclude with `Nat.Coprime.symm this`.

Establish `hMc : IsCoprime (M : ℤ) (c : ℤ)` using `Nat.isCoprime_iff_coprime.mpr hcop`. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / M) ∈ Set.range ((↑) : ℤ → ℚ) → (M : ℤ) ∣ z`. Introduce and unpack `z ⟨k, hk⟩`. Establish `e : (k : ℚ) * M = c * z` using `by rw [hk]; field_simp`.

Establish `e' : k * (M : ℤ) = c * z` using `by exact_mod_cast e`. Conclude with `hMc.dvd_of_dvd_mul_left ⟨k, by rw [← e']; ring⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hab ⟨key a (by simpa using h1), key b (by simpa using h2)⟩`.
-/
theorem isAdmissibleSmoothingFactor_of_int_index {c M : ℕ} (hM : 0 < M) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b : ℤ}
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) : admitted c ![(a : ℚ) / M, (b : ℚ) / M] := by
  refine ⟨hc, h6, ?_⟩
  have hcop : Nat.Coprime M c := by
    have := Nat.ModEq.gcd_eq hcM
    rw [Nat.gcd_one_left] at this
    exact Nat.Coprime.symm this
  have hMc : IsCoprime (M : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / M) ∈ Set.range ((↑) : ℤ → ℚ) → (M : ℤ) ∣ z := by
    rintro z ⟨k, hk⟩
    have e : (k : ℚ) * M = c * z := by rw [hk]; field_simp
    have e' : k * (M : ℤ) = c * z := by exact_mod_cast e
    exact hMc.dvd_of_dvd_mul_left ⟨k, by rw [← e']; ring⟩
  rintro ⟨h1, h2⟩
  exact hab ⟨key a (by simpa using h1), key b (by simpa using h2)⟩

/- English proof (translation)
Establish `e : sgC c (fun i => x i + n i) = sgC c x` using `funext fun z => GlobalTheory.Sieg.Per.sg_add_int c x n _ hx`. Unfold `siegel`. Rewrite using `[e]`.
-/
theorem siegel_add_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c : ℕ} {x : Fin 2 → ℚ}
    (hx : admitted c x) (n : Fin 2 → ℤ) : siegel T c (fun i => x i + n i) = siegel T c x := by
  have e : sgC c (fun i => x i + n i) = sgC c x := funext fun z => GlobalTheory.Sieg.Per.sg_add_int c x n _ hx
  unfold siegel
  rw [e]

/- English proof (translation)
Establish `hM0 : (M : ℤ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hMpos : (0 : ℤ) < M` using `by exact_mod_cast hM`. Establish `ta : (((a % M).toNat : ℕ) : ℤ) = a % M` using `Int.toNat_of_nonneg (Int.emod_nonneg a hM0)`. Establish `tb : (((b % M).toNat : ℕ) : ℤ) = b % M` using `Int.toNat_of_nonneg (Int.emod_nonneg b hM0)`. Use `⟨ta, tb, ?_, ?_⟩` and prove the remaining obligations.

Use `Int.emod_lt_of_pos a hMpos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[ta, tb]`. Introduce and unpack `⟨h1, h2⟩`. Apply `hab` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← Int.emod_add_mul_ediv a M]`. Conclude with `dvd_add h1 (dvd_mul_right _ _)`. Rewrite using `[← Int.emod_add_mul_ediv b M]`. Conclude with `dvd_add h2 (dvd_mul_right _ _)`.
-/
theorem norm_facts {M : ℕ} (hM : 0 < M) {a b : ℤ} (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) :
    (((a % M).toNat : ℕ) : ℤ) = a % M ∧ (((b % M).toNat : ℕ) : ℤ) = b % M ∧ (a % M).toNat < M ∧
    ¬ ((M : ℤ) ∣ (((a % M).toNat : ℕ) : ℤ) ∧ (M : ℤ) ∣ (((b % M).toNat : ℕ) : ℤ)) := by
  have hM0 : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  have ta : (((a % M).toNat : ℕ) : ℤ) = a % M := Int.toNat_of_nonneg (Int.emod_nonneg a hM0)
  have tb : (((b % M).toNat : ℕ) : ℤ) = b % M := Int.toNat_of_nonneg (Int.emod_nonneg b hM0)
  refine ⟨ta, tb, ?_, ?_⟩
  · have := Int.emod_lt_of_pos a hMpos
    omega
  · rw [ta, tb]
    rintro ⟨h1, h2⟩
    apply hab
    constructor
    · rw [← Int.emod_add_mul_ediv a M]; exact dvd_add h1 (dvd_mul_right _ _)
    · rw [← Int.emod_add_mul_ediv b M]; exact dvd_add h2 (dvd_mul_right _ _)

/- English proof (translation)
Use `isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM (norm_facts hM hab).2.2.2` as an intermediate fact. Simplify `this` using `only [Int.cast_natCast]`.
-/
theorem isAdmissibleSmoothingFactor_of_emod_index {c M : ℕ} (hM : 0 < M) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b : ℤ}
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) :
    admitted c ![(((a % M).toNat : ℕ) : ℚ) / M, (((b % M).toNat : ℕ) : ℚ) / M] := by
  have := isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM (norm_facts hM hab).2.2.2
  simpa only [Int.cast_natCast] using this

/- English proof (translation)
Take `⟨ta, tb, -, -⟩` from `norm_facts hM hab`. Rewrite using `[← siegel_add_int T (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab) ![a / M, b / M]]`. Use `congr 1`. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `qa : ((((a % M).toNat : ℕ)) : ℚ) = ((a % M : ℤ) : ℚ)`.

Use `congrArg (Int.cast : ℤ → ℚ) ta` as an intermediate fact. Rewrite `this` using `[Int.cast_natCast]`. Then use the resulting hypothesis. Establish `qb : ((((b % M).toNat : ℕ)) : ℚ) = ((b % M : ℤ) : ℚ)`. Use `congrArg (Int.cast : ℤ → ℚ) tb` as an intermediate fact. Rewrite `this` using `[Int.cast_natCast]`. Then use the resulting hypothesis.

Establish `ha : (a : ℚ) = ((a % M : ℤ) : ℚ) + M * ((a / M : ℤ) : ℚ)`. Conclude with `(Int.emod_add_mul_ediv a M).symm` after adjusting the coercions. Establish `hb : (b : ℚ) = ((b % M : ℤ) : ℚ) + M * ((b / M : ℤ) : ℚ)`. Conclude with `(Int.emod_add_mul_ediv b M).symm` after adjusting the coercions. Use function extensionality and compare the values at `i`.

Use `fin_cases i`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero]`. Rewrite using `[qa, ha]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]`.

Rewrite using `[qb, hb]`. Clear the denominators using the available nonvanishing facts.
-/
theorem siegel_norm {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε) {c M : ℕ} (hM : 0 < M)
    (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b : ℤ} (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) :
    siegel T c ![(a : ℚ) / M, (b : ℚ) / M] =
      siegel T c ![(((a % M).toNat : ℕ) : ℚ) / M, (((b % M).toNat : ℕ) : ℚ) / M] := by
  obtain ⟨ta, tb, -, -⟩ := norm_facts hM hab
  rw [← siegel_add_int T (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab) ![a / M, b / M]]
  congr 1
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have qa : ((((a % M).toNat : ℕ)) : ℚ) = ((a % M : ℤ) : ℚ) := by
    have := congrArg (Int.cast : ℤ → ℚ) ta; rwa [Int.cast_natCast] at this
  have qb : ((((b % M).toNat : ℕ)) : ℚ) = ((b % M : ℤ) : ℚ) := by
    have := congrArg (Int.cast : ℤ → ℚ) tb; rwa [Int.cast_natCast] at this
  have ha : (a : ℚ) = ((a % M : ℤ) : ℚ) + M * ((a / M : ℤ) : ℚ) := by
    exact_mod_cast (Int.emod_add_mul_ediv a M).symm
  have hb : (b : ℚ) = ((b % M : ℤ) : ℚ) + M * ((b / M : ℤ) : ℚ) := by
    exact_mod_cast (Int.emod_add_mul_ediv b M).symm
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [qa, ha]; field_simp
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [qb, hb]; field_simp

/- English proof (translation)
Rewrite `h` using `[siegel_norm T hM hc h6 hcM hab, siegel_norm T hM hc h6 hcM hab']`. Take `⟨ta, -, ha, -⟩` from `norm_facts hM hab`. Take `⟨ta', -, ha', -⟩` from `norm_facts hM hab'`. Establish `o1` using `exp_siegel_ord ε T c M _ _ hM ha (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab)`. Establish `o2` using `exp_siegel_ord ε T c M _ _ hM ha' (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab')`.

Rewrite `o1` using `[h]`. Establish `e1` using `o1.2 _ o2.1`. Establish `e2` using `o2.2 _ o1.1`. Establish `hMq : (0 : ℚ) < M` using `by exact_mod_cast hM`. Establish `e3 : (expo c M (a % M).toNat : ℚ) = expo c M (a' % M).toNat`.

Use `le_antisymm e1 e2` as an intermediate fact. Rewrite `this` using `[div_left_inj' hMq.ne']`. Then use the resulting hypothesis. Establish `e4 : expo c M (a % M).toNat = expo c M (a' % M).toNat` using `by exact_mod_cast e3`. Break down `expo_inj c M _ _ hc hcM ha ha' e4 with h5 | h5` into its components or cases. Use `left`.

Rewrite using `[← ta, ← ta', h5]`. Use `right`. Rewrite using `[← ta, ← ta']`. Conclude with `h5` after adjusting the coercions.
-/
theorem siegel_eq_imp {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    {c M : ℕ} (hM : 0 < M) (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b a' b' : ℤ}
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) (hab' : ¬ ((M : ℤ) ∣ a' ∧ (M : ℤ) ∣ b'))
    (h : siegel T c ![(a : ℚ) / M, (b : ℚ) / M] = siegel T c ![(a' : ℚ) / M, (b' : ℚ) / M]) :
    a % M = a' % M ∨ a % M + a' % M = M := by
  rw [siegel_norm T hM hc h6 hcM hab, siegel_norm T hM hc h6 hcM hab'] at h
  obtain ⟨ta, -, ha, -⟩ := norm_facts hM hab
  obtain ⟨ta', -, ha', -⟩ := norm_facts hM hab'
  have o1 := exp_siegel_ord ε T c M _ _ hM ha (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab)
  have o2 := exp_siegel_ord ε T c M _ _ hM ha' (isAdmissibleSmoothingFactor_of_emod_index hM hc h6 hcM hab')
  rw [h] at o1
  have e1 := o1.2 _ o2.1
  have e2 := o2.2 _ o1.1
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have e3 : (expo c M (a % M).toNat : ℚ) = expo c M (a' % M).toNat := by
    have := le_antisymm e1 e2
    rwa [div_left_inj' hMq.ne'] at this
  have e4 : expo c M (a % M).toNat = expo c M (a' % M).toNat := by exact_mod_cast e3
  rcases expo_inj c M _ _ hc hcM ha ha' e4 with h5 | h5
  · left; rw [← ta, ← ta', h5]
  · right; rw [← ta, ← ta']; exact_mod_cast h5

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [act, en, Fin.sum_univ_two] <;> ring`.
-/
theorem act_int (M : ℕ) (a b : ℤ) (γ : SL(2, ℤ)) :
    act ![(a : ℚ) / M, (b : ℚ) / M] γ =
      ![((a * en γ 0 0 + b * en γ 1 0 : ℤ) : ℚ) / M, ((a * en γ 0 1 + b * en γ 1 1 : ℤ) : ℚ) / M] := by
  funext i
  fin_cases i <;> simp [act, en, Fin.sum_univ_two] <;> ring

/- English proof (translation)
Introduce and unpack `⟨h1, h2⟩`. Establish `hd : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1`. Use `δ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Simplify `this` using `[en]`.

Apply `hab` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Establish `e : a = (a * en δ 0 0 + b * en δ 1 0) * en δ 1 1 - (a * en δ 0 1 + b * en δ 1 1) * en δ 1 0`. Take the linear combination `(-a) * hd`. Rewrite using `[e]`.

Conclude with `dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)`. Establish `e : b = (a * en δ 0 1 + b * en δ 1 1) * en δ 0 0 - (a * en δ 0 0 + b * en δ 1 0) * en δ 0 1`. Take the linear combination `(-b) * hd`. Rewrite using `[e]`. Conclude with `dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)`.
-/
theorem prim_act {M : ℕ} {a b : ℤ} (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) (δ : SL(2, ℤ)) :
    ¬ ((M : ℤ) ∣ (a * en δ 0 0 + b * en δ 1 0) ∧ (M : ℤ) ∣ (a * en δ 0 1 + b * en δ 1 1)) := by
  rintro ⟨h1, h2⟩
  have hd : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe; rw [Matrix.det_fin_two] at this; simpa [en] using this
  apply hab
  constructor
  · have e : a = (a * en δ 0 0 + b * en δ 1 0) * en δ 1 1 - (a * en δ 0 1 + b * en δ 1 1) * en δ 1 0 := by
      linear_combination (-a) * hd
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _)
  · have e : b = (a * en δ 0 1 + b * en δ 1 1) * en δ 0 0 - (a * en δ 0 0 + b * en δ 1 0) * en δ 0 1 := by
      linear_combination (-b) * hd
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)

/- English proof (translation)
Introduce `Ω _ _ _ ε X M c γ hM hc h6 hcM H`. Break down `Nat.lt_or_ge M 2 with hM1 | hM2` into its components or cases. Use `left`. Take `rfl : M = 1` from `by omega`. Rewrite using `[CongruenceSubgroup.Gamma_one_top]`.

Discharge the goal by the elementary cases of `trivial`. Establish `hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) → siegel X c ![((a * en γ 0 0 + b * en γ 1 0 : ℤ) : ℚ) / M, ((a * en γ 0 1 + b * en γ 1 1 : ℤ) : ℚ) / M] = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]` using `fun a b hab => by`. Rewrite using `[← act_int, ← GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ γ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM hab)]`. Conclude with `H a b hab`. Establish `hM1' : ¬ ((M : ℤ) ∣ 1)`.

Introduce `h`. Use `Int.le_of_dvd one_pos h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `p01 : ¬ ((M : ℤ) ∣ 0 ∧ (M : ℤ) ∣ 1)` using `fun h => hM1' h.2`. Establish `p10 : ¬ ((M : ℤ) ∣ 1 ∧ (M : ℤ) ∣ 0)` using `fun h => hM1' h.1`.

Establish `hr` using `siegel_eq_imp ε X hM hc h6 hcM (prim_act p01 γ) p01 (hfix 0 1 p01)`. Establish `hp` using `siegel_eq_imp ε X hM hc h6 hcM (prim_act p10 γ) p10 (hfix 1 0 p10)`. Establish `hS` using `congrArg (X.sl (ofSL ModularGroup.S)) (hfix 1 0 p10)`. Rewrite `hS` using `[GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ _ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM (prim_act p10 γ)), GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ _ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM p10), act_int, act_i …`. Establish `hq` using `siegel_eq_imp ε X hM hc h6 hcM (prim_act (prim_act p10 γ) ModularGroup.S) (prim_act p10 ModularGroup.S) hS`.

Establish `hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1`. Use `γ.det_coe` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Simplify `this` using `[en]`. Simplify using `[en, ModularGroup.S] at hr hp hq`.

Simplify using `only [en] at hd`. Establish `hMpos : (0 : ℤ) < M` using `by exact_mod_cast hM`. Establish `hr' : (M : ℤ) ∣ γ 1 0` using `hr.resolve_right fun h => (Int.emod_lt_of_pos _ hMpos).ne h`. Establish `hq' : (M : ℤ) ∣ γ 0 1` using `hq.resolve_right fun h => (Int.emod_lt_of_pos _ hMpos).ne h`. Establish `h1 : (1 : ℤ) % M = 1` using `Int.emod_eq_of_lt (by norm_num) (by omega)`.

Rewrite `hp` using `[h1]`. Establish `z10 : ((γ 1 0 : ℤ) : ZMod M) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hr'`. Establish `z01 : ((γ 0 1 : ℤ) : ZMod M) = 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hq'`. Establish `hdZ : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1`. Use `congrArg (Int.cast : ℤ → ZMod M) hd` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `this` using `[z10, mul_zero, sub_zero]`. Conclude with `this`. Break down `hp with hp | hp` into its components or cases. Use `left`.

Establish `e00 : ((γ 0 0 : ℤ) : ZMod M) = 1`. Use `(ZMod.intCast_eq_intCast_iff' (γ 0 0) 1 M).2 (by rw [hp, h1])` as an intermediate fact. Simplify using `using this`. Rewrite `hdZ` using `[e00, one_mul]`. Rewrite using `[CongruenceSubgroup.Gamma_mem]`.

Conclude with `⟨e00, z01, z10, hdZ⟩`. Use `right`. Establish `e00 : ((γ 0 0 : ℤ) : ZMod M) = -1`. Establish `h2 : (((γ 0 0 + 1 : ℤ)) : ZMod M) = 0`. Use `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ⟨γ 0 0 / M + 1, ?_⟩` and prove the remaining obligations.

Use `Int.emod_add_mul_ediv (γ 0 0) M` as an intermediate fact. Take the linear combination `-this + hp`. Move the coercions through the operations in `at h2`. Take the linear combination `h2`. Rewrite `hdZ` using `[e00]`.

Establish `e11 : ((γ 1 1 : ℤ) : ZMod M) = -1` using `by linear_combination -hdZ`. Rewrite using `[CongruenceSubgroup.Gamma_mem]`. Simplify using `only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, e00, e11, z01, z10]`. Evaluate the numerical expressions.
-/
theorem fix_siegel_pm_one : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ) (γ : SL(2, ℤ)), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → (∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) → X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) → γ ∈ CongruenceSubgroup.Gamma M ∨ -γ ∈ CongruenceSubgroup.Gamma M := by
  intro Ω _ _ _ ε X M c γ hM hc h6 hcM H
  rcases Nat.lt_or_ge M 2 with hM1 | hM2
  · left
    obtain rfl : M = 1 := by omega
    rw [CongruenceSubgroup.Gamma_one_top]; trivial
  have hfix : ∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) →
      siegel X c ![((a * en γ 0 0 + b * en γ 1 0 : ℤ) : ℚ) / M, ((a * en γ 0 1 + b * en γ 1 1 : ℤ) : ℚ) / M] =
      siegel X c ![(a : ℚ) / M, (b : ℚ) / M] := fun a b hab => by
    rw [← act_int, ← GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ γ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM hab)]; exact H a b hab
  have hM1' : ¬ ((M : ℤ) ∣ 1) := by
    intro h; have := Int.le_of_dvd one_pos h; omega
  have p01 : ¬ ((M : ℤ) ∣ 0 ∧ (M : ℤ) ∣ 1) := fun h => hM1' h.2
  have p10 : ¬ ((M : ℤ) ∣ 1 ∧ (M : ℤ) ∣ 0) := fun h => hM1' h.1
  have hr := siegel_eq_imp ε X hM hc h6 hcM (prim_act p01 γ) p01 (hfix 0 1 p01)
  have hp := siegel_eq_imp ε X hM hc h6 hcM (prim_act p10 γ) p10 (hfix 1 0 p10)
  have hS := congrArg (X.sl (ofSL ModularGroup.S)) (hfix 1 0 p10)
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ _ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM (prim_act p10 γ)),
    GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ _ (isAdmissibleSmoothingFactor_of_int_index hM hc h6 hcM p10), act_int, act_int] at hS
  have hq := siegel_eq_imp ε X hM hc h6 hcM (prim_act (prim_act p10 γ) ModularGroup.S) (prim_act p10 ModularGroup.S) hS
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; simpa [en] using this
  simp [en, ModularGroup.S] at hr hp hq
  simp only [en] at hd
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  have hr' : (M : ℤ) ∣ γ 1 0 := hr.resolve_right fun h => (Int.emod_lt_of_pos _ hMpos).ne h
  have hq' : (M : ℤ) ∣ γ 0 1 := hq.resolve_right fun h => (Int.emod_lt_of_pos _ hMpos).ne h
  have h1 : (1 : ℤ) % M = 1 := Int.emod_eq_of_lt (by norm_num) (by omega)
  rw [h1] at hp
  have z10 : ((γ 1 0 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hr'
  have z01 : ((γ 0 1 : ℤ) : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hq'
  have hdZ : ((γ 0 0 : ℤ) : ZMod M) * ((γ 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod M) hd
    push_cast at this
    rw [z10, mul_zero, sub_zero] at this
    exact this
  rcases hp with hp | hp
  · left
    have e00 : ((γ 0 0 : ℤ) : ZMod M) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff' (γ 0 0) 1 M).2 (by rw [hp, h1])
      simpa using this
    rw [e00, one_mul] at hdZ
    rw [CongruenceSubgroup.Gamma_mem]
    exact ⟨e00, z01, z10, hdZ⟩
  · right
    have e00 : ((γ 0 0 : ℤ) : ZMod M) = -1 := by
      have h2 : (((γ 0 0 + 1 : ℤ)) : ZMod M) = 0 := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 ⟨γ 0 0 / M + 1, ?_⟩
        have := Int.emod_add_mul_ediv (γ 0 0) M
        linear_combination -this + hp
      push_cast at h2
      linear_combination h2
    rw [e00] at hdZ
    have e11 : ((γ 1 1 : ℤ) : ZMod M) = -1 := by linear_combination -hdZ
    rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, e00, e11, z01, z10]
    norm_num

end GlobalTheory.SiegSep
