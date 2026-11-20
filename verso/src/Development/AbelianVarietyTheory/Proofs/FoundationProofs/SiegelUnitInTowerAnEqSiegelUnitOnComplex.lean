import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionHolomorphic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitQExpansionCoeffsIntegralStatement

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ.SiegelMem

open Polynomial in

/- English proof (translation)
Establish `h0 : minpoly ℚ α ≠ 0` using `minpoly.ne_zero hα`. Establish `e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ)`. Rewrite using `[Polynomial.map_map]`. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.

Establish `hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots`. Rewrite using `[e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot, ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]`. Conclude with `minpoly.aeval ℚ α`. Rewrite `hb` using `[Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map]`. Take `⟨y, -, hy⟩` from `hb`.

Conclude with `⟨y, hy⟩`.
-/
theorem mem_range_of_isIntegral {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {α : ℂ}
    (hα : IsIntegral ℚ α) : α ∈ Set.range ε := by
  have h0 : minpoly ℚ α ≠ 0 := minpoly.ne_zero hα
  have e : ((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    rw [Polynomial.map_map]; congr 1; exact Subsingleton.elim _ _
  have hb : α ∈ (((minpoly ℚ α).map (algebraMap ℚ Ω)).map ε).roots := by
    rw [e, Polynomial.mem_roots (Polynomial.map_ne_zero h0), Polynomial.IsRoot,
      ← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α
  rw [Polynomial.Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨y, -, hy⟩ := hb
  exact ⟨y, hy⟩

/- English proof (translation)
Establish `hMc : (M : ℂ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `h : ee (1 / (M : ℂ)) ^ M = 1`. Rewrite using `[ee, ← Complex.exp_nat_mul]`. Establish `: (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I` using `by field_simp`. Rewrite using `[this, Complex.exp_two_pi_mul_I]`.

Conclude with `IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)`.
-/
theorem isIntegral_ee {M : ℕ} (hM : 0 < M) : IsIntegral ℚ (ee (1 / (M : ℂ))) := by
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have h : ee (1 / (M : ℂ)) ^ M = 1 := by
    rw [ee, ← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact IsIntegral.of_pow hM (by rw [h]; exact isIntegral_one)

/- English proof (translation)
Use `haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)`. Establish `h` using `Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})`. Conclude with `IntermediateField.isIntegral_iff.1 h`.
-/
theorem isIntegral_of_mem_adjoin {M : ℕ} (hM : 0 < M) {z : ℂ}
    (hz : z ∈ IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))}) : IsIntegral ℚ z := by
  haveI := IntermediateField.adjoin.finiteDimensional (isIntegral_ee hM)
  have h := Algebra.IsIntegral.isIntegral (R := ℚ) (⟨z, hz⟩ : IntermediateField.adjoin ℚ {ee (1 / (M : ℂ))})
  exact IntermediateField.isIntegral_iff.1 h

/- English proof (translation)
Simplify using `[act, Fin.sum_univ_two]`.
-/
theorem act_zero (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 0 = x 0 * (γ 0 0 : ℚ) + x 1 * (γ 1 0 : ℚ) := by
  simp [act, Fin.sum_univ_two]

/- English proof (translation)
Simplify using `[act, Fin.sum_univ_two]`.
-/
theorem act_one' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act x γ 1 = x 0 * (γ 0 1 : ℚ) + x 1 * (γ 1 1 : ℚ) := by
  simp [act, Fin.sum_univ_two]

/- English proof (translation)
Use `⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩` and prove the remaining obligations. Use `all_goals`. Establish `hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1`. Use `Matrix.SpecialLinearGroup.det_coe γ` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`.

Conclude with `this` after adjusting the coercions. Rewrite `hm0` using `[act_zero]`. Rewrite `hm1` using `[act_one']`. Use `push_cast`. Take the linear combination `(γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet`.

Take the linear combination `(γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet`.
-/
theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (γ : SL(2, ℤ)) : admitted c (act x γ) := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hx.2.2 ⟨⟨m0 * γ 1 1 - m1 * γ 1 0, ?_⟩, ⟨m1 * γ 0 0 - m0 * γ 0 1, ?_⟩⟩⟩
  all_goals
    have hdet : ((γ 0 0 : ℤ) : ℚ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
      have := Matrix.SpecialLinearGroup.det_coe γ
      rw [Matrix.det_fin_two] at this
      exact_mod_cast this
    rw [act_zero] at hm0
    rw [act_one'] at hm1
    push_cast
  · linear_combination (γ 1 1 : ℚ) * hm0 - (γ 1 0 : ℚ) * hm1 + ((c : ℚ) * x 0) * hdet
  · linear_combination (γ 0 0 : ℚ) * hm1 - (γ 0 1 : ℚ) * hm0 + ((c : ℚ) * x 1) * hdet

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

/- English proof (translation)
Establish `hMz : (M : ℤ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hMq : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ)` using `fun i => by`. Rewrite using `[← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]`. Establish `hlt : (P 0 % (M : ℤ)).toNat < M`.

Use `Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0`. Use `set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1`. Use `set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'`.

Establish `hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M` using `fun i => by fin_cases i`. Simplify using `[x', ha0, hr]`. Simplify using `[x', ha1, hr]`. Use `set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn`. Establish `hyx : y = fun i => x' i + n i`.

Use function extensionality and compare the values at `i`. Establish `h1 : y i = (P i : ℚ) / M` using `by rw [← hP i]; field_simp`. Establish `h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ)`. Establish `h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ)` using `by rw [Int.emod_def]; ring`. Conclude with `h3` after adjusting the coercions.

Rewrite using `[h1, hx'i, h2]`. Simplify using `only [n]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hadm : admitted c x'`.

Use `⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩` and prove the remaining obligations. Rewrite using `[hyx]`. Use `push_cast`. Rewrite using `[hm0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hyx]`. Use `push_cast`. Rewrite using `[hm1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hper : ∀ τ : ℍ, sg c y τ = sg c x' τ` using `fun τ => by`.

Rewrite using `[hyx]`. Conclude with `GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm`. Take `⟨k, hk⟩` from `GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt`. Take `⟨A, hQ, -, hA, -, -⟩` from `hk a1 hadm`. Establish `hε : ∀ j, ε (Function.invFun ε (A j)) = A j` using `fun j => Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))`.

Use `⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k, fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩` and prove the remaining obligations. Establish `hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k)` using `fun i j h => by simpa using h`. Rewrite using `[← Function.Injective.hasSum_iff hinj (fun m hm => by`. Establish `: ¬ k ≤ m` using `fun h => hm ⟨(m - k).toNat, by simp; omega⟩`. Simplify using `[this])]`.

Establish `h1` using `(hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))`. Establish `key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ`. Rewrite using `[hper, mul_left_comm, ee, ee, ← Complex.exp_add]`. Establish `: 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Complex.exp_zero, mul_one]`. Rewrite `h1` using `[key]`. Establish `e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) * Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) = fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M))`. Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right, Int.toNat_natCast, hε]`.

Rewrite using `[mul_left_comm, ee, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `e ▸ h1`.
-/
theorem exp_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) {c M : ℕ} (hM : 0 < M)
    {y : Fin 2 → ℚ} (P : Fin 2 → ℤ) (hP : ∀ i, (M : ℚ) * y i = P i) (hy : admitted c y) :
    ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c y τ) := by
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : ∀ i, ((P i % (M : ℤ)).toNat : ℚ) = ((P i % (M : ℤ) : ℤ) : ℚ) := fun i => by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)]
  have hlt : (P 0 % (M : ℤ)).toNat < M := by
    have := Int.emod_lt_of_pos (P 0) (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  set a0 : ℕ := (P 0 % (M : ℤ)).toNat with ha0
  set a1 : ℕ := (P 1 % (M : ℤ)).toNat with ha1
  set x' : Fin 2 → ℚ := ![(a0 : ℚ) / M, (a1 : ℚ) / M] with hx'
  have hx'i : ∀ i, x' i = ((P i % (M : ℤ) : ℤ) : ℚ) / M := fun i => by
    fin_cases i
    · simp [x', ha0, hr]
    · simp [x', ha1, hr]
  set n : Fin 2 → ℤ := fun i => P i / (M : ℤ) with hn
  have hyx : y = fun i => x' i + n i := by
    funext i
    have h1 : y i = (P i : ℚ) / M := by rw [← hP i]; field_simp
    have h2 : (P i : ℚ) = (M : ℚ) * ((P i / (M : ℤ) : ℤ) : ℚ) + ((P i % (M : ℤ) : ℤ) : ℚ) := by
      have h3 : P i = (M : ℤ) * (P i / (M : ℤ)) + P i % (M : ℤ) := by rw [Int.emod_def]; ring
      exact_mod_cast h3
    rw [h1, hx'i, h2]
    simp only [n]
    field_simp
    ring
  have hadm : admitted c x' := by
    refine ⟨hy.1, hy.2.1, fun ⟨⟨m0, hm0⟩, ⟨m1, hm1⟩⟩ => hy.2.2 ⟨⟨m0 + c * n 0, ?_⟩, ⟨m1 + c * n 1, ?_⟩⟩⟩
    · rw [hyx]; push_cast; rw [hm0]; ring
    · rw [hyx]; push_cast; rw [hm1]; ring
  have hper : ∀ τ : ℍ, sg c y τ = sg c x' τ := fun τ => by
    rw [hyx]; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x' n τ hadm
  obtain ⟨k, hk⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A, hQ, -, hA, -, -⟩ := hk a1 hadm
  have hε : ∀ j, ε (Function.invFun ε (A j)) = A j := fun j =>
    Function.invFun_eq (mem_range_of_isIntegral ε (isIntegral_of_mem_adjoin hM (hA j)))
  classical
  refine ⟨fun m => if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0, k,
    fun m hm => by simp [not_le.2 hm], fun τ => ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ) + k) := fun i j h => by simpa using h
  rw [← Function.Injective.hasSum_iff hinj (fun m hm => by
    have : ¬ k ≤ m := fun h => hm ⟨(m - k).toNat, by simp; omega⟩
    simp [this])]
  have h1 := (hQ τ).mul_left (ee ((k : ℂ) / M * (τ : ℂ)))
  have key : ee ((k : ℂ) / M * (τ : ℂ)) * (sg c x' τ * ee (-((k : ℂ) / M) * (τ : ℂ))) = sg c y τ := by
    rw [hper, mul_left_comm, ee, ee, ← Complex.exp_add]
    have : 2 * ↑Real.pi * Complex.I * ((k : ℂ) / ↑M * ↑τ) + 2 * ↑Real.pi * Complex.I * (-((k : ℂ) / ↑M) * ↑τ) = 0 := by
      ring
    rw [this, Complex.exp_zero, mul_one]
  rw [key] at h1
  have e : (fun m : ℤ => ε (if k ≤ m then Function.invFun ε (A (m - k).toNat) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / M)) ∘ (fun j : ℕ => (j : ℤ) + k) =
      fun j : ℕ => ee ((k : ℂ) / M * (τ : ℂ)) * (A j * Complex.exp (2 * Real.pi * Complex.I * j * τ / M)) := by
    funext j
    simp only [Function.comp_apply, le_add_iff_nonneg_left, Nat.cast_nonneg, if_true, add_sub_cancel_right,
      Int.toNat_natCast, hε]
    rw [mul_left_comm, ee, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  exact e ▸ h1

end GlobalTheory.KZ.SiegelMem

namespace GlobalTheory.KZ.SiegelMem

/- English proof (translation)
Introduce `Ω _ _ _ ε T c x hx`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `set M : ℕ := (x 0).den * (x 1).den with hMdef`. Establish `hM : 0 < M` using `Nat.mul_pos (x 0).den_pos (x 1).den_pos`. Use `set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx`.

Establish `hMx : ∀ i, (M : ℚ) * x i = Px i` using `fun i => by fin_cases i`. Simplify using `only [hMdef, hPx, Matrix.cons_val_zero]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num (x 0)]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]`. Use `push_cast`. Rewrite using `[← Rat.mul_den_eq_num (x 1)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : DifferentiableOn ℂ (sgC c x) Hs` using `UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)`.

Establish `hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ`. Introduce `γ hγ τ`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Take `⟨g00, g01, g10, g11⟩` from `CongruenceSubgroup.Gamma_mem.1 hγ`. Establish `d00 : (M : ℤ) ∣ γ 0 0 - 1` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])`.

Establish `d01 : (M : ℤ) ∣ γ 0 1` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01`. Establish `d10 : (M : ℤ) ∣ γ 1 0` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10`. Establish `d11 : (M : ℤ) ∣ γ 1 1 - 1` using `(ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])`. Take `⟨t00, h00⟩` from `d00`. Take `⟨t01, h01⟩` from `d01`.

Take `⟨t10, h10⟩` from `d10`. Take `⟨t11, h11⟩` from `d11`. Establish `e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i`. Establish `q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00`. Establish `: γ 0 0 = 1 + M * t00` using `by rw [← h00]; ring`.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11`. Establish `: γ 1 1 = 1 + M * t11` using `by rw [← h11]; ring`.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01` using `by rw [h01]; push_cast; ring`. Establish `q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10` using `by rw [h10]; push_cast; ring`.

Establish `r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ)`. Rewrite using `[act_zero, q00, q10]`. Use `push_cast`. Rewrite using `[← hMx 0, ← hMx 1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ)`. Rewrite using `[act_one', q01, q11]`. Use `push_cast`. Rewrite using `[← hMx 0, ← hMx 1]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `using r0`. Simplify using `using r1`. Rewrite using `[e]`.

Conclude with `GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx`. Use `SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)` and prove the remaining obligations. Use `exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)` and prove the remaining obligations. Simplify using `only [act, Fin.sum_univ_two]`. Use `push_cast`.

Rewrite using `[← hMx 0, ← hMx 1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem an_siegel_eq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (x : Fin 2 → ℚ), admitted c x → T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by
  intro Ω _ _ _ ε T c x hx
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  set M : ℕ := (x 0).den * (x 1).den with hMdef
  have hM : 0 < M := Nat.mul_pos (x 0).den_pos (x 1).den_pos
  set Px : Fin 2 → ℤ := ![(x 0).num * (x 1).den, (x 1).num * (x 0).den] with hPx
  have hMx : ∀ i, (M : ℚ) * x i = Px i := fun i => by
    fin_cases i
    · simp only [hMdef, hPx, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 0)]; ring
    · simp only [hMdef, hPx, Matrix.cons_val_one, Matrix.cons_val_zero]; push_cast
      rw [← Rat.mul_den_eq_num (x 1)]; ring
  have hd : DifferentiableOn ℂ (sgC c x) Hs :=
    UpperHalfPlane.mdifferentiable_iff.1 (GlobalTheory.Sieg.mdifferentiable_sg c x hx)
  have hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ := by
    intro γ hγ τ
    haveI : NeZero M := ⟨hM.ne'⟩
    obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have d00 : (M : ℤ) ∣ γ 0 0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g00, sub_self])
    have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g01
    have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 g10
    have d11 : (M : ℤ) ∣ γ 1 1 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; rw [g11, sub_self])
    obtain ⟨t00, h00⟩ := d00
    obtain ⟨t01, h01⟩ := d01
    obtain ⟨t10, h10⟩ := d10
    obtain ⟨t11, h11⟩ := d11
    have e : act x γ = fun i => x i + (![Px 0 * t00 + Px 1 * t10, Px 0 * t01 + Px 1 * t11] : Fin 2 → ℤ) i := by
      have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * t00 := by
        have : γ 0 0 = 1 + M * t00 := by rw [← h00]; ring
        rw [this]; push_cast; ring
      have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * t11 := by
        have : γ 1 1 = 1 + M * t11 := by rw [← h11]; ring
        rw [this]; push_cast; ring
      have q01 : ((γ 0 1 : ℤ) : ℚ) = M * t01 := by rw [h01]; push_cast; ring
      have q10 : ((γ 1 0 : ℤ) : ℚ) = M * t10 := by rw [h10]; push_cast; ring
      have r0 : act x γ 0 = x 0 + ((Px 0 * t00 + Px 1 * t10 : ℤ) : ℚ) := by
        rw [act_zero, q00, q10]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      have r1 : act x γ 1 = x 1 + ((Px 0 * t01 + Px 1 * t11 : ℤ) : ℚ) := by
        rw [act_one', q01, q11]; push_cast; rw [← hMx 0, ← hMx 1]; ring
      funext i
      fin_cases i
      · simpa using r0
      · simpa using r1
    rw [e]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ τ hx
  refine SiegelModel.an_siegel T M hM hd (fun γ τ => GlobalTheory.T.siegel_function_transformation c x γ τ hx) hlev (fun γ => ?_)
  refine exp_int ε hM (fun i => Px 0 * γ 0 i + Px 1 * γ 1 i) (fun i => ?_) (admissible_act_SL2 hx γ)
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [← hMx 0, ← hMx 1]
  ring

end GlobalTheory.KZ.SiegelMem
