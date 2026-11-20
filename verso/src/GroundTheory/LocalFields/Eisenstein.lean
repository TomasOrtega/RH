import Mathlib
import GroundTheory.LocalFields.Interface
import GroundTheory.LocalFields.Integers
import GroundTheory.LocalFields.IntermediateField

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Assume the negation of the conclusion as `h0`. Establish `htop : addVal R (t j) ≠ ⊤` using `fun h => h0 (addVal_eq_top_iff.mp h)`. Establish `hrest : addVal R (t j) < addVal R (∑ i ∈ s.erase j, t i)` using `(addVal R).map_lt_sum htop fun i hi => hlt i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)`. Use `(addVal R).map_add_eq_of_lt_left hrest` as an intermediate fact. Rewrite `this` using `[Finset.add_sum_erase s t hj, hs, AddValuation.map_zero]`.

Conclude with `htop this.symm`.
-/
theorem eq_zero_of_addVal_lt_of_sum_eq_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {t : ι → R}
    (hs : ∑ i ∈ s, t i = 0) {j : ι} (hj : j ∈ s)
    (hlt : ∀ i ∈ s, i ≠ j → addVal R (t j) < addVal R (t i)) : t j = 0 := by
  by_contra h0
  have htop : addVal R (t j) ≠ ⊤ := fun h => h0 (addVal_eq_top_iff.mp h)
  have hrest : addVal R (t j) < addVal R (∑ i ∈ s.erase j, t i) :=
    (addVal R).map_lt_sum htop fun i hi => hlt i (Finset.mem_of_mem_erase hi)
      (Finset.ne_of_mem_erase hi)
  have := (addVal R).map_add_eq_of_lt_left hrest
  rw [Finset.add_sum_erase s t hj, hs, AddValuation.map_zero] at this
  exact htop this.symm

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Take `⟨k, u, rfl⟩` from `eq_unit_mul_pow_irreducible hx hϖ`. Conclude with `⟨k, addVal_def' u hϖ k⟩`.
-/
theorem exists_addVal_eq_coe {x : R} (hx : x ≠ 0) : ∃ k : ℕ, addVal R x = k := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  exact ⟨k, addVal_def' u hϖ k⟩

end DVR

section Local

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible 𝒪[K]`. Take `⟨ϖL, hϖL⟩` from `exists_irreducible 𝒪[L]`. Establish `key : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] ϖ) = ramificationIndex K L`. Establish `h` using `map_maximalIdeal K L`. Rewrite `h` using `[hϖ.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]`.

Rewrite using `[(addVal_eq_iff_associated _ _).mpr h, hϖL.addVal_pow]`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Rewrite using `[map_zero, addVal_zero, addVal_zero, ENat.mul_top]`. Conclude with `(ramificationIndex_pos K L).ne'` after adjusting the coercions. Take `⟨k, u, rfl⟩` from `eq_unit_mul_pow_irreducible hx hϖ`.

Rewrite using `[map_mul, map_pow, addVal_mul, addVal_pow, key, addVal_def' u hϖ k]`. Establish `hu : IsUnit (algebraMap 𝒪[K] 𝒪[L] u)` using `u.isUnit.map _`. Rewrite using `[addVal_eq_zero_iff.mpr hu, zero_add, nsmul_eq_mul, mul_comm]`.
-/
theorem addVal_algebraMap_integer (x : 𝒪[K]) :
    addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) = ramificationIndex K L * addVal 𝒪[K] x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[K]
  obtain ⟨ϖL, hϖL⟩ := exists_irreducible 𝒪[L]
  have key : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] ϖ) = ramificationIndex K L := by
    have h := map_maximalIdeal K L
    rw [hϖ.maximalIdeal_eq, hϖL.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
    rw [(addVal_eq_iff_associated _ _).mpr h, hϖL.addVal_pow]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addVal_zero, addVal_zero, ENat.mul_top]
    exact_mod_cast (ramificationIndex_pos K L).ne'
  obtain ⟨k, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  rw [map_mul, map_pow, addVal_mul, addVal_pow, key, addVal_def' u hϖ k]
  have hu : IsUnit (algebraMap 𝒪[K] 𝒪[L] u) := u.isUnit.map _
  rw [addVal_eq_zero_iff.mpr hu, zero_add, nsmul_eq_mul, mul_comm]

end Local

section DVR2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow]`.
-/
theorem mem_maximalIdeal_pow_iff_le_addVal (k : ℕ) (x : R) :
    x ∈ IsLocalRing.maximalIdeal R ^ k ↔ (k : ℕ∞) ≤ addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hϖ.addVal_pow]

/- English proof (translation)
Rewrite `h1` using `[← pow_one (IsLocalRing.maximalIdeal R), mem_maximalIdeal_pow_iff_le_addVal]`. Rewrite `h2` using `[mem_maximalIdeal_pow_iff_le_addVal, not_le]`. Establish `h0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h2`.

Take `⟨k, hk⟩` from `exists_addVal_eq_coe h0`. Rewrite `h1`, `h2`, the goal using `[hk]`. Normalize the coercions in `at h1 h2 ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem addVal_eq_one_of_mem_of_notMem_sq {x : R} (h1 : x ∈ IsLocalRing.maximalIdeal R)
    (h2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) : addVal R x = 1 := by
  rw [← pow_one (IsLocalRing.maximalIdeal R), mem_maximalIdeal_pow_iff_le_addVal] at h1
  rw [mem_maximalIdeal_pow_iff_le_addVal, not_le] at h2
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at h2
  obtain ⟨k, hk⟩ := exists_addVal_eq_coe h0
  rw [hk] at h1 h2 ⊢
  norm_cast at h1 h2 ⊢
  omega

end DVR2

section Forward

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Use `set n := f.natDegree with hn_def`. Use `set e := ramificationIndex K L with he_def`. Establish `he : 0 < e` using `ramificationIndex_pos K L`. Establish `hinj` using `algebraMap_integer_injective K L`. Establish `hα0 : α ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hα` using `[aeval_def, eval₂_at_zero]`. Establish `: f.coeff 0 = 0` using `hinj (by rw [hα, map_zero])`. Conclude with `hf.notMem (by rw [this]; exact zero_mem _)`. Take `⟨m, hm⟩` from `exists_addVal_eq_coe hα0`.

Use `set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * α ^ i with ht`. Establish `hsum : ∑ i ∈ Finset.range (n + 1), t i = 0`. Rewrite using `[← hα, aeval_eq_sum_range]`. Simplify using `[t, Algebra.smul_def, n]`. Establish `hval : ∀ i, addVal 𝒪[L] (t i) = e * addVal 𝒪[K] (f.coeff i) + i * m`.

Introduce `i`. Simplify using `only [t, addVal_mul, addVal_pow, addVal_algebraMap_integer, hm, nsmul_eq_mul, e]`. Establish `hlow : ∀ i < n, ((e + i * m : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i)`. Introduce `i hi`. Establish `h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i)`.

Use `hf.mem hi` as an intermediate fact. Rewrite `this` using `[← pow_one (IsLocalRing.maximalIdeal 𝒪[K]), mem_maximalIdeal_pow_iff_le_addVal]`. Conclude with `this` after adjusting the coercions. Rewrite using `[hval]`. Use `push_cast`.

Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Establish `htop : addVal 𝒪[L] (t n) = ((n * m : ℕ) : ℕ∞)`. Establish `hu : IsUnit (f.coeff n)`. Use `hf.leading` as an intermediate fact.

Rewrite `this` using `[leadingCoeff]`. Conclude with `(IsLocalRing.notMem_maximalIdeal.mp this)`. Rewrite using `[hval, addVal_eq_zero_iff.mpr hu]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hbot : addVal 𝒪[L] (t 0) = (e : ℕ∞)`. Establish `h1 : f.coeff 0 ∈ IsLocalRing.maximalIdeal 𝒪[K]` using `hf.mem hn`. Rewrite using `[hval, addVal_eq_one_of_mem_of_notMem_sq h1 hf.notMem]`. Simplify using the standard rewrite rules. Establish `hne_n : t n ≠ 0`.

Introduce `h`. Rewrite `htop` using `[h, addVal_zero]`. Conclude with `ENat.top_ne_natCast _ htop`. Establish `hne_0 : t 0 ≠ 0`. Introduce `h`.

Rewrite `hbot` using `[h, addVal_zero]`. Conclude with `ENat.top_ne_natCast _ hbot`. Establish `hA : e ≤ n * m`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`.

Use `hne_n (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ n) ?_)` and prove the remaining obligations. Introduce `i hi hin`. Establish `hi' : i < n` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin`. Use `lt_of_lt_of_le ?_ (hlow i hi')` and prove the remaining obligations. Rewrite using `[htop]`.

Conclude with `(by omega : n * m < e + i * m)` after adjusting the coercions. Establish `hm1 : 1 ≤ m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Rewrite `hA` using `[h]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hB : n * m ≤ e`. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Use `hne_0 (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (by simp) ?_)` and prove the remaining obligations.

Introduce `i hi hi0`. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Rewrite using `[hbot]`. Break down `lt_or_eq_of_le hi' with hlt' | rfl` into its components or cases. Use `lt_of_lt_of_le ?_ (hlow i hlt')` and prove the remaining obligations.

Establish `: 1 ≤ i * m` using `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hi0 (by omega))`. Conclude with `(by omega : e < e + i * m)` after adjusting the coercions. Rewrite using `[htop]`. Conclude with `hlt` after adjusting the coercions. Rewrite using `[hm]`.

Conclude with `le_antisymm hB hA` after adjusting the coercions.
-/
theorem natDegree_mul_addVal_eq_ramificationIndex {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
    {α : 𝒪[L]} (hα : aeval α f = 0) :
    (f.natDegree : ℕ∞) * addVal 𝒪[L] α = ramificationIndex K L := by
  set n := f.natDegree with hn_def
  set e := ramificationIndex K L with he_def
  have he : 0 < e := ramificationIndex_pos K L
  have hinj := algebraMap_integer_injective K L
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [aeval_def, eval₂_at_zero] at hα
    have : f.coeff 0 = 0 := hinj (by rw [hα, map_zero])
    exact hf.notMem (by rw [this]; exact zero_mem _)
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (f.coeff i) * α ^ i with ht
  have hsum : ∑ i ∈ Finset.range (n + 1), t i = 0 := by
    rw [← hα, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, n]
  have hval : ∀ i, addVal 𝒪[L] (t i) = e * addVal 𝒪[K] (f.coeff i) + i * m := by
    intro i
    simp only [t, addVal_mul, addVal_pow, addVal_algebraMap_integer, hm, nsmul_eq_mul, e]

  have hlow : ∀ i < n, ((e + i * m : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi
    have h1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff i) := by
      have := hf.mem hi
      rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[K]), mem_maximalIdeal_pow_iff_le_addVal] at this
      exact_mod_cast this
    rw [hval]
    push_cast
    gcongr
    calc (e : ℕ∞) = e * 1 := (mul_one _).symm
      _ ≤ e * addVal 𝒪[K] (f.coeff i) := by gcongr

  have htop : addVal 𝒪[L] (t n) = ((n * m : ℕ) : ℕ∞) := by
    have hu : IsUnit (f.coeff n) := by
      have := hf.leading
      rw [leadingCoeff] at this
      exact (IsLocalRing.notMem_maximalIdeal.mp this)
    rw [hval, addVal_eq_zero_iff.mpr hu]
    push_cast
    ring

  have hbot : addVal 𝒪[L] (t 0) = (e : ℕ∞) := by
    have h1 : f.coeff 0 ∈ IsLocalRing.maximalIdeal 𝒪[K] := hf.mem hn
    rw [hval, addVal_eq_one_of_mem_of_notMem_sq h1 hf.notMem]
    simp
  have hne_n : t n ≠ 0 := by
    intro h
    rw [h, addVal_zero] at htop
    exact ENat.top_ne_natCast _ htop
  have hne_0 : t 0 ≠ 0 := by
    intro h
    rw [h, addVal_zero] at hbot
    exact ENat.top_ne_natCast _ hbot

  have hA : e ≤ n * m := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_n (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ n) ?_)
    intro i hi hin
    have hi' : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    refine lt_of_lt_of_le ?_ (hlow i hi')
    rw [htop]
    exact_mod_cast (by omega : n * m < e + i * m)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hA
      omega
    · exact h

  have hB : n * m ≤ e := by
    by_contra hlt
    rw [not_le] at hlt
    refine hne_0 (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (by simp) ?_)
    intro i hi hi0
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hbot]
    rcases lt_or_eq_of_le hi' with hlt' | rfl
    · refine lt_of_lt_of_le ?_ (hlow i hlt')
      have : 1 ≤ i * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hi0 (by omega))
      exact_mod_cast (by omega : e < e + i * m)
    · rw [htop]
      exact_mod_cast hlt
  rw [hm]
  exact_mod_cast le_antisymm hB hA

end Forward

section TotallyRamified

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Establish `h1` using `ramificationIndex_mul_residueDegree K L`. Establish `h2` using `ramificationIndex_pos K L`. Rewrite `h1`, `h2` using `[h]`. Conclude with `(Nat.mul_eq_left h2.ne').mp h1`.
-/
theorem residueDegree_eq_one_of_ramificationIndex_eq_finrank
    (h : ramificationIndex K L = Module.finrank K L) : residueDegree K L = 1 := by
  have h1 := ramificationIndex_mul_residueDegree K L
  have h2 := ramificationIndex_pos K L
  rw [h] at h1 h2
  exact (Nat.mul_eq_left h2.ne').mp h1

/- English proof (translation)
Rewrite `h` using `[residueDegree_eq_finrank, finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero]`. Take `⟨c, hc⟩` from `h (IsLocalRing.residue 𝒪[L] w)`. Take `⟨c', rfl⟩` from `IsLocalRing.residue_surjective c`. Use `⟨c', ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_residue, sub_self]`.
-/
theorem exists_sub_algebraMap_mem_maximalIdeal (h : residueDegree K L = 1) (w : 𝒪[L]) :
    ∃ c : 𝒪[K], w - algebraMap 𝒪[K] 𝒪[L] c ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
  rw [residueDegree_eq_finrank, finrank_eq_one_iff_of_nonzero' (1 : 𝓀[L]) one_ne_zero] at h
  obtain ⟨c, hc⟩ := h (IsLocalRing.residue 𝒪[L] w)
  obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
  refine ⟨c', ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc, Algebra.smul_def, mul_one,
    IsLocalRing.ResidueField.algebraMap_residue, sub_self]

end TotallyRamified

section Eisenstein

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/- English proof (translation)
The claim follows from `IsLocalRing.notMem_maximalIdeal.mp hf.leading`.
-/
theorem isUnit_leadingCoeff_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading

/- English proof (translation)
Introduce `r hr`. Rewrite `hr` using `[C_dvd_iff_dvd_coeff]`. Conclude with `isUnit_of_dvd_unit (hr _) (isUnit_leadingCoeff_of_isEisensteinAt hf)`.
-/
theorem isPrimitive_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) : f.IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  exact isUnit_of_dvd_unit (hr _) (isUnit_leadingCoeff_of_isEisensteinAt hf)

/- English proof (translation)
The claim follows from `hf.irreducible (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime (isPrimitive_of_isEisensteinAt hf) hn`.
-/
theorem irreducible_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible f :=
  hf.irreducible (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).isPrime
    (isPrimitive_of_isEisensteinAt hf) hn

/- English proof (translation)
The claim follows from `(isPrimitive_of_isEisensteinAt hf).irreducible_iff_irreducible_map_fraction_map.mp (irreducible_of_isEisensteinAt hf hn)`.
-/
theorem irreducible_map_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap 𝒪[K] K)) :=
  (isPrimitive_of_isEisensteinAt hf).irreducible_iff_irreducible_map_fraction_map.mp
    (irreducible_of_isEisensteinAt hf hn)

variable [Field L] [Algebra K L]

/- English proof (translation)
Take `⟨u, hu⟩` from `isUnit_leadingCoeff_of_isEisensteinAt hf`. Use `⟨C (↑u⁻¹ : 𝒪[K]) * f, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, map_mul, hα, mul_zero]`.
-/
theorem isIntegral_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    IsIntegral 𝒪[K] α := by
  obtain ⟨u, hu⟩ := isUnit_leadingCoeff_of_isEisensteinAt hf
  refine ⟨C (↑u⁻¹ : 𝒪[K]) * f, monic_C_mul_of_mul_leadingCoeff_eq_one (by rw [← hu]; simp), ?_⟩
  rw [← aeval_def, map_mul, hα, mul_zero]

/- English proof (translation)
Establish `hint : IsIntegral K α` using `(isIntegral_of_isEisensteinAt hf hα).tower_top`. Establish `hinj : Function.Injective (algebraMap 𝒪[K] K)` using `IsFractionRing.injective 𝒪[K] K`. Establish `hne : f.map (algebraMap 𝒪[K] K) ≠ 0`. Rewrite using `[Ne, Polynomial.map_eq_zero_iff hinj]`. Introduce and unpack `rfl`.

Conclude with `hf.leading (by simp)`. Rewrite using `[IntermediateField.adjoin.finrank hint, ← natDegree_map_eq_of_injective hinj f]`. Conclude with `natDegree_le_of_dvd (minpoly.dvd K α (by rw [aeval_map_algebraMap, hα])) hne`.
-/
theorem finrank_adjoin_le_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ ≤ f.natDegree := by
  have hint : IsIntegral K α := (isIntegral_of_isEisensteinAt hf hα).tower_top
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hne : f.map (algebraMap 𝒪[K] K) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hinj]
    rintro rfl
    exact hf.leading (by simp)
  rw [IntermediateField.adjoin.finrank hint, ← natDegree_map_eq_of_injective hinj f]
  exact natDegree_le_of_dvd (minpoly.dvd K α (by rw [aeval_map_algebraMap, hα])) hne

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap 𝒪[K] K)` using `IsFractionRing.injective 𝒪[K] K`. Establish `hc : algebraMap 𝒪[K] K f.leadingCoeff ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ hinj]`. Introduce and unpack `h`. Conclude with `hf.leading (by rw [h]; exact zero_mem _)`.

Use `(minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm` and prove the remaining obligations. Rewrite using `[irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc)))]`. Conclude with `irreducible_map_of_isEisensteinAt hf hn`. Rewrite using `[map_mul, aeval_map_algebraMap, hα, mul_zero]`. Use `monic_C_mul_of_mul_leadingCoeff_eq_one ?_` and prove the remaining obligations.

Rewrite using `[leadingCoeff_map_of_injective hinj, inv_mul_cancel₀ hc]`.
-/
theorem minpoly_eq_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree) {α : L}
    (hα : aeval α f = 0) :
    minpoly K α = C (algebraMap 𝒪[K] K f.leadingCoeff)⁻¹ * f.map (algebraMap 𝒪[K] K) := by
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := IsFractionRing.injective 𝒪[K] K
  have hc : algebraMap 𝒪[K] K f.leadingCoeff ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    rintro h
    exact hf.leading (by rw [h]; exact zero_mem _)
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · rw [irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc)))]
    exact irreducible_map_of_isEisensteinAt hf hn
  · rw [map_mul, aeval_map_algebraMap, hα, mul_zero]
  · refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [leadingCoeff_map_of_injective hinj, inv_mul_cancel₀ hc]

end Eisenstein

section Root

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}

/- English proof (translation)
The claim follows from `(isIntegral_iff K L α).mp (isIntegral_of_isEisensteinAt hf hα)`.
-/
theorem mem_integer_of_isEisensteinAt (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    {α : L} (hα : aeval α f = 0) : α ∈ 𝒪[L] :=
  (isIntegral_iff K L α).mp (isIntegral_of_isEisensteinAt hf hα)

/- English proof (translation)
Use `Subtype.val_injective ?_` and prove the remaining obligations. Establish `h2 : (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) (aeval (⟨α, h⟩ : 𝒪[L]) f) = aeval α f` using `(aeval_algHom_apply _ _ _).symm`. Rewrite `h2` using `[hα]`. Simplify using `using h2`.
-/
theorem aeval_integer_eq_zero {α : L} (h : α ∈ 𝒪[L]) (hα : aeval α f = 0) :
    aeval (⟨α, h⟩ : 𝒪[L]) f = 0 := by
  refine Subtype.val_injective ?_
  have h2 : (IsScalarTower.toAlgHom 𝒪[K] 𝒪[L] L) (aeval (⟨α, h⟩ : 𝒪[L]) f) = aeval α f :=
    (aeval_algHom_apply _ _ _).symm
  rw [hα] at h2
  simpa using h2

/- English proof (translation)
Establish `key` using `natDegree_mul_addVal_eq_ramificationIndex hf hn hα`. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`. Rewrite `key` using `[addVal_zero, ENat.mul_top (by exact_mod_cast hn.ne')]`. Conclude with `ENat.top_ne_natCast _ key`.

Take `⟨m, hm⟩` from `exists_addVal_eq_coe hα0`. Rewrite `key` using `[hm]`. Establish `key' : f.natDegree * m = ramificationIndex K L` using `by exact_mod_cast key`. Establish `hef` using `ramificationIndex_mul_residueDegree K L`. Establish `hf1` using `residueDegree_pos K L`.

Establish `he` using `ramificationIndex_pos K L`. Establish `hle : ramificationIndex K L ≤ Module.finrank K L`. Rewrite using `[← hef]`. Conclude with `Nat.le_mul_of_pos_right _ hf1`. Establish `hm1 : m = 1`.

Break down `Nat.lt_or_ge m 1 with h | h` into its components or cases. Establish `: m = 0` using `by omega`. Rewrite `key'` using `[this, mul_zero]`. Use linear arithmetic over natural numbers and integers. Establish `: f.natDegree * m ≤ f.natDegree * 1` using `by omega`.

Use `Nat.le_of_mul_le_mul_left this hn` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Substitute `hm1` using the available equality. Rewrite `key'` using `[mul_one]`. Use `⟨key'.symm, by omega, ?_⟩` and prove the remaining obligations.

Take `⟨ϖ, hϖ⟩` from `exists_irreducible 𝒪[L]`. Establish `: Associated ϖ α`. Rewrite using `[← addVal_eq_iff_associated, addVal_uniformizer hϖ, hm, Nat.cast_one]`. Conclude with `this.irreducible hϖ`.
-/
theorem isEisensteinAt_root_of_finrank_le (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < f.natDegree) {α : 𝒪[L]} (hα : aeval α f = 0)
    (hdeg : Module.finrank K L ≤ f.natDegree) :
    ramificationIndex K L = f.natDegree ∧ Module.finrank K L = f.natDegree ∧ Irreducible α := by
  have key := natDegree_mul_addVal_eq_ramificationIndex hf hn hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [addVal_zero, ENat.mul_top (by exact_mod_cast hn.ne')] at key
    exact ENat.top_ne_natCast _ key
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  rw [hm] at key
  have key' : f.natDegree * m = ramificationIndex K L := by exact_mod_cast key
  have hef := ramificationIndex_mul_residueDegree K L
  have hf1 := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hle : ramificationIndex K L ≤ Module.finrank K L := by
    rw [← hef]
    exact Nat.le_mul_of_pos_right _ hf1
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      rw [this, mul_zero] at key'
      omega
    · have : f.natDegree * m ≤ f.natDegree * 1 := by omega
      have := Nat.le_of_mul_le_mul_left this hn
      omega
  subst hm1
  rw [mul_one] at key'
  refine ⟨key'.symm, by omega, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
  have : Associated ϖ α := by
    rw [← addVal_eq_iff_associated, addVal_uniformizer hϖ, hm, Nat.cast_one]
  exact this.irreducible hϖ

variable (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)
include hf hn hα

section Generated

variable (hgen : K⟮α⟯ = ⊤)
include hgen

omit hn in

/- English proof (translation)
Rewrite using `[← IntermediateField.finrank_top', ← hgen]`. Conclude with `finrank_adjoin_le_of_isEisensteinAt hf hα`.
-/
theorem finrank_le_of_isEisensteinAt : Module.finrank K L ≤ f.natDegree := by
  rw [← IntermediateField.finrank_top', ← hgen]
  exact finrank_adjoin_le_of_isEisensteinAt hf hα

/- English proof (translation)
The claim follows from `(isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.1`.
-/
theorem finrank_eq_natDegree_of_isEisensteinAt : Module.finrank K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.1

/- English proof (translation)
The claim follows from `(isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).1`.
-/
theorem ramificationIndex_eq_natDegree_of_isEisensteinAt : ramificationIndex K L = f.natDegree :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).1

/- English proof (translation)
The claim follows from `(isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.2`.
-/
theorem irreducible_of_isEisensteinAt_root :
    Irreducible (⟨α, mem_integer_of_isEisensteinAt hf hα⟩ : 𝒪[L]) :=
  (isEisensteinAt_root_of_finrank_le hf hn (aeval_integer_eq_zero
    (mem_integer_of_isEisensteinAt hf hα) hα) (finrank_le_of_isEisensteinAt hf hα hgen)).2.2

end Generated

end Root

section AdjoinRoot

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]} (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) (hn : 0 < f.natDegree)
  {α : L} (hα : aeval α f = 0)

include hf hα

include hn

end AdjoinRoot

section Converse

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  (h : ramificationIndex K L = Module.finrank K L) {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include h hϖ

/- English proof (translation)
Establish `hval : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = Module.finrank K L * addVal 𝒪[K] (g.coeff i) + i`. Rewrite using `[addVal_mul, addVal_algebraMap_integer, h, hϖ.addVal_pow]`. Use `⟨fun k hk => ?_, fun hu => ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[mem_maximalIdeal_pow_iff_le_addVal]`. Rewrite using `[hval]`.

Use `push_cast`. Use `gcongr`. Rewrite using `[hval, addVal_eq_zero_iff.mpr hu, mul_zero, zero_add]`.
-/
theorem addVal_term_of_totallyRamified (g : 𝒪[K][X]) (i : ℕ) :
    (∀ k, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ k →
      ((Module.finrank K L * k + i : ℕ) : ℕ∞) ≤
        addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i)) ∧
    (IsUnit (g.coeff i) → addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) = i) := by
  have hval : addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i) =
      Module.finrank K L * addVal 𝒪[K] (g.coeff i) + i := by
    rw [addVal_mul, addVal_algebraMap_integer, h, hϖ.addVal_pow]
  refine ⟨fun k hk => ?_, fun hu => ?_⟩
  · rw [mem_maximalIdeal_pow_iff_le_addVal] at hk
    rw [hval]
    push_cast
    gcongr
  · rw [hval, addVal_eq_zero_iff.mpr hu, mul_zero, zero_add]

/- English proof (translation)
Use `set g := minpoly 𝒪[K] (ϖ : L) with hg_def`. Use `set n := Module.finrank K L with hn_def`. Establish `hint : IsIntegral 𝒪[K] (ϖ : L)` using `(isIntegral_iff K L _).mpr ϖ.2`. Establish `hmon : g.Monic` using `minpoly.monic hint`. Use `set d := g.natDegree with hd_def`.

Establish `hd0 : 0 < d` using `minpoly.natDegree_pos hint`. Establish `hmap : minpoly K (ϖ : L) = g.map (algebraMap 𝒪[K] K)` using `minpoly.isIntegrallyClosed_eq_field_fractions' K hint`. Establish `hdn : d ≤ n`. Use `minpoly.natDegree_le (A := K) (ϖ : L)` as an intermediate fact. Rewrite `this` using `[hmap, hmon.natDegree_map]`. Then use the resulting hypothesis.

Establish `hn0 : 0 < n` using `Module.finrank_pos`. Establish `hroot : aeval ϖ g = 0`. Use `aeval_integer_eq_zero (f := g) ϖ.2 (minpoly.aeval 𝒪[K] (ϖ : L))` as an intermediate fact. Simplify using `using this`. Use `set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i with ht`.

Establish `hsum : ∑ i ∈ Finset.range (d + 1), t i = 0`. Rewrite using `[← hroot, aeval_eq_sum_range]`. Simplify using `[t, Algebra.smul_def, d]`. Establish `hterm` using `addVal_term_of_totallyRamified h hϖ g`. Establish `hne : ∀ i, IsUnit (g.coeff i) → t i ≠ 0`.

Introduce `i hu h0`. Use `(hterm i).2 hu` as an intermediate fact. Simplify using `only [t] at h0`. Rewrite `this` using `[h0, addVal_zero]`. Conclude with `ENat.top_ne_natCast _ this`.

Establish `hlow : ∀ i, ((i : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i)`. Introduce `i`. Use `(hterm i).1 0 (by simp)` as an intermediate fact. Rewrite `this` using `[mul_zero, zero_add]`. Conclude with `this`.

Establish `hmem : ∀ i < d, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K]`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hex : ∃ j, j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K]` using `hcon`. Set `j` to `Nat.find hex`.

Establish `hj : j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K]` using `Nat.find_spec hex`. Establish `hu : IsUnit (g.coeff j)` using `IsLocalRing.notMem_maximalIdeal.mp hj.2`. Use `hne j hu (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.mem_range.mpr (by omega)) fun i hi hij => ?_)` and prove the remaining obligations. Rewrite using `[(hterm j).2 hu]`. Break down `lt_or_gt_of_ne hij with hlt | hgt` into its components or cases.

Establish `hi' : g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K]`. Assume the negation of the conclusion as `hc`. Conclude with `Nat.find_min hex hlt ⟨by omega, hc⟩`. Use `(hterm i).1 1 (by rwa [pow_one])` as an intermediate fact. Use `lt_of_lt_of_le ?_ this` and prove the remaining obligations.

Conclude with `(by omega : j < n * 1 + i)` after adjusting the coercions. Conclude with `lt_of_lt_of_le (by exact_mod_cast hgt) (hlow i)`. Establish `htop : t d = ϖ ^ d`. Simplify using `only [t]`. Rewrite using `[show g.coeff d = 1 from hmon]`.

Simplify using the standard rewrite rules. Establish `htop_val : addVal 𝒪[L] (t d) = d` using `by rw [htop, hϖ.addVal_pow]`. Establish `htop_ne : t d ≠ 0`. Rewrite using `[htop]`. Conclude with `pow_ne_zero _ hϖ.ne_zero`.

Establish `hmid : ∀ i, 0 < i → i < d → ((n + 1 : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i)`. Introduce `i hi0 hid`. Use `(hterm i).1 1 (by rw [pow_one]; exact hmem i hid)` as an intermediate fact. Use `le_trans ?_ this` and prove the remaining obligations. Conclude with `(by omega : n + 1 ≤ n * 1 + i)` after adjusting the coercions.

Establish `hsq : g.coeff 0 ∉ IsLocalRing.maximalIdeal 𝒪[K] ^ 2`. Introduce `hc`. Use `htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d) fun i hi hid => ?_)` and prove the remaining obligations. Establish `hid' : i < d` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid`. Rewrite using `[htop_val]`.

Break down `Nat.eq_zero_or_pos i with rfl | hi0` into its components or cases. Use `lt_of_lt_of_le ?_ ((hterm 0).1 2 hc)` and prove the remaining obligations. Conclude with `(by omega : d < n * 2 + 0)` after adjusting the coercions. Conclude with `lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')`. Establish `Heisenberg₂ : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])` using `{ leading := by`.

Rewrite using `[hmon.leadingCoeff]`. Conclude with `fun h1 => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top ((Ideal.eq_top_iff_one _).mpr h1)`. Use `mem := fun hi => hmem _ hi`. Use `notMem := hsq }`. Use `⟨Heisenberg₂, le_antisymm hdn ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `h0val : addVal 𝒪[L] (t 0) = n`. Simplify using `only [t]`. Rewrite using `[addVal_mul, addVal_algebraMap_integer, h, addVal_eq_one_of_mem_of_notMem_sq (hmem 0 hd0) hsq]`.

Simplify using the standard rewrite rules. Use `htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d) fun i hi hid => ?_)` and prove the remaining obligations. Establish `hid' : i < d` using `lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid`. Rewrite using `[htop_val]`. Break down `Nat.eq_zero_or_pos i with rfl | hi0` into its components or cases.

Rewrite using `[h0val]`. Conclude with `hlt` after adjusting the coercions. Conclude with `lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')`.
-/
theorem minpoly_isEisensteinAt_of_irreducible :
    (minpoly 𝒪[K] (ϖ : L)).IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) ∧
      (minpoly 𝒪[K] (ϖ : L)).natDegree = Module.finrank K L := by
  set g := minpoly 𝒪[K] (ϖ : L) with hg_def
  set n := Module.finrank K L with hn_def
  have hint : IsIntegral 𝒪[K] (ϖ : L) := (isIntegral_iff K L _).mpr ϖ.2
  have hmon : g.Monic := minpoly.monic hint
  set d := g.natDegree with hd_def
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hmap : minpoly K (ϖ : L) = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hdn : d ≤ n := by
    have := minpoly.natDegree_le (A := K) (ϖ : L)
    rwa [hmap, hmon.natDegree_map] at this
  have hn0 : 0 < n := Module.finrank_pos
  have hroot : aeval ϖ g = 0 := by
    have := aeval_integer_eq_zero (f := g) ϖ.2 (minpoly.aeval 𝒪[K] (ϖ : L))
    simpa using this
  set t : ℕ → 𝒪[L] := fun i => algebraMap 𝒪[K] 𝒪[L] (g.coeff i) * ϖ ^ i with ht
  have hsum : ∑ i ∈ Finset.range (d + 1), t i = 0 := by
    rw [← hroot, aeval_eq_sum_range]
    simp [t, Algebra.smul_def, d]
  have hterm := addVal_term_of_totallyRamified h hϖ g
  have hne : ∀ i, IsUnit (g.coeff i) → t i ≠ 0 := by
    intro i hu h0
    have := (hterm i).2 hu
    simp only [t] at h0
    rw [h0, addVal_zero] at this
    exact ENat.top_ne_natCast _ this
  have hlow : ∀ i, ((i : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i
    have := (hterm i).1 0 (by simp)
    rw [mul_zero, zero_add] at this
    exact this

  have hmem : ∀ i < d, g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ j, j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := hcon
    classical
    let j := Nat.find hex
    have hj : j < d ∧ g.coeff j ∉ IsLocalRing.maximalIdeal 𝒪[K] := Nat.find_spec hex
    have hu : IsUnit (g.coeff j) := IsLocalRing.notMem_maximalIdeal.mp hj.2
    refine hne j hu (eq_zero_of_addVal_lt_of_sum_eq_zero hsum
      (Finset.mem_range.mpr (by omega)) fun i hi hij => ?_)
    rw [(hterm j).2 hu]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hi' : g.coeff i ∈ IsLocalRing.maximalIdeal 𝒪[K] := by
        by_contra hc
        exact Nat.find_min hex hlt ⟨by omega, hc⟩
      have := (hterm i).1 1 (by rwa [pow_one])
      refine lt_of_lt_of_le ?_ this
      exact_mod_cast (by omega : j < n * 1 + i)
    · exact lt_of_lt_of_le (by exact_mod_cast hgt) (hlow i)
  have htop : t d = ϖ ^ d := by
    simp only [t]
    rw [show g.coeff d = 1 from hmon]
    simp
  have htop_val : addVal 𝒪[L] (t d) = d := by rw [htop, hϖ.addVal_pow]
  have htop_ne : t d ≠ 0 := by
    rw [htop]
    exact pow_ne_zero _ hϖ.ne_zero

  have hmid : ∀ i, 0 < i → i < d → ((n + 1 : ℕ) : ℕ∞) ≤ addVal 𝒪[L] (t i) := by
    intro i hi0 hid
    have := (hterm i).1 1 (by rw [pow_one]; exact hmem i hid)
    refine le_trans ?_ this
    exact_mod_cast (by omega : n + 1 ≤ n * 1 + i)

  have hsq : g.coeff 0 ∉ IsLocalRing.maximalIdeal 𝒪[K] ^ 2 := by
    intro hc
    refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
      fun i hi hid => ?_)
    have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
    rw [htop_val]
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · refine lt_of_lt_of_le ?_ ((hterm 0).1 2 hc)
      exact_mod_cast (by omega : d < n * 2 + 0)
    · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')
  have Heisenberg₂ : g.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]) :=
    { leading := by
        rw [hmon.leadingCoeff]
        exact fun h1 => (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      mem := fun hi => hmem _ hi
      notMem := hsq }
  refine ⟨Heisenberg₂, le_antisymm hdn ?_⟩

  by_contra hlt
  rw [not_le] at hlt
  have h0val : addVal 𝒪[L] (t 0) = n := by
    simp only [t]
    rw [addVal_mul, addVal_algebraMap_integer, h,
      addVal_eq_one_of_mem_of_notMem_sq (hmem 0 hd0) hsq]
    simp
  refine htop_ne (eq_zero_of_addVal_lt_of_sum_eq_zero hsum (Finset.self_mem_range_succ d)
    fun i hi hid => ?_)
  have hid' : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hid
  rw [htop_val]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [h0val]
    exact_mod_cast hlt
  · exact lt_of_lt_of_le (by exact_mod_cast (by omega : d < n + 1)) (hmid i hi0 hid')

/- English proof (translation)
The claim follows from `minpoly.isIntegrallyClosed_eq_field_fractions' K ((isIntegral_iff K L _).mpr ϖ.2)`.
-/
theorem minpoly_eq_map_of_irreducible :
    minpoly K (ϖ : L) = (minpoly 𝒪[K] (ϖ : L)).map (algebraMap 𝒪[K] K) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' K ((isIntegral_iff K L _).mpr ϖ.2)

/- English proof (translation)
Establish `hint : IsIntegral K (ϖ : L)` using `((isIntegral_iff K L _).mpr ϖ.2).tower_top`. Use `IntermediateField.eq_of_le_of_finrank_eq le_top ?_` and prove the remaining obligations. Rewrite using `[IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, minpoly_eq_map_of_irreducible h hϖ, (minpoly.monic ((isIntegral_iff K L _).mpr ϖ.2)).natDegree_map]`. Conclude with `(minpoly_isEisensteinAt_of_irreducible h hϖ).2`.
-/
theorem adjoin_eq_top_of_irreducible : K⟮(ϖ : L)⟯ = ⊤ := by
  have hint : IsIntegral K (ϖ : L) := ((isIntegral_iff K L _).mpr ϖ.2).tower_top
  refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
  rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hint, minpoly_eq_map_of_irreducible h hϖ,
    (minpoly.monic ((isIntegral_iff K L _).mpr ϖ.2)).natDegree_map]
  exact (minpoly_isEisensteinAt_of_irreducible h hϖ).2

end Converse

end GroundTheory.LocalField
