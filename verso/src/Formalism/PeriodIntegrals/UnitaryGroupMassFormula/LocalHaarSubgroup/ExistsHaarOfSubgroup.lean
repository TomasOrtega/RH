import Mathlib

noncomputable section

open ValuativeRel MeasureTheory Topology Polynomial

namespace PI.LocHaarRRW

section General

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Establish `hRo : IsOpen (R : Set V)` using `AddSubgroup.isOpen_of_mem_nhds R h0`. Establish `hRc : IsClosed (R : Set V)` using `R.isClosed_of_isOpen hRo`. Establish `hRk : IsCompact (R : Set V)` using `hC.of_isClosed_subset hRc hRC`. Set `K0 : TopologicalSpace.PositiveCompacts V` to `{ carrier := R, isCompact' := hRk, interior_nonempty' := by rw [hRo.interior_eq]; exact ⟨0, R.zero_mem⟩ }`. Use `⟨Measure.addHaarMeasure K0, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations.

Conclude with `Measure.addHaarMeasure_self`.
-/
theorem exists_haar_of_subgroup [SigmaCompactSpace V] (R : AddSubgroup V)
    (h0 : (R : Set V) ∈ 𝓝 (0 : V)) {C : Set V} (hC : IsCompact C) (hRC : (R : Set V) ⊆ C) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (R : Set V) = 1 := by
  have hRo : IsOpen (R : Set V) := AddSubgroup.isOpen_of_mem_nhds R h0
  have hRc : IsClosed (R : Set V) := R.isClosed_of_isOpen hRo
  have hRk : IsCompact (R : Set V) := hC.of_isClosed_subset hRc hRC
  let K0 : TopologicalSpace.PositiveCompacts V :=
    { carrier := R, isCompact' := hRk,
      interior_nonempty' := by rw [hRo.interior_eq]; exact ⟨0, R.zero_mem⟩ }
  refine ⟨Measure.addHaarMeasure K0, inferInstance, inferInstance, ?_⟩
  exact Measure.addHaarMeasure_self

end General

section Field

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
The claim follows from `isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K])`.
-/
theorem isCompact_integer : IsCompact (𝒪[K] : Set K) :=
  isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K])

/- English proof (translation)
The claim follows from `Valuation.isOpen_integer`.
-/
theorem isOpen_integer' : IsOpen (𝒪[K] : Set K) := Valuation.isOpen_integer

variable {K} in
/- English proof (translation)
Rewrite `hx`, the goal using `[Valuation.mem_integer_iff]`. Rewrite using `[map_inv₀]`. Use `push Not at hx`. Conclude with `inv_le_one_of_one_le₀ hx.le`.
-/
theorem inv_mem_integer {x : K} (hx : x ∉ 𝒪[K]) : x⁻¹ ∈ 𝒪[K] := by
  rw [Valuation.mem_integer_iff] at hx ⊢
  rw [map_inv₀]
  push Not at hx
  exact inv_le_one_of_one_le₀ hx.le

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hϖ0 : (ϖ : K) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Use `⟨⟨fun n => (fun y : K => ((ϖ : K) ^ n)⁻¹ * y) '' (𝒪[K] : Set K), fun n => (isCompact_integer K).image (continuous_const.mul continuous_id), ?_⟩⟩` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Rewrite using `[Set.mem_iUnion]`.

Distinguish the cases in `hx : x ∈ 𝒪[K]`. Conclude with `⟨0, x, hx, by simp⟩`. Establish `hx0 : x ≠ 0` using `by rintro rfl; exact hx (zero_mem _)`. Establish `hxi : x⁻¹ ∈ 𝒪[K]` using `inv_mem_integer hx`. Establish `hne : (⟨x⁻¹, hxi⟩ : 𝒪[K]) ≠ 0`.

Introduce `h`. Apply `hx0` to reduce the goal to its premises. Use `congrArg (fun z : 𝒪[K] => (z : K)) h` as an intermediate fact. Simplify using `using this`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`.

Establish `h1 : x⁻¹ = (u : K) * (ϖ : K) ^ n`. Use `congrArg (fun z : 𝒪[K] => (z : K)) hu` as an intermediate fact. Simplify using `using this`. Use `set y : K := (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) with hy`. Establish `h2 : (u : K) * y = 1`.

Rewrite using `[hy]`. Conclude with `congrArg Subtype.val u.mul_inv`. Establish `hp : ((ϖ : K) ^ n) ≠ 0` using `pow_ne_zero _ hϖ0`. Use `⟨n, y, SetLike.coe_mem _, ?_⟩` and prove the remaining obligations. Use `show ((ϖ : K) ^ n)⁻¹ * y = x`.

Establish `h3 : x⁻¹ * (((ϖ : K) ^ n)⁻¹ * y) = 1`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `inv_eq_of_mul_eq_one_right h3`. Rewrite `h4` using `[inv_inv]`.

Conclude with `h4.symm`.
-/
theorem sigmaCompactSpace_lf : SigmaCompactSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨⟨fun n => (fun y : K => ((ϖ : K) ^ n)⁻¹ * y) '' (𝒪[K] : Set K),
    fun n => (isCompact_integer K).image (continuous_const.mul continuous_id), ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  rw [Set.mem_iUnion]
  by_cases hx : x ∈ 𝒪[K]
  · exact ⟨0, x, hx, by simp⟩
  · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    have hxi : x⁻¹ ∈ 𝒪[K] := inv_mem_integer hx
    have hne : (⟨x⁻¹, hxi⟩ : 𝒪[K]) ≠ 0 := by
      intro h
      apply hx0
      have := congrArg (fun z : 𝒪[K] => (z : K)) h
      simpa using this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    have h1 : x⁻¹ = (u : K) * (ϖ : K) ^ n := by
      have := congrArg (fun z : 𝒪[K] => (z : K)) hu
      simpa using this
    set y : K := (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) with hy
    have h2 : (u : K) * y = 1 := by
      rw [hy]; exact congrArg Subtype.val u.mul_inv
    have hp : ((ϖ : K) ^ n) ≠ 0 := pow_ne_zero _ hϖ0
    refine ⟨n, y, SetLike.coe_mem _, ?_⟩
    show ((ϖ : K) ^ n)⁻¹ * y = x
    have h3 : x⁻¹ * (((ϖ : K) ^ n)⁻¹ * y) = 1 := by
      rw [h1]
      calc (u : K) * (ϖ : K) ^ n * (((ϖ : K) ^ n)⁻¹ * y)
          = ((u : K) * y) * ((ϖ : K) ^ n * ((ϖ : K) ^ n)⁻¹) := by ring
        _ = 1 := by rw [h2, mul_inv_cancel₀ hp, one_mul]
    have h4 := inv_eq_of_mul_eq_one_right h3
    rw [inv_inv] at h4
    exact h4.symm

end Field

section Lin

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {M V : Type*} [AddCommGroup M] [Module K M] [TopologicalSpace M] [IsModuleTopology K M]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]

def homeoOfLin (e : M ≃ₗ[K] V) : M ≃ₜ V :=
  haveI := IsModuleTopology.toContinuousAdd K V
  haveI := IsModuleTopology.toContinuousAdd K M
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

end Lin

section Alg

variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]

/- English proof (translation)
The claim follows from `(Valuation.integer.integers _).mem_of_integral h`.
-/
theorem memO_of_integral {y : K} (h : IsIntegral 𝒪[K] y) : y ∈ 𝒪[K] :=
  (Valuation.integer.integers _).mem_of_integral h

/- English proof (translation)
Establish `: algebraMap 𝒪[K] K ⟨y, h⟩ = y` using `rfl`. Conclude with `this ▸ isIntegral_algebraMap`.
-/
theorem integral_of_memO {y : K} (h : y ∈ 𝒪[K]) : IsIntegral 𝒪[K] y := by
  have : algebraMap 𝒪[K] K ⟨y, h⟩ = y := rfl
  exact this ▸ isIntegral_algebraMap

/- English proof (translation)
The claim follows from `memO_of_integral ((isIntegral_algebraMap_iff (algebraMap K V).injective).1 h)`.
-/
theorem memO_of_integral_V [Nontrivial V] {y : K} (h : IsIntegral 𝒪[K] (algebraMap K V y)) :
    y ∈ 𝒪[K] :=
  memO_of_integral ((isIntegral_algebraMap_iff (algebraMap K V).injective).1 h)

/- English proof (translation)
The claim follows from `(isIntegral_algebraMap_iff (algebraMap K V).injective).2 (integral_of_memO h)`.
-/
theorem integral_V_of_memO [Nontrivial V] {y : K} (h : y ∈ 𝒪[K]) :
    IsIntegral 𝒪[K] (algebraMap K V y) :=
  (isIntegral_algebraMap_iff (algebraMap K V).injective).2 (integral_of_memO h)

/- English proof (translation)
Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Simplify using `only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h`. Conclude with `⟨h, rfl⟩`. It suffices to derive a contradiction.

Apply `hθ` to reduce the goal to its premises. Use `⟨-(t⁻¹ * s), ?_⟩` and prove the remaining obligations. Establish `h1 : t • θ = -(s • (1 : V))` using `eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)`. Establish `h2 : θ = t⁻¹ • (t • θ)` using `by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]`. Rewrite using `[h2, h1, smul_neg, smul_smul, ← neg_smul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem pair_indep [Nontrivial V] {θ : V} (hθ : θ ∉ (algebraMap K V).range) (s t : K)
    (h : s • (1 : V) + t • θ = 0) : s = 0 ∧ t = 0 := by
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at h
    exact ⟨h, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-(t⁻¹ * s), ?_⟩
    have h1 : t • θ = -(s • (1 : V)) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h)
    have h2 : θ = t⁻¹ • (t • θ) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, h1, smul_neg, smul_smul, ← neg_smul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `hpos : 0 < Module.finrank K V` using `by rw [hr]; norm_num`. Use `haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos`. Use `haveI : Module.Finite K V := Module.finite_of_finrank_pos hpos`. Use `set ι := algebraMap K V with hι`. Choose the witnesses or unpack the hypotheses as in `⟨θ0, hθ0⟩ : ∃ θ0 : V, θ0 ∉ ι.range := by`.

Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `htop : (⊤ : Submodule K V) = Submodule.span K {1}`. Use extensionality with `x`. Simplify using `only [Submodule.mem_top, true_iff, Submodule.mem_span_singleton]`.

Take `⟨c, rfl⟩` from `hall x`. Conclude with `⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩`. Establish `h1` using `finrank_span_singleton (K := K) (one_ne_zero : (1 : V) ≠ 0)`. Rewrite `h1` using `[← htop, finrank_top, hr]`. Evaluate the numerical expressions using `at h1`.

Establish `hli : LinearIndependent K ![(1 : V), θ0]` using `LinearIndependent.pair_iff.mpr (pair_indep hθ0)`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])`. Establish `hb0 : b 0 = 1` using `by simp [b]`. Establish `hb1 : b 1 = θ0` using `by simp [b]`. Establish `hb` using `b.sum_repr (θ0 * θ0)`.

Rewrite `hb` using `[Fin.sum_univ_two, hb0, hb1]`. Use `set α := b.repr (θ0 * θ0) 0`. Use `set β := b.repr (θ0 * θ0) 1`. Establish `hsq : θ0 * θ0 = ι α + ι β * θ0`. Rewrite using `[← hb, Algebra.smul_def, Algebra.smul_def, mul_one]`.

Establish `h2 : ι β = 2 * ι (β / 2)`. Rewrite using `[← map_ofNat ι 2, ← map_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `set θ1 := θ0 - ι (β / 2) with hθ1def`.

Establish `hθ1 : θ1 * θ1 = ι (α + (β / 2) ^ 2)`. Rewrite using `[hθ1def, map_add, map_pow]`. Take the linear combination `hsq + θ0 * h2`. Establish `hθ1r : θ1 ∉ ι.range`. Introduce and unpack `⟨c, hc⟩`.

Apply `hθ0` to reduce the goal to its premises. Use `⟨c + β / 2, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hc, hθ1def]`. Expand and normalize the polynomial expressions, which then agree. Establish `hd1 : α + (β / 2) ^ 2 ≠ 0`.

Introduce `h0`. Rewrite `hθ1` using `[h0, map_zero]`. Establish `hn : IsNilpotent θ1` using `⟨2, by rw [pow_two]; exact hθ1⟩`. Apply `hθ1r` to reduce the goal to its premises. Conclude with `⟨0, by rw [map_zero, IsReduced.eq_zero θ1 hn]⟩`.

Use `set d1 := α + (β / 2) ^ 2`. Distinguish the cases in `hdO : d1 ∈ 𝒪[K]`. Conclude with `⟨θ1, d1, hθ1r, hθ1, hd1, hdO⟩`. Use `⟨ι d1⁻¹ * θ1, d1⁻¹, ?_, ?_, inv_ne_zero hd1, inv_mem_integer hdO⟩` and prove the remaining obligations. Introduce and unpack `⟨c, hc⟩`.

Apply `hθ1r` to reduce the goal to its premises. Use `⟨d1 * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd1, map_one, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hθ1, ← map_mul, ← map_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_sq [Module.Free K V] (hr : Module.finrank K V = 2) [IsReduced V] :
    ∃ θ : V, ∃ d : K, θ ∉ (algebraMap K V).range ∧ θ * θ = algebraMap K V d ∧ d ≠ 0 ∧
      d ∈ 𝒪[K] := by
  have hpos : 0 < Module.finrank K V := by rw [hr]; norm_num
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  haveI : Module.Finite K V := Module.finite_of_finrank_pos hpos
  set ι := algebraMap K V with hι
  obtain ⟨θ0, hθ0⟩ : ∃ θ0 : V, θ0 ∉ ι.range := by
    by_contra hall
    push Not at hall
    have htop : (⊤ : Submodule K V) = Submodule.span K {1} := by
      ext x
      simp only [Submodule.mem_top, true_iff, Submodule.mem_span_singleton]
      obtain ⟨c, rfl⟩ := hall x
      exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩
    have h1 := finrank_span_singleton (K := K) (one_ne_zero : (1 : V) ≠ 0)
    rw [← htop, finrank_top, hr] at h1
    norm_num at h1
  have hli : LinearIndependent K ![(1 : V), θ0] :=
    LinearIndependent.pair_iff.mpr (pair_indep hθ0)
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ0 := by simp [b]
  have hb := b.sum_repr (θ0 * θ0)
  rw [Fin.sum_univ_two, hb0, hb1] at hb
  set α := b.repr (θ0 * θ0) 0
  set β := b.repr (θ0 * θ0) 1
  have hsq : θ0 * θ0 = ι α + ι β * θ0 := by
    rw [← hb, Algebra.smul_def, Algebra.smul_def, mul_one]
  have h2 : ι β = 2 * ι (β / 2) := by
    rw [← map_ofNat ι 2, ← map_mul]; congr 1; field_simp
  set θ1 := θ0 - ι (β / 2) with hθ1def
  have hθ1 : θ1 * θ1 = ι (α + (β / 2) ^ 2) := by
    rw [hθ1def, map_add, map_pow]
    linear_combination hsq + θ0 * h2
  have hθ1r : θ1 ∉ ι.range := by
    rintro ⟨c, hc⟩
    apply hθ0
    refine ⟨c + β / 2, ?_⟩
    rw [map_add, hc, hθ1def]; ring
  have hd1 : α + (β / 2) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hθ1
    have hn : IsNilpotent θ1 := ⟨2, by rw [pow_two]; exact hθ1⟩
    apply hθ1r
    exact ⟨0, by rw [map_zero, IsReduced.eq_zero θ1 hn]⟩
  set d1 := α + (β / 2) ^ 2
  by_cases hdO : d1 ∈ 𝒪[K]
  · exact ⟨θ1, d1, hθ1r, hθ1, hd1, hdO⟩
  · refine ⟨ι d1⁻¹ * θ1, d1⁻¹, ?_, ?_, inv_ne_zero hd1, inv_mem_integer hdO⟩
    · rintro ⟨c, hc⟩
      apply hθ1r
      refine ⟨d1 * c, ?_⟩
      rw [map_mul, hc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd1, map_one, one_mul]
    · calc ι d1⁻¹ * θ1 * (ι d1⁻¹ * θ1) = ι d1⁻¹ * ι d1⁻¹ * (θ1 * θ1) := by ring
        _ = ι d1⁻¹ := by
          rw [hθ1, ← map_mul, ← map_mul]; congr 1; field_simp

end Alg

end PI.LocHaarRRW
