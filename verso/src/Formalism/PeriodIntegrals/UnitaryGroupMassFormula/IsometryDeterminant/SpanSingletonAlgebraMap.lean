import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDeterminant.AlgebraMapMemCI

noncomputable section

namespace PI.IsoDetW.Loc

open PI.IsoDetDefs IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

local notation "FI" => FractionalIdeal (nonZeroDivisors R) K

abbrev mulR (a : K) : K →ₗ[R] K := (LinearMap.mulLeft K a).restrictScalars R

/- English proof (translation)
Introduce `x y h` and use `mul_left_cancel₀ ha h`.
-/
theorem mulR_injective {a : K} (ha : a ≠ 0) : Function.Injective (mulR (R := R) a) :=
  fun x y h => mul_left_cancel₀ ha h

/- English proof (translation)
The claim follows from `sat_of_linear p (LinearMap.mulLeft K a) s y hs hy`.
-/
theorem mulR_sat (p : Ideal R) [p.IsPrime] (a : K) (s : R) (y : K) (hs : s ∈ p.primeCompl)
    (hy : s • y ∈ LinearMap.range (mulR (R := R) a)) : y ∈ LinearMap.range (mulR (R := R) a) :=
  sat_of_linear p (LinearMap.mulLeft K a) s y hs hy

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, hz, rfl⟩`.
-/
theorem map_mulR (a : K) (I : FI) :
    (I : Submodule R K).map (mulR a) = ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K) := by
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
    LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩

/- English proof (translation)
Rewrite using `[← map_mulR, ← map_mulR]`. Conclude with `lidx_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _`.
-/
theorem lidx_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    lidx P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K)
      ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K) =
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) := by
  rw [← map_mulR, ← map_mulR]
  exact lidx_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _

/- English proof (translation)
Rewrite using `[← map_mulR, ← map_mulR]`. Conclude with `relativeLength_localized_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _`.
-/
theorem rlen_mulR (P : HeightOneSpectrum R) {a : K} (ha : a ≠ 0) (I J : FI) :
    relative₂ (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * I : FI) : Submodule R K))
      (localization₂ P.asIdeal ((FractionalIdeal.spanSingleton _ a * J : FI) : Submodule R K)) =
    relative₂ (localization₂ P.asIdeal (I : Submodule R K)) (localization₂ P.asIdeal (J : Submodule R K)) := by
  rw [← map_mulR, ← map_mulR]
  exact relativeLength_localized_map P.asIdeal (mulR a) (mulR_injective ha) (mulR_sat P.asIdeal a) _ _

/- English proof (translation)
Use `relativeLength_localized_coeIdeal (K := K) P hJ` as an intermediate fact. Rewrite using `[FractionalIdeal.count_coe K P hJ, Int.toNat_natCast]`. Conclude with `this`.
-/
theorem rlen_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    relative₂ (localization₂ P.asIdeal ((J : FI) : Submodule R K)) (localization₂ P.asIdeal (1 : Submodule R K)) =
      ((FractionalIdeal.count K P (J : FI)).toNat : ℕ∞) := by
  have := relativeLength_localized_coeIdeal (K := K) P hJ
  rw [FractionalIdeal.count_coe K P hJ, Int.toNat_natCast]
  exact this

/- English proof (translation)
Take `⟨a, J, ha, hIJ⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul I`. Establish `ha' : algebraMap R K a ≠ 0`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `ha`. Use `⟨a, ha, J, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Apply `hI` to reduce the goal to its premises. Rewrite using `[hIJ]`. Simplify using the standard rewrite rules. Rewrite using `[hIJ, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha', FractionalIdeal.spanSingleton_one, one_mul]`.
-/
theorem exists_integral (I : FI) (hI : I ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∃ J : Ideal R, J ≠ 0 ∧
      FractionalIdeal.spanSingleton _ (algebraMap R K a) * I = (J : FI) := by
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  refine ⟨a, ha, J, ?_, ?_⟩
  · rintro rfl
    apply hI
    rw [hIJ]; simp
  · rw [hIJ, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha',
      FractionalIdeal.spanSingleton_one, one_mul]

/- English proof (translation)
The claim follows from `(FractionalIdeal.coe_le_coe.mpr h).trans_eq FractionalIdeal.coe_one`.
-/
theorem coe_le_one {I : FI} (h : I ≤ 1) : (I : Submodule R K) ≤ 1 :=
  (FractionalIdeal.coe_le_coe.mpr h).trans_eq FractionalIdeal.coe_one

/- English proof (translation)
Establish `hX : X ≠ 0` using `by rintro rfl; exact hD (le_bot_iff.mp hDX)`. Take `⟨a, ha, J, hJ, hXJ⟩` from `exists_integral X hX`. Establish `ha' : algebraMap R K a ≠ 0`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `ha`.

Rewrite using `[← rlen_mulR P ha' D X, hXJ]`. Establish `hle : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ (J : FI)` using `hXJ ▸ (by gcongr)`. Establish `hle1 : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ 1` using `hle.trans (FractionalIdeal.coeIdeal_le_one)`. Take `⟨J', hJ'⟩` from `FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1`. Establish `hJ'0 : J' ≠ 0`.

Introduce and unpack `rfl`. Establish `: FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * D = 0`. Rewrite using `[← hJ']`. Simplify using the standard rewrite rules. Break down `mul_eq_zero.mp this with h | h` into its components or cases.

Conclude with `ha' (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)`. Conclude with `hD h`. Rewrite using `[← hJ']`. Establish `h1` using `rlen_mono (localization_mono P.asIdeal (le_refl ((J' : FI) : Submodule R K))) (localization_mono P.asIdeal (show ((J' : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) from by rw [hJ']; exact FractionalIdeal.coe_le_coe.mpr hle)) (localization_mono P.asIdeal (coe_le_one Fraction …`. Rewrite `h1` using `[rlen_coeIdeal P hJ'0]`.

Conclude with `ne_top_of_le_ne_top (ENat.coe_ne_top _) h1`.
-/
theorem rlen_ne_top (P : HeightOneSpectrum R) {D X : FI} (hD : D ≠ 0) (hDX : D ≤ X) :
    relative₂ (localization₂ P.asIdeal (D : Submodule R K)) (localization₂ P.asIdeal (X : Submodule R K)) ≠ ⊤ := by
  have hX : X ≠ 0 := by rintro rfl; exact hD (le_bot_iff.mp hDX)
  obtain ⟨a, ha, J, hJ, hXJ⟩ := exists_integral X hX
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  rw [← rlen_mulR P ha' D X, hXJ]
  have hle : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ (J : FI) :=
    hXJ ▸ (by gcongr)
  have hle1 : FractionalIdeal.spanSingleton _ (algebraMap R K a) * D ≤ 1 :=
    hle.trans (FractionalIdeal.coeIdeal_le_one)
  obtain ⟨J', hJ'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  have hJ'0 : J' ≠ 0 := by
    rintro rfl
    have : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * D = 0 := by
      rw [← hJ']; simp
    rcases mul_eq_zero.mp this with h | h
    · exact ha' (FractionalIdeal.spanSingleton_eq_zero_iff.mp h)
    · exact hD h
  rw [← hJ']
  have h1 := rlen_mono (localization_mono P.asIdeal (le_refl ((J' : FI) : Submodule R K)))
    (localization_mono P.asIdeal (show ((J' : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) from
      by rw [hJ']; exact FractionalIdeal.coe_le_coe.mpr hle))
    (localization_mono P.asIdeal (coe_le_one FractionalIdeal.coeIdeal_le_one))
  rw [rlen_coeIdeal P hJ'0] at h1
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) h1

/- English proof (translation)
Establish `hle : ((J : FI) : Submodule R K) ≤ 1` using `coe_le_one FractionalIdeal.coeIdeal_le_one`. Establish `hne : (J : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hJ`. Rewrite using `[lidx_eq_of_le P.asIdeal (D := ((J : FI) : Submodule R K)) (le_inf hle le_rfl) (by rw [rlen_coeIdeal P hJ]; exact ENat.coe_ne_top _) (by rw [rlen_self]; exact ENat.zero_ne_top), rlen_coeIdeal P hJ, rlen_self]`. Simplify using `only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]`. Conclude with `Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K P J)`.
-/
theorem lidx_one_coeIdeal (P : HeightOneSpectrum R) {J : Ideal R} (hJ : J ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) ((J : FI) : Submodule R K) = FractionalIdeal.count K P (J : FI) := by
  have hle : ((J : FI) : Submodule R K) ≤ 1 := coe_le_one FractionalIdeal.coeIdeal_le_one
  have hne : (J : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  rw [lidx_eq_of_le P.asIdeal (D := ((J : FI) : Submodule R K)) (le_inf hle le_rfl)
    (by rw [rlen_coeIdeal P hJ]; exact ENat.coe_ne_top _) (by rw [rlen_self]; exact ENat.zero_ne_top),
    rlen_coeIdeal P hJ, rlen_self]
  simp only [ENat.toNat_coe, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact Int.toNat_of_nonneg (FractionalIdeal.count_coe_nonneg K P J)

/- English proof (translation)
The claim follows from `(FractionalIdeal.coeIdeal_span_singleton a).symm`.
-/
theorem spanSingleton_algebraMap (a : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) = ((Ideal.span {a} : Ideal R) : FI) :=
  (FractionalIdeal.coeIdeal_span_singleton a).symm

/- English proof (translation)
Take `⟨a, ha, J, hJ, hIJ⟩` from `exists_integral I hI`. Establish `ha' : algebraMap R K a ≠ 0`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `ha`. Establish `hsa : Ideal.span {a} ≠ (0 : Ideal R)`.

Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha`. Establish `hsaJ : Ideal.span {a} * J ≠ 0` using `mul_ne_zero hsa hJ`. Rewrite using `[← FractionalIdeal.coe_one, ← lidx_mulR P ha' 1 I, mul_one, hIJ, spanSingleton_algebraMap]`. Establish `hD1 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((Ideal.span {a} : Ideal R) : FI)`.

Apply `FractionalIdeal.coe_le_coe.mpr` to reduce the goal to its premises. Rewrite using `[FractionalIdeal.coeIdeal_mul]`. Conclude with `mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one`. Establish `hD2 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K)`. Apply `FractionalIdeal.coe_le_coe.mpr` to reduce the goal to its premises.

Rewrite using `[FractionalIdeal.coeIdeal_mul]`. Conclude with `mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one`. Establish `hD3 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((1 : FI) : Submodule R K)` using `FractionalIdeal.coe_le_coe.mpr FractionalIdeal.coeIdeal_le_one`. Establish `hDne : ((Ideal.span {a} * J : Ideal R) : FI) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr hsaJ`. Rewrite using `[lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K)) hD1 hD3 hD2 (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD1)) (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD3)) (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD2))]`.

Rewrite using `[lidx_antisymm, FractionalIdeal.coe_one, lidx_one_coeIdeal P hsa, lidx_one_coeIdeal P hJ]`. Establish `hc` using `congrArg (FractionalIdeal.count K P) hIJ`. Rewrite `hc` using `[FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha') hI, spanSingleton_algebraMap]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lidx_one_left (P : HeightOneSpectrum R) {I : FI} (hI : I ≠ 0) :
    lidx P.asIdeal (1 : Submodule R K) (I : Submodule R K) = FractionalIdeal.count K P I := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  have hsa : Ideal.span {a} ≠ (0 : Ideal R) := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hsaJ : Ideal.span {a} * J ≠ 0 := mul_ne_zero hsa hJ
  rw [← FractionalIdeal.coe_one, ← lidx_mulR P ha' 1 I, mul_one, hIJ, spanSingleton_algebraMap]

  have hD1 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((Ideal.span {a} : Ideal R) : FI) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
  have hD2 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((J : FI) : Submodule R K) := by
    apply FractionalIdeal.coe_le_coe.mpr
    rw [FractionalIdeal.coeIdeal_mul]
    exact mul_le_of_le_one_left' FractionalIdeal.coeIdeal_le_one
  have hD3 : (((Ideal.span {a} * J : Ideal R) : FI) : Submodule R K) ≤ ((1 : FI) : Submodule R K) :=
    FractionalIdeal.coe_le_coe.mpr FractionalIdeal.coeIdeal_le_one
  have hDne : ((Ideal.span {a} * J : Ideal R) : FI) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hsaJ
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K)) hD1 hD3 hD2
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD1))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD3))
    (rlen_ne_top P hDne (FractionalIdeal.coe_le_coe.mp hD2))]
  rw [lidx_antisymm, FractionalIdeal.coe_one, lidx_one_coeIdeal P hsa, lidx_one_coeIdeal P hJ]
  have hc := congrArg (FractionalIdeal.count K P) hIJ
  rw [FractionalIdeal.count_mul K P (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha') hI,
    spanSingleton_algebraMap] at hc
  linarith

/- English proof (translation)
Take `⟨a, ha, J, hJ, hIJ⟩` from `exists_integral I hI`. Establish `ha' : algebraMap R K a ≠ 0`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `ha`. Take `⟨j, hjJ, hj0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hJ`.

Use `⟨a * j, mul_ne_zero ha hj0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem]`. Establish `: algebraMap R K j ∈ FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I`. Rewrite using `[hIJ]`. Conclude with `(FractionalIdeal.mem_coeIdeal _).mpr ⟨j, hjJ, rfl⟩`.

Take `⟨x, hx, hxe⟩` from `(FractionalIdeal.mem_singleton_mul).mp this`. Establish `e : algebraMap R K (a * j) = (a * a) • x`. Rewrite using `[map_mul, hxe, Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `FractionalIdeal.mem_coe.mp (Submodule.smul_mem _ _ (FractionalIdeal.mem_coe.mpr hx))`. Introduce `x hx`. Establish `hj' : algebraMap R K j ≠ 0`. Rewrite using `[ne_eq, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hj0`.

Establish `hax : algebraMap R K a * x ∈ (J : FI)`. Rewrite using `[← hIJ]`. Conclude with `FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩`. Take `⟨z, -, hze⟩` from `(FractionalIdeal.mem_coeIdeal _).mp hax`. Rewrite using `[FractionalIdeal.mem_spanSingleton]`.

Use `⟨j * z, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_mul, hze]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_sandwich (I : FI) (hI : I ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ FractionalIdeal.spanSingleton _ (algebraMap R K r) ≤ I ∧
      I ≤ FractionalIdeal.spanSingleton _ (algebraMap R K r)⁻¹ := by
  obtain ⟨a, ha, J, hJ, hIJ⟩ := exists_integral I hI
  have ha' : algebraMap R K a ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact ha
  obtain ⟨j, hjJ, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  refine ⟨a * j, mul_ne_zero ha hj0, ?_, ?_⟩
  ·
    rw [FractionalIdeal.spanSingleton_le_iff_mem]
    have : algebraMap R K j ∈ FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a) * I := by
      rw [hIJ]; exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨j, hjJ, rfl⟩
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_singleton_mul).mp this
    have e : algebraMap R K (a * j) = (a * a) • x := by
      rw [map_mul, hxe, Algebra.smul_def, map_mul]; ring
    rw [e]
    exact FractionalIdeal.mem_coe.mp (Submodule.smul_mem _ _ (FractionalIdeal.mem_coe.mpr hx))
  · intro x hx
    have hj' : algebraMap R K j ≠ 0 := by
      rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]; exact hj0
    have hax : algebraMap R K a * x ∈ (J : FI) := by
      rw [← hIJ]; exact FractionalIdeal.mem_singleton_mul.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, -, hze⟩ := (FractionalIdeal.mem_coeIdeal _).mp hax
    rw [FractionalIdeal.mem_spanSingleton]
    refine ⟨j * z, ?_⟩
    rw [Algebra.smul_def, map_mul, map_mul, hze]
    field_simp

/- English proof (translation)
Rewrite using `[FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]`. Conclude with `⟨y, by rw [Algebra.smul_def, map_mul, mul_comm]⟩`.
-/
theorem spanSingleton_mul_le (x y : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (x * y)) ≤
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) := by
  rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
  exact ⟨y, by rw [Algebra.smul_def, map_mul, mul_comm]⟩

/- English proof (translation)
Rewrite using `[spanSingleton_algebraMap]`. Conclude with `FractionalIdeal.coeIdeal_le_one`.
-/
theorem spanSingleton_le_one (x : R) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K x) ≤ 1 := by
  rw [spanSingleton_algebraMap]; exact FractionalIdeal.coeIdeal_le_one

/- English proof (translation)
Take `⟨a, ha, haI, -⟩` from `exists_sandwich I hI`. Take `⟨b, hb, hbJ, -⟩` from `exists_sandwich J hJ`. Use `set D := FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (a * b)) with hD`. Establish `hD0 : D ≠ 0`. Rewrite using `[hD, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]`.

Conclude with `mul_ne_zero ha hb`. Establish `hDI : D ≤ I` using `(spanSingleton_mul_le a b).trans haI`. Establish `hDJ : D ≤ J` using `(by rw [hD, mul_comm]; exact spanSingleton_mul_le b a : D ≤ _).trans hbJ`. Establish `hD1 : D ≤ 1` using `spanSingleton_le_one _`. Rewrite using `[lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K)) (FractionalIdeal.coe_le_coe.mpr hDI) (FractionalIdeal.coe_le_coe.mpr hD1) (FractionalIdeal.coe_le_coe.mpr hDJ) (rlen_ne_top P hD0 hDI) (rlen_ne_top P hD0 hD1) (rlen_ne_top P hD0 hDJ)]`.

Rewrite using `[lidx_antisymm P.asIdeal _ ((1 : FI) : Submodule R K), FractionalIdeal.coe_one, lidx_one_left P hI, lidx_one_left P hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lidx_frac (P : HeightOneSpectrum R) {I J : FI} (hI : I ≠ 0) (hJ : J ≠ 0) :
    lidx P.asIdeal (I : Submodule R K) (J : Submodule R K) =
      FractionalIdeal.count K P J - FractionalIdeal.count K P I := by
  obtain ⟨a, ha, haI, -⟩ := exists_sandwich I hI
  obtain ⟨b, hb, hbJ, -⟩ := exists_sandwich J hJ
  set D := FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K (a * b)) with hD
  have hD0 : D ≠ 0 := by
    rw [hD, ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff]
    exact mul_ne_zero ha hb
  have hDI : D ≤ I := (spanSingleton_mul_le a b).trans haI
  have hDJ : D ≤ J := (by rw [hD, mul_comm]; exact spanSingleton_mul_le b a : D ≤ _).trans hbJ
  have hD1 : D ≤ 1 := spanSingleton_le_one _
  rw [lidx_cocycle P.asIdeal (B := ((1 : FI) : Submodule R K))
    (FractionalIdeal.coe_le_coe.mpr hDI) (FractionalIdeal.coe_le_coe.mpr hD1)
    (FractionalIdeal.coe_le_coe.mpr hDJ)
    (rlen_ne_top P hD0 hDI) (rlen_ne_top P hD0 hD1) (rlen_ne_top P hD0 hDJ)]
  rw [lidx_antisymm P.asIdeal _ ((1 : FI) : Submodule R K), FractionalIdeal.coe_one,
    lidx_one_left P hI, lidx_one_left P hJ]
  ring

end PI.IsoDetW.Loc
