import Mathlib
import GroundTheory.LocalFields.LocalFourier
import GroundTheory.LocalFields.LocalFourierTrace
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.NormCorrespondence

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.LocalField.FiltrationCocycleLiftCriterion

namespace WeilRep

open ValuativeRel MeasureTheory Measure Topology Filter Polynomial
open scoped NNReal ENNReal

section Algebraic

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  [Algebra.IsSeparable K E] [hE : Fact (Module.finrank K E = 2)]

/- English proof (translation)
Use `normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩` and prove the remaining obligations. Establish `hint : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Use `set p := (minpoly K x).map (algebraMap K E) with hp`. Establish `hmonic : p.Monic` using `(minpoly.monic hint).map _`. Establish `hroot : p.IsRoot x` using `by simp [p]`.

Establish `hdeg : p.natDegree ≤ 2`. Rewrite using `[hp, Polynomial.natDegree_map]`. Use `minpoly.natDegree_le (A := K) x` as an intermediate fact. Rewrite `this` using `[hE.out]`. Then use the resulting hypothesis. Establish `hq` using `Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot`.

Establish `hq0 : p /ₘ (X - C x) ≠ 0`. Introduce `h0`. Rewrite `hq` using `[h0, mul_zero]`. Conclude with `hmonic.ne_zero hq.symm`. Rewrite using `[← hq]`.

Use `(Splits.X_sub_C x).mul ?_` and prove the remaining obligations. Set `: Invertible (p /ₘ (X - C x)).leadingCoeff` to `invertibleOfNonzero (leadingCoeff_ne_zero.2 hq0)`. Use `Splits.of_natDegree_le_one_of_invertible ?_ this` and prove the remaining obligations. Rewrite using `[Polynomial.natDegree_divByMonic _ (monic_X_sub_C x), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.
-/
theorem normal_of_finrank_eq_two : Normal K E := by
  refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  set p := (minpoly K x).map (algebraMap K E) with hp
  have hmonic : p.Monic := (minpoly.monic hint).map _
  have hroot : p.IsRoot x := by simp [p]
  have hdeg : p.natDegree ≤ 2 := by
    rw [hp, Polynomial.natDegree_map]
    have := minpoly.natDegree_le (A := K) x
    rwa [hE.out] at this
  have hq := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hq0 : p /ₘ (X - C x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hq; exact hmonic.ne_zero hq.symm
  rw [← hq]
  refine (Splits.X_sub_C x).mul ?_
  let : Invertible (p /ₘ (X - C x)).leadingCoeff :=
    invertibleOfNonzero (leadingCoeff_ne_zero.2 hq0)
  refine Splits.of_natDegree_le_one_of_invertible ?_ this
  rw [Polynomial.natDegree_divByMonic _ (monic_X_sub_C x), natDegree_X_sub_C]
  omega

instance isGalois_of_finrank_eq_two : IsGalois K E :=
  haveI := normal_of_finrank_eq_two K E
  ⟨⟩

/- English proof (translation)
Rewrite using `[IsGalois.card_aut_eq_finrank, hE.out]`.
-/
theorem card_gal_eq_two : Nat.card (E ≃ₐ[K] E) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, hE.out]

/- English proof (translation)
Take `⟨y, hy, -⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).1 (card_gal_eq_two K E)`. Conclude with `⟨y, hy⟩`.
-/
theorem exists_ne_one_gal : ∃ σ : E ≃ₐ[K] E, σ ≠ 1 := by
  obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).1 (card_gal_eq_two K E)
  exact ⟨y, hy⟩

def conj : E ≃ₐ[K] E := (exists_ne_one_gal K E).choose

/- English proof (translation)
The claim follows from `(exists_ne_one_gal K E).choose_spec`.
-/
theorem conj_ne_one : conj K E ≠ 1 := (exists_ne_one_gal K E).choose_spec

variable {K E}

/- English proof (translation)
Take `⟨y, -, hy⟩` from `(Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).1 (card_gal_eq_two K E)`. Distinguish the cases in `h : τ = 1`. Conclude with `Or.inl h`. Conclude with `Or.inr ((hy τ h).trans (hy _ (conj_ne_one K E)).symm)`.
-/
theorem eq_one_or_eq_conj (τ : E ≃ₐ[K] E) : τ = 1 ∨ τ = conj K E := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[K] E)).1 (card_gal_eq_two K E)
  by_cases h : τ = 1
  · exact Or.inl h
  · exact Or.inr ((hy τ h).trans (hy _ (conj_ne_one K E)).symm)

/- English proof (translation)
Break down `eq_one_or_eq_conj (conj K E * conj K E) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `conj_ne_one K E` to reduce the goal to its premises. Use `congrArg (fun τ => (conj K E)⁻¹ * τ) h` as an intermediate fact.

Simplify using `using this`. Use the proof step `@[simp]`.
-/
theorem conj_mul_conj : conj K E * conj K E = 1 := by
  rcases eq_one_or_eq_conj (conj K E * conj K E) with h | h
  · exact h
  · exfalso
    apply conj_ne_one K E
    have := congrArg (fun τ => (conj K E)⁻¹ * τ) h
    simpa using this

@[simp]
/- English proof (translation)
Use `congrArg (fun τ : E ≃ₐ[K] E => τ x) (conj_mul_conj (K := K) (E := E))` as an intermediate fact. Simplify using `using this`.
-/
theorem conj_conj (x : E) : conj K E (conj K E x) = x := by
  have := congrArg (fun τ : E ≃ₐ[K] E => τ x) (conj_mul_conj (K := K) (E := E))
  simpa using this

/- English proof (translation)
The claim follows from `(conj K E).injective @[simp]`.
-/
theorem conj_injective : Function.Injective (conj K E) := (conj K E).injective

@[simp]
/- English proof (translation)
The claim follows from `(conj K E).commutes a`.
-/
theorem conj_algebraMap (a : K) : conj K E (algebraMap K E a) = algebraMap K E a :=
  (conj K E).commutes a

/- English proof (translation)
Use `Fintype.prod_eq_mul 1 (conj K E) (conj_ne_one K E).symm fun τ hτ => ?_` and prove the remaining obligations. Break down `eq_one_or_eq_conj τ with h | h` into its components or cases. Conclude with `absurd h hτ.1`. Conclude with `absurd h hτ.2`.
-/
theorem prod_gal (f : (E ≃ₐ[K] E) → E) : ∏ τ : E ≃ₐ[K] E, f τ = f 1 * f (conj K E) := by
  classical
  refine Fintype.prod_eq_mul 1 (conj K E) (conj_ne_one K E).symm fun τ hτ => ?_
  rcases eq_one_or_eq_conj τ with h | h
  · exact absurd h hτ.1
  · exact absurd h hτ.2

/- English proof (translation)
Use `Fintype.sum_eq_add 1 (conj K E) (conj_ne_one K E).symm fun τ hτ => ?_` and prove the remaining obligations. Break down `eq_one_or_eq_conj τ with h | h` into its components or cases. Conclude with `absurd h hτ.1`. Conclude with `absurd h hτ.2`.
-/
theorem sum_gal (f : (E ≃ₐ[K] E) → E) : ∑ τ : E ≃ₐ[K] E, f τ = f 1 + f (conj K E) := by
  classical
  refine Fintype.sum_eq_add 1 (conj K E) (conj_ne_one K E).symm fun τ hτ => ?_
  rcases eq_one_or_eq_conj τ with h | h
  · exact absurd h hτ.1
  · exact absurd h hτ.2

/- English proof (translation)
Rewrite using `[algebraMap_norm_eq_prod, prod_gal]`. Both sides reduce to the same expression.
-/
theorem algebraMap_norm_eq_mul_conj (x : E) :
    algebraMap K E (Algebra.norm K x) = x * conj K E x := by
  rw [algebraMap_norm_eq_prod, prod_gal]
  rfl

/- English proof (translation)
Rewrite using `[trace_eq_sum_automorphisms, sum_gal]`. Both sides reduce to the same expression. Use the proof step `@[simp]`.
-/
theorem algebraMap_trace_eq_add_conj (x : E) :
    algebraMap K E (Algebra.trace K E x) = x + conj K E x := by
  rw [trace_eq_sum_automorphisms, sum_gal]
  rfl

@[simp]
/- English proof (translation)
Apply `(algebraMap K E).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_norm_eq_mul_conj, algebraMap_norm_eq_mul_conj, conj_conj, mul_comm]`. Use the proof step `@[simp]`.
-/
theorem norm_conj (x : E) : Algebra.norm K (conj K E x) = Algebra.norm K x := by
  apply (algebraMap K E).injective
  rw [algebraMap_norm_eq_mul_conj, algebraMap_norm_eq_mul_conj, conj_conj, mul_comm]

@[simp]
/- English proof (translation)
Apply `(algebraMap K E).injective` to reduce the goal to its premises. Rewrite using `[algebraMap_trace_eq_add_conj, algebraMap_trace_eq_add_conj, conj_conj, add_comm]`.
-/
theorem trace_conj (x : E) : Algebra.trace K E (conj K E x) = Algebra.trace K E x := by
  apply (algebraMap K E).injective
  rw [algebraMap_trace_eq_add_conj, algebraMap_trace_eq_add_conj, conj_conj, add_comm]

/- English proof (translation)
Apply `(algebraMap K E).injective` to reduce the goal to its premises. Simplify using `only [map_add, algebraMap_norm_eq_mul_conj, algebraMap_trace_eq_add_conj, map_mul, conj_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_add (x y : E) :
    Algebra.norm K (x + y) =
      Algebra.norm K x + Algebra.norm K y + Algebra.trace K E (x * conj K E y) := by
  apply (algebraMap K E).injective
  simp only [map_add, algebraMap_norm_eq_mul_conj, algebraMap_trace_eq_add_conj, map_mul,
    conj_conj]
  ring

/- English proof (translation)
Rewrite using `[Algebra.norm_algebraMap, hE.out]`.
-/
theorem norm_algebraMap_eq_sq (a : K) : Algebra.norm K (algebraMap K E a) = a ^ 2 := by
  rw [Algebra.norm_algebraMap, hE.out]

end Algebraic

section Local

variable {K E : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra K E] [ValuativeExtension K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]
  [hE : Fact (Module.finrank K E = 2)]

/- English proof (translation)
Establish `h1` using `ord_norm (K := K) (conj K E x)`. Establish `h2` using `ord_norm (K := K) x`. Rewrite `h1` using `[norm_conj]`. Establish `hf : (residueDegree K E : ℤ) ≠ 0` using `by exact_mod_cast (residueDegree_pos K E).ne'`. Conclude with `mul_left_cancel₀ hf (h1.symm.trans h2)`.
-/
theorem ord_conj (x : E) : ord (conj K E x) = ord x := by
  have h1 := ord_norm (K := K) (conj K E x)
  have h2 := ord_norm (K := K) x
  rw [norm_conj] at h1
  have hf : (residueDegree K E : ℤ) ≠ 0 := by exact_mod_cast (residueDegree_pos K E).ne'
  exact mul_left_cancel₀ hf (h1.symm.trans h2)

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `only [map_zero]`. Establish `hx' : conj K E x ≠ 0` using `by simpa using hx`. Rewrite using `[mem_valBall_iff_le_ord hx, mem_valBall_iff_le_ord hx', ord_conj]`.
-/
theorem conj_mem_valBall_iff {n : ℤ} {x : E} : conj K E x ∈ valBall E n ↔ x ∈ valBall E n := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [map_zero]
  have hx' : conj K E x ≠ 0 := by simpa using hx
  rw [mem_valBall_iff_le_ord hx, mem_valBall_iff_le_ord hx', ord_conj]

/- English proof (translation)
Establish `ht : Tendsto (conj K E) (𝓝 0) (𝓝 0)` using `((hasBasis_nhds_zero_valBall (K := E)).tendsto_iff (hasBasis_nhds_zero_valBall (K := E))).2 fun n _ => ⟨n, trivial, fun x hx => conj_mem_valBall_iff.2 hx⟩`. Use `continuous_of_continuousAt_zero (conj K E).toAlgHom.toRingHom ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Conclude with `ht`.
-/
theorem continuous_conj : Continuous (conj K E) := by
  have ht : Tendsto (conj K E) (𝓝 0) (𝓝 0) :=
    ((hasBasis_nhds_zero_valBall (K := E)).tendsto_iff (hasBasis_nhds_zero_valBall (K := E))).2
      fun n _ => ⟨n, trivial, fun x hx => conj_mem_valBall_iff.2 hx⟩
  refine continuous_of_continuousAt_zero (conj K E).toAlgHom.toRingHom ?_
  rw [ContinuousAt, map_zero]
  exact ht

variable (K E) in

def conjContinuousAddEquiv : E ≃ₜ+ E where
  toAddEquiv := (conj K E).toAddEquiv
  continuous_toFun := continuous_conj
  continuous_invFun := by
    have : (conj K E).symm = conj K E := by
      ext x
      apply conj_injective (K := K)
      simp
    show Continuous (conj K E).symm
    rw [this]
    exact continuous_conj

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_conjContinuousAddEquiv : (conjContinuousAddEquiv K E : E → E) = conj K E := rfl

/- English proof (translation)
Use extensionality with `x`. Conclude with `conj_mem_valBall_iff`.
-/
theorem conj_preimage_valBall (n : ℤ) :
    (conj K E) ⁻¹' (valBall E n : Set E) = (valBall E n : Set E) := by
  ext x
  exact conj_mem_valBall_iff

/- English proof (translation)
Establish `hH : (μ.map (conj K E)).IsAddHaarMeasure`. Rewrite using `[← coe_conjContinuousAddEquiv]`. Conclude with `ContinuousAddEquiv.isAddHaarMeasure_map μ _`. Rewrite using `[eq_smul_haarIntegers (μ.map (conj K E)), ← coe_valBall_zero, Measure.map_apply continuous_conj.measurable (measurableSet_valBall 0), conj_preimage_valBall, coe_valBall_zero, ← eq_smul_haarIntegers μ]`.
-/
theorem map_conj_eq [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ.map (conj K E) = μ := by
  have hH : (μ.map (conj K E)).IsAddHaarMeasure := by
    rw [← coe_conjContinuousAddEquiv]
    exact ContinuousAddEquiv.isAddHaarMeasure_map μ _
  rw [eq_smul_haarIntegers (μ.map (conj K E)), ← coe_valBall_zero,
    Measure.map_apply continuous_conj.measurable (measurableSet_valBall 0), conj_preimage_valBall,
    coe_valBall_zero, ← eq_smul_haarIntegers μ]

/- English proof (translation)
The claim follows from `card_residueField_eq_pow_residueDegree K E`.
-/
theorem residueCard_eq_pow : residueCard E = residueCard K ^ residueDegree K E :=
  card_residueField_eq_pow_residueDegree K E

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using `[modulus_zero]`. Establish `hN : Algebra.norm K x ≠ 0` using `(Algebra.norm_ne_zero_iff).2 hx`. Rewrite using `[modulus_of_ne_zero hN, modulus_of_ne_zero hx, ord_norm (K := K) (L := E), residueCard_eq_pow (K := K) (E := E), Nat.cast_pow, ← zpow_natCast (residueCard K : ℝ≥0), ← zpow_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem modulus_norm (x : E) : modulus (Algebra.norm K x) = modulus x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [modulus_zero]
  have hN : Algebra.norm K x ≠ 0 := (Algebra.norm_ne_zero_iff).2 hx
  rw [modulus_of_ne_zero hN, modulus_of_ne_zero hx, ord_norm (K := K) (L := E),
    residueCard_eq_pow (K := K) (E := E), Nat.cast_pow, ← zpow_natCast (residueCard K : ℝ≥0), ← zpow_mul]
  congr 1
  ring

/- English proof (translation)
Rewrite using `[← modulus_norm (K := K), norm_algebraMap_eq_sq, sq, sq, modulus_mul]`.
-/
theorem modulus_algebraMap (a : K) : modulus (algebraMap K E a) = modulus a ^ 2 := by
  rw [← modulus_norm (K := K), norm_algebraMap_eq_sq, sq, sq, modulus_mul]

/- English proof (translation)
Rewrite using `[← modulus_norm (K := K), norm_conj, modulus_norm]`.
-/
theorem modulus_conj (x : E) : modulus (conj K E x) = modulus x := by
  rw [← modulus_norm (K := K), norm_conj, modulus_norm]

instance isMulCommutative_gal : IsMulCommutative (E ≃ₐ[K] E) :=
  ⟨⟨fun a b => by
    rcases eq_one_or_eq_conj a with rfl | rfl <;> rcases eq_one_or_eq_conj b with rfl | rfl <;>
      simp⟩⟩

instance isAbelianGalois_of_finrank_eq_two : IsAbelianGalois K E := ⟨⟩

variable (K E) in

/- English proof (translation)
Set `φ : E →ₐ[K] SeparableClosure K` to `IsSepClosed.lift`. Set `L : IntermediateField K (SeparableClosure K)` to `φ.fieldRange`. Set `e : E ≃ₐ[K] L` to `AlgHom.equivFieldRange φ`. Establish `: FiniteDimensional K L` using `e.toLinearEquiv.finiteDimensional`. Establish `: IsAbelianGalois K L` using `IsAbelianGalois.of_algHom e.symm.toAlgHom`.

Establish `h` using `index_range_normUnits_of_isAbelianGalois (K := K) (Ω := SeparableClosure K) L`. Rewrite `h` using `[← e.toLinearEquiv.finrank_eq, hE.out]`. Establish `hrange : (normUnits K E).range = (normUnits K L).range`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Use `⟨Units.map e.toAlgHom.toRingHom.toMonoidHom x, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[Algebra.norm_eq_of_algEquiv]`. Introduce and unpack `⟨x, rfl⟩`.

Use `⟨Units.map e.symm.toAlgHom.toRingHom.toMonoidHom x, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[Algebra.norm_eq_of_algEquiv]`. Rewrite using `[hrange, h]`.
-/
theorem index_range_normUnits_eq_two : (normUnits K E).range.index = 2 := by
  let φ : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let L : IntermediateField K (SeparableClosure K) := φ.fieldRange
  let e : E ≃ₐ[K] L := AlgHom.equivFieldRange φ
  have : FiniteDimensional K L := e.toLinearEquiv.finiteDimensional
  have : IsAbelianGalois K L := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have h := index_range_normUnits_of_isAbelianGalois (K := K) (Ω := SeparableClosure K) L
  rw [← e.toLinearEquiv.finrank_eq, hE.out] at h
  have hrange : (normUnits K E).range = (normUnits K L).range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Units.map e.toAlgHom.toRingHom.toMonoidHom x, ?_⟩
      ext
      simp [Algebra.norm_eq_of_algEquiv]
    · rintro ⟨x, rfl⟩
      refine ⟨Units.map e.symm.toAlgHom.toRingHom.toMonoidHom x, ?_⟩
      ext
      simp [Algebra.norm_eq_of_algEquiv]
  rw [hrange, h]

instance finiteIndex_range_normUnits : (normUnits K E).range.FiniteIndex :=
  ⟨by rw [index_range_normUnits_eq_two K E]; norm_num⟩

/- English proof (translation)
The claim follows from `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_range_normUnits K E)`.
-/
theorem isOpen_range_normUnits : IsOpen ((normUnits K E).range : Set Kˣ) :=
  Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_range_normUnits K E)

variable (K E) in

def quadChar : Kˣ →* ℂˣ where
  toFun t := by classical exact if t ∈ (normUnits K E).range then 1 else -1
  map_one' := by simp [one_mem]
  map_mul' a b := by
    classical
    have h := Subgroup.mul_mem_iff_of_index_two (index_range_normUnits_eq_two K E) (a := a) (b := b)
    by_cases ha : a ∈ (normUnits K E).range <;> by_cases hb : b ∈ (normUnits K E).range <;>
      simp [ha, hb, h]

/- English proof (translation)
Simplify using `[quadChar, ht]`.
-/
theorem quadChar_apply_of_mem {t : Kˣ} (ht : t ∈ (normUnits K E).range) : quadChar K E t = 1 := by
  simp [quadChar, ht]

/- English proof (translation)
Simplify using `[quadChar, ht]`.
-/
theorem quadChar_apply_of_notMem {t : Kˣ} (ht : t ∉ (normUnits K E).range) :
    quadChar K E t = -1 := by
  simp [quadChar, ht]

/- English proof (translation)
Use `⟨fun h => ?_, quadChar_apply_of_mem⟩` and prove the remaining obligations. Assume the negation of the conclusion as `ht`. Rewrite `h` using `[quadChar_apply_of_notMem ht]`. Use `congrArg (fun u : ℂˣ => (u : ℂ)) h` as an intermediate fact. Evaluate the numerical expressions using `at this`.

Use the proof step `@[simp]`.
-/
theorem quadChar_eq_one_iff {t : Kˣ} : quadChar K E t = 1 ↔ t ∈ (normUnits K E).range := by
  refine ⟨fun h => ?_, quadChar_apply_of_mem⟩
  by_contra ht
  rw [quadChar_apply_of_notMem ht] at h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

@[simp]
/- English proof (translation)
The claim follows from `quadChar_apply_of_mem ⟨x, rfl⟩`.
-/
theorem quadChar_normUnits (x : Eˣ) : quadChar K E (normUnits K E x) = 1 :=
  quadChar_apply_of_mem ⟨x, rfl⟩

/- English proof (translation)
Distinguish the cases in `ht : t ∈ (normUnits K E).range`. Simplify using `[quadChar_apply_of_mem ht]`. Simplify using `[quadChar_apply_of_notMem ht]`.
-/
theorem quadChar_sq (t : Kˣ) : quadChar K E t ^ 2 = 1 := by
  classical
  by_cases ht : t ∈ (normUnits K E).range
  · simp [quadChar_apply_of_mem ht]
  · simp [quadChar_apply_of_notMem ht]

/- English proof (translation)
Rewrite using `[map_mul, ← sq, quadChar_sq]`.
-/
theorem quadChar_mul_self (t : Kˣ) : quadChar K E (t * t) = 1 := by
  rw [map_mul, ← sq, quadChar_sq]

/- English proof (translation)
Introduce `h`. Establish `htop : (normUnits K E).range = ⊤`. Use `eq_top_iff.2 fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← quadChar_eq_one_iff, h, MonoidHom.one_apply]`. Use `index_range_normUnits_eq_two K E` as an intermediate fact.

Rewrite `this` using `[htop, Subgroup.index_top]`. Evaluate the numerical expressions using `at this`.
-/
theorem quadChar_ne_one : quadChar K E ≠ 1 := by
  intro h
  have htop : (normUnits K E).range = ⊤ := by
    refine eq_top_iff.2 fun t _ => ?_
    rw [← quadChar_eq_one_iff, h, MonoidHom.one_apply]
  have := index_range_normUnits_eq_two K E
  rw [htop, Subgroup.index_top] at this
  norm_num at this

/- English proof (translation)
Establish `: (quadChar K E).ker = (normUnits K E).range`. Use extensionality with `t`. Conclude with `quadChar_eq_one_iff`. Rewrite using `[this]`. Conclude with `isOpen_range_normUnits`.
-/
theorem isOpen_ker_quadChar : IsOpen ((quadChar K E).ker : Set Kˣ) := by
  have : (quadChar K E).ker = (normUnits K E).range := by
    ext t
    exact quadChar_eq_one_iff
  rw [this]
  exact isOpen_range_normUnits

end Local

end WeilRep

end GroundTheory.LocalField.FiltrationCocycleLiftCriterion
