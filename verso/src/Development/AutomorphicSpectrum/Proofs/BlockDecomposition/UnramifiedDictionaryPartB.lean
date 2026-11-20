import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import GroundTheory.LocalFields.Integers

open ValuativeRel PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Unram

/- English proof (translation)
Proceed by induction on `m, hm using Nat.le_induction with`. Consider the case `base => simpa using h1`. Consider the case `succ m hm ih`. Introduce `x`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.mp (hpow x)`.

Establish `e1 : τ (x ^ q - x) = τ z * π` using `by rw [← hz, map_mul, hτπ]`. Rewrite `e1` using `[map_sub, map_pow]`. Establish `hsum : ∑ i ∈ Finset.range q, (τ x) ^ i * x ^ (q - 1 - i) ∈ Ideal.span {π}`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sum]`. Establish `hab : Ideal.Quotient.mk (Ideal.span {π}) (τ x) = Ideal.Quotient.mk (Ideal.span {π}) x` using `Ideal.Quotient.eq.mpr (h1 x)`.

Simplify using `only [map_mul, map_pow, hab]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => by`. Rewrite using `[← pow_add, show i + (q - 1 - i) = q - 1 by have := Finset.mem_range.mp hi; omega]),`. Use the proof step `Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Rewrite using `[show ((q : ℕ) : O ⧸ Ideal.span {π}) = Ideal.Quotient.mk (Ideal.span {π}) (q : O) by simp, Ideal.Quotient.eq_zero_iff_mem.mpr hq, zero_mul]`.

Establish `hA : (τ x) ^ q - x ^ q ∈ (Ideal.span {π}) ^ (m + 1)`. Rewrite using `[← geom_sum₂_mul, pow_succ']`. Conclude with `Ideal.mul_mem_mul hsum (ih x)`. Establish `hB : (τ z - z) * π ∈ (Ideal.span {π}) ^ (m + 1)`. Rewrite using `[pow_succ]`.

Conclude with `Ideal.mul_mem_mul (ih z) (Ideal.mem_span_singleton_self π)`. Establish `e2 : τ x - x = ((τ x) ^ q - x ^ q) - (τ z - z) * π`. Take the linear combination `(-1 : O) * e1 - hz`. Rewrite using `[e2]`. Conclude with `Ideal.sub_mem _ hA hB`.
-/
theorem sub_mem_span_pow {O : Type*} [CommRing O] (τ : O →+* O) (π : O) (q : ℕ)
    (hτπ : τ π = π) (hq : (q : O) ∈ Ideal.span {π})
    (hpow : ∀ x : O, x ^ q - x ∈ Ideal.span {π})
    (h1 : ∀ x : O, τ x - x ∈ Ideal.span {π}) (m : ℕ) (hm : 1 ≤ m) :
    ∀ x : O, τ x - x ∈ (Ideal.span {π}) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => simpa using h1
  | succ m hm ih =>
    intro x
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hpow x)
    have e1 : τ (x ^ q - x) = τ z * π := by rw [← hz, map_mul, hτπ]
    rw [map_sub, map_pow] at e1
    have hsum : ∑ i ∈ Finset.range q, (τ x) ^ i * x ^ (q - 1 - i) ∈ Ideal.span {π} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      have hab : Ideal.Quotient.mk (Ideal.span {π}) (τ x) = Ideal.Quotient.mk (Ideal.span {π}) x :=
        Ideal.Quotient.eq.mpr (h1 x)
      simp only [map_mul, map_pow, hab]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [← pow_add, show i + (q - 1 - i) = q - 1 by have := Finset.mem_range.mp hi; omega]),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show ((q : ℕ) : O ⧸ Ideal.span {π}) = Ideal.Quotient.mk (Ideal.span {π}) (q : O) by simp,
        Ideal.Quotient.eq_zero_iff_mem.mpr hq, zero_mul]
    have hA : (τ x) ^ q - x ^ q ∈ (Ideal.span {π}) ^ (m + 1) := by
      rw [← geom_sum₂_mul, pow_succ']
      exact Ideal.mul_mem_mul hsum (ih x)
    have hB : (τ z - z) * π ∈ (Ideal.span {π}) ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih z) (Ideal.mem_span_singleton_self π)
    have e2 : τ x - x = ((τ x) ^ q - x ^ q) - (τ z - z) * π := by
      linear_combination (-1 : O) * e1 - hz
    rw [e2]
    exact Ideal.sub_mem _ hA hB

section Local

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/- English proof (translation)
Establish `hle : valuation E (x : E) ≤ 1` using `x.2`. Use `lt_of_le_of_ne hle ?_` and prove the remaining obligations. Introduce `heq`. Establish `hunit : IsUnit x` using `(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mpr heq`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp hx) hunit`.
-/
theorem lt_one_of_mem_maximal (x : 𝒪[E]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[E]) :
    valuation E (x : E) < 1 := by
  have hle : valuation E (x : E) ≤ 1 := x.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hunit : IsUnit x := (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mpr heq
  exact ((IsLocalRing.mem_maximalIdeal _).mp hx) hunit

/- English proof (translation)
Use `haveI : Fintype (IsLocalRing.ResidueField 𝒪[E]) := Fintype.ofFinite _`. Use `⟨Fintype.card (IsLocalRing.ResidueField 𝒪[E]), ?_, ?_⟩` and prove the remaining obligations. Establish `hmem : ((Fintype.card (IsLocalRing.ResidueField 𝒪[E]) : ℕ) : 𝒪[E]) ∈ IsLocalRing.maximalIdeal 𝒪[E]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_natCast]`. Conclude with `FiniteField.cast_card_eq_zero _`.

Use `lt_one_of_mem_maximal E _ hmem` as an intermediate fact. Simplify using `using this`. Introduce `x`. Apply `lt_one_of_mem_maximal E` to reduce the goal to its premises. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, FiniteField.pow_card, sub_self]`.
-/
theorem residue_card_facts : ∃ q : ℕ, valuation E (q : E) < 1 ∧
    ∀ x : 𝒪[E], valuation E (((x ^ q - x : 𝒪[E])) : E) < 1 := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField 𝒪[E]) := Fintype.ofFinite _
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[E]), ?_, ?_⟩
  · have hmem : ((Fintype.card (IsLocalRing.ResidueField 𝒪[E]) : ℕ) : 𝒪[E]) ∈ IsLocalRing.maximalIdeal 𝒪[E] := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact FiniteField.cast_card_eq_zero _
    have := lt_one_of_mem_maximal E _ hmem
    simpa using this
  · intro x
    apply lt_one_of_mem_maximal E
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, FiniteField.pow_card, sub_self]

end Local

section Ext

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

/- English proof (translation)
Use `haveI := GroundTheory.LocalField.free_integer k E`. Use `haveI := GroundTheory.LocalField.finite_integer k E`. Use `haveI := GroundTheory.LocalField.isIntegralClosure k E`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid 𝒪[E] (nonZeroDivisors 𝒪[k])) E := IsIntegralClosure.isLocalization 𝒪[k] k E 𝒪[E]`. Set `bO` to `Module.finBasisOfFinrankEq 𝒪[k] 𝒪[E] (GroundTheory.LocalField.finrank_integer k E)`.

Set `b` to `bO.localizationLocalization k (nonZeroDivisors 𝒪[k]) E`. Establish `hb : ∀ i, b i = ((bO i : 𝒪[E]) : E)` using `fun i => Module.Basis.localizationLocalization_apply _ _ _ _ _`. Use `⟨b, fun i => by rw [hb]; exact (bO i).2, fun x => ⟨fun hx i => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `hx' : x = algebraMap 𝒪[E] E ⟨x, hx⟩` using `rfl`. Rewrite using `[hx', Module.Basis.localizationLocalization_repr_algebraMap]`.

Conclude with `(bO.repr ⟨x, hx⟩ i).2`. Rewrite using `[← b.sum_repr x]`. Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hb]`. Conclude with `Subring.mul_mem _ ((hint _).mpr (h i)) (bO i).2`.
-/
theorem integral_basis
    (hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k) :
    ∃ b : Module.Basis (Fin (Module.finrank k E)) k E, (∀ i, b i ∈ intO E) ∧
      ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k := by
  haveI := GroundTheory.LocalField.free_integer k E
  haveI := GroundTheory.LocalField.finite_integer k E
  haveI := GroundTheory.LocalField.isIntegralClosure k E
  haveI : IsLocalization (Algebra.algebraMapSubmonoid 𝒪[E] (nonZeroDivisors 𝒪[k])) E :=
    IsIntegralClosure.isLocalization 𝒪[k] k E 𝒪[E]
  let bO := Module.finBasisOfFinrankEq 𝒪[k] 𝒪[E] (GroundTheory.LocalField.finrank_integer k E)
  let b := bO.localizationLocalization k (nonZeroDivisors 𝒪[k]) E
  have hb : ∀ i, b i = ((bO i : 𝒪[E]) : E) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ _
  refine ⟨b, fun i => by rw [hb]; exact (bO i).2, fun x => ⟨fun hx i => ?_, fun h => ?_⟩⟩
  · have hx' : x = algebraMap 𝒪[E] E ⟨x, hx⟩ := rfl
    rw [hx', Module.Basis.localizationLocalization_repr_algebraMap]
    exact (bO.repr ⟨x, hx⟩ i).2
  · rw [← b.sum_repr x]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, hb]
    exact Subring.mul_mem _ ((hint _).mpr (h i)) (bO i).2

variable {k E}

/- English proof (translation)
Rewrite using `[← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]`.
-/
theorem val_le_iff (a b : k) :
    valuation k a ≤ valuation k b ↔
      valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]

/- English proof (translation)
Take `⟨π, hπ1, hπ2⟩` from `hU`. Establish `hk1 : ∀ x : k, valuation k x < 1 ↔ valuation E (algebraMap k E x) < 1`. Introduce `x`. Establish `h` using `val_le_iff (E := E) (1 : k) x`. Simplify using `only [map_one] at h`.

Rewrite using `[← not_le, ← not_le, h]`. Establish `hne : π ≠ 0`. Introduce and unpack `rfl`. Take `⟨y, hy, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (GroundTheory.LocalField.maximalIdeal_ne_bot E)`. Establish `hlt` using `lt_one_of_mem_maximal E y hy`.

Establish `h0` using `hπ2 _ hlt`. Rewrite `h0` using `[map_zero, map_zero]`. Conclude with `hy0 (Subtype.ext ((Valuation.zero_iff _).mp (le_antisymm h0 zero_le')))`. Use `⟨π, ⟨(hk1 π).mpr hπ1, hne, ?_⟩, ⟨hπ1, (map_ne_zero _).mpr hne, hπ2⟩⟩` and prove the remaining obligations. Introduce `x hx`.

Conclude with `(val_le_iff x π).mpr (hπ2 _ ((hk1 x).mp hx))`.
-/
theorem uniformiser_of_unramified (hU : IsUnramifiedLoc k E) :
    ∃ π : k, IsUniformiser π ∧ IsUniformiser (algebraMap k E π) := by
  obtain ⟨π, hπ1, hπ2⟩ := hU
  have hk1 : ∀ x : k, valuation k x < 1 ↔ valuation E (algebraMap k E x) < 1 := by
    intro x
    have h := val_le_iff (E := E) (1 : k) x
    simp only [map_one] at h
    rw [← not_le, ← not_le, h]
  have hne : π ≠ 0 := by
    rintro rfl
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GroundTheory.LocalField.maximalIdeal_ne_bot E)
    have hlt := lt_one_of_mem_maximal E y hy
    have h0 := hπ2 _ hlt
    rw [map_zero, map_zero] at h0
    exact hy0 (Subtype.ext ((Valuation.zero_iff _).mp (le_antisymm h0 zero_le')))
  refine ⟨π, ⟨(hk1 π).mpr hπ1, hne, ?_⟩, ⟨hπ1, (map_ne_zero _).mpr hne, hπ2⟩⟩
  intro x hx
  exact (val_le_iff x π).mpr (hπ2 _ ((hk1 x).mp hx))

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨π, -, hπE⟩` from `uniformiser_of_unramified hU`. Take `⟨hπ1, hπ0, hπmax⟩` from `hπE`. Use `haveI := GroundTheory.LocalField.isDiscreteValuationRing E`.

Establish `hint : ∀ x : 𝒪[E], ((τ : E →+* E).comp (𝒪[E]).subtype) x ∈ 𝒪[E]`. Introduce `x`. Use `show valuation E (τ x) ≤ 1`. Rewrite using `[hval]`. Conclude with `x.2`.

Set `τO : 𝒪[E] →+* 𝒪[E]` to `((τ : E →+* E).comp (𝒪[E]).subtype).codRestrict 𝒪[E] hint`. Establish `hτO : ∀ x : 𝒪[E], ((τO x : 𝒪[E]) : E) = τ x` using `fun x => rfl`. Set `πO : 𝒪[E]` to `⟨algebraMap k E π, hπ1.le⟩`. Establish `hτπ : τO πO = πO` using `Subtype.ext (by rw [hτO]; exact τ.commutes π)`. Establish `hspan : ∀ y : 𝒪[E], valuation E (y : E) < 1 → y ∈ Ideal.span {πO}`.

Introduce `y hy`. Rewrite using `[Ideal.mem_span_singleton']`. Establish `hle` using `hπmax _ hy`. Use `⟨⟨(y : E) / algebraMap k E π, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show valuation E ((y : E) / algebraMap k E π) ≤ 1`.

Rewrite using `[div_eq_mul_inv, map_mul, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Subtype.ext (div_mul_cancel₀ (y : E) hπ0)`. Take `⟨q, hq1, hq2⟩` from `residue_card_facts E`. Establish `hqmem : (q : 𝒪[E]) ∈ Ideal.span {πO}` using `hspan _ (by simpa using hq1)`.

Establish `hpowmem : ∀ x : 𝒪[E], x ^ q - x ∈ Ideal.span {πO}` using `fun x => hspan _ (hq2 x)`. Establish `h1 : ∀ x : 𝒪[E], τO x - x ∈ Ideal.span {πO}`. Introduce `x`. Apply `hspan` to reduce the goal to its premises. Establish `hle : valuation E ((τO x - x : 𝒪[E]) : E) ≤ 1` using `(τO x - x).2`.

Conclude with `lt_of_le_of_ne hle (hcon x x.2)`. Establish `hnt : Ideal.span {πO} ≠ ⊤`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Use `(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mp hu` as an intermediate fact.

Conclude with `(ne_of_lt hπ1) this`. Establish `hbot` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {πO}) hnt`. Establish `hall : ∀ x : 𝒪[E], τO x = x`. Introduce `x`. Establish `hmem : τO x - x ∈ ⨅ i, (Ideal.span {πO}) ^ i`.

Rewrite using `[Submodule.mem_iInf]`. Introduce `i`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Simplify using the standard rewrite rules. Conclude with `sub_mem_span_pow τO πO q hτπ hqmem hpowmem h1 i hi x`.

Rewrite `hmem` using `[hbot]`. Conclude with `sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem)`. Apply `hτ` to reduce the goal to its premises. Use `AlgEquiv.ext fun y => ?_` and prove the remaining obligations. Use `show τ y = y`.

Distinguish the cases in `hy : valuation E y ≤ 1`. Use `congrArg Subtype.val (hall ⟨y, hy⟩)` as an intermediate fact. Rewrite `this` using `[hτO]`. Conclude with `this`. Establish `hy0 : y ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hy (by rw [map_zero]; exact zero_le')`. Establish `hy' : valuation E y⁻¹ ≤ 1` using `((Valuation.one_lt_val_iff _ hy0).mp (not_le.mp hy)).le`. Use `congrArg Subtype.val (hall ⟨y⁻¹, hy'⟩)` as an intermediate fact. Rewrite `this` using `[hτO]`.

Simplify using `only [map_inv₀] at this`. Conclude with `inv_injective this`.
-/
theorem exists_moved (hU : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1)
    (hval : ∀ x : E, valuation E (τ x) = valuation E x) :
    ∃ x : E, x ∈ intO E ∧ valuation E (τ x - x) = 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨π, -, hπE⟩ := uniformiser_of_unramified hU
  obtain ⟨hπ1, hπ0, hπmax⟩ := hπE
  haveI := GroundTheory.LocalField.isDiscreteValuationRing E
  have hint : ∀ x : 𝒪[E], ((τ : E →+* E).comp (𝒪[E]).subtype) x ∈ 𝒪[E] := by
    intro x
    show valuation E (τ x) ≤ 1
    rw [hval]
    exact x.2
  let τO : 𝒪[E] →+* 𝒪[E] := ((τ : E →+* E).comp (𝒪[E]).subtype).codRestrict 𝒪[E] hint
  have hτO : ∀ x : 𝒪[E], ((τO x : 𝒪[E]) : E) = τ x := fun x => rfl
  let πO : 𝒪[E] := ⟨algebraMap k E π, hπ1.le⟩
  have hτπ : τO πO = πO := Subtype.ext (by rw [hτO]; exact τ.commutes π)
  have hspan : ∀ y : 𝒪[E], valuation E (y : E) < 1 → y ∈ Ideal.span {πO} := by
    intro y hy
    rw [Ideal.mem_span_singleton']
    have hle := hπmax _ hy
    refine ⟨⟨(y : E) / algebraMap k E π, ?_⟩, ?_⟩
    · show valuation E ((y : E) / algebraMap k E π) ≤ 1
      rw [div_eq_mul_inv, map_mul, map_inv₀]
      calc valuation E (y : E) * (valuation E (algebraMap k E π))⁻¹
          ≤ valuation E (algebraMap k E π) * (valuation E (algebraMap k E π))⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hπ0)
    · exact Subtype.ext (div_mul_cancel₀ (y : E) hπ0)
  obtain ⟨q, hq1, hq2⟩ := residue_card_facts E
  have hqmem : (q : 𝒪[E]) ∈ Ideal.span {πO} := hspan _ (by simpa using hq1)
  have hpowmem : ∀ x : 𝒪[E], x ^ q - x ∈ Ideal.span {πO} := fun x => hspan _ (hq2 x)
  have h1 : ∀ x : 𝒪[E], τO x - x ∈ Ideal.span {πO} := by
    intro x
    apply hspan
    have hle : valuation E ((τO x - x : 𝒪[E]) : E) ≤ 1 := (τO x - x).2
    exact lt_of_le_of_ne hle (hcon x x.2)
  have hnt : Ideal.span {πO} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have := (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mp hu
    exact (ne_of_lt hπ1) this
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {πO}) hnt
  have hall : ∀ x : 𝒪[E], τO x = x := by
    intro x
    have hmem : τO x - x ∈ ⨅ i, (Ideal.span {πO}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · exact sub_mem_span_pow τO πO q hτπ hqmem hpowmem h1 i hi x
    rw [hbot] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem)
  apply hτ
  refine AlgEquiv.ext fun y => ?_
  show τ y = y
  by_cases hy : valuation E y ≤ 1
  · have := congrArg Subtype.val (hall ⟨y, hy⟩)
    rw [hτO] at this
    exact this
  · have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by rw [map_zero]; exact zero_le')
    have hy' : valuation E y⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hy0).mp (not_le.mp hy)).le
    have := congrArg Subtype.val (hall ⟨y⁻¹, hy'⟩)
    rw [hτO] at this
    simp only [map_inv₀] at this
    exact inv_injective this

end Ext

/- English proof (translation)
Introduce `hA k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ`. Take `⟨hval, hint, -⟩` from `hA k E hU σ hσ`. Use `⟨integral_basis k E hint, uniformiser_of_unramified hU, ?_⟩` and prove the remaining obligations. Introduce `j hj0 hjn`. Establish `hord : orderOf σ = Module.finrank k E`.

Rewrite using `[orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]`. Establish `hne : σ ^ j ≠ 1` using `pow_ne_one_of_lt_orderOf hj0.ne' (hord ▸ hjn)`. Take `⟨x, hx, hx1⟩` from `exists_moved hU (σ ^ j) hne (hval (σ ^ j))`. Conclude with `⟨x, hx, hx1⟩`.
-/
theorem unramifiedDictionary_part_b : D0a → IntegralBasisUnramified := by
  intro hA k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ
  obtain ⟨hval, hint, -⟩ := hA k E hU σ hσ
  refine ⟨integral_basis k E hint, uniformiser_of_unramified hU, ?_⟩
  intro j hj0 hjn
  have hord : orderOf σ = Module.finrank k E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hne : σ ^ j ≠ 1 := pow_ne_one_of_lt_orderOf hj0.ne' (hord ▸ hjn)
  obtain ⟨x, hx, hx1⟩ := exists_moved hU (σ ^ j) hne (hval (σ ^ j))
  exact ⟨x, hx, hx1⟩

end GlobalTheory.CompanionTheory.Unram
