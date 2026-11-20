import Mathlib
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.SeparableClosureValuation
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

section Ambient

variable {K Ω : Type*} [Field K] [Field Ω] [ValuativeRel Ω] [Algebra K Ω]

/- English proof (translation)
Rewrite using `[← Valuation.vle_iff_le, ← Valuation.vle_iff_le, IntermediateField.coe_vle_coe_iff]`.
-/
theorem valuation_le_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x ≤ valuation E y ↔ valuation Ω (x : Ω) ≤ valuation Ω (y : Ω) := by
  rw [← Valuation.vle_iff_le, ← Valuation.vle_iff_le, IntermediateField.coe_vle_coe_iff]

/- English proof (translation)
Rewrite using `[le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe, valuation_le_valuation_iff_coe]`.
-/
theorem valuation_eq_valuation_iff_coe (E : IntermediateField K Ω) (x y : E) :
    valuation E x = valuation E y ↔ valuation Ω (x : Ω) = valuation Ω (y : Ω) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe,
    valuation_le_valuation_iff_coe]

/- English proof (translation)
Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation E), valuation_le_valuation_iff_coe]`. Simplify using the standard rewrite rules.
-/
theorem mem_integer_intermediateField_iff (E : IntermediateField K Ω) (x : E) :
    x ∈ 𝒪[E] ↔ valuation Ω (x : Ω) ≤ 1 := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation E), valuation_le_valuation_iff_coe]
  simp

/- English proof (translation)
Rewrite using `[(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one, ← map_one (valuation E)]`. Conclude with `(valuation_eq_valuation_iff_coe E _ _).trans (by simp; rfl)`.
-/
theorem isUnit_integer_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    IsUnit x ↔ valuation Ω ((x : E) : Ω) = 1 := by
  rw [(Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one, ← map_one (valuation E)]
  exact (valuation_eq_valuation_iff_coe E _ _).trans (by simp; rfl)

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_intermediateField_iff]`. Establish `: valuation Ω ((x : E) : Ω) ≤ 1` using `(mem_integer_intermediateField_iff E x).mp x.2`. Conclude with `⟨fun h ↦ lt_of_le_of_ne this h, fun h ↦ h.ne⟩`.
-/
theorem mem_maximalIdeal_intermediateField_iff (E : IntermediateField K Ω) (x : 𝒪[E]) :
    x ∈ 𝓂[E] ↔ valuation Ω ((x : E) : Ω) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_integer_intermediateField_iff]
  have : valuation Ω ((x : E) : Ω) ≤ 1 := (mem_integer_intermediateField_iff E x).mp x.2
  exact ⟨fun h ↦ lt_of_le_of_ne this h, fun h ↦ h.ne⟩

/- English proof (translation)
Rewrite using `[(Valuation.integer.integers (valuation E)).dvd_iff_le]`. Conclude with `valuation_le_valuation_iff_coe E _ _`.
-/
theorem dvd_integer_intermediateField_iff (E : IntermediateField K Ω) (x y : 𝒪[E]) :
    x ∣ y ↔ valuation Ω ((y : E) : Ω) ≤ valuation Ω ((x : E) : Ω) := by
  rw [(Valuation.integer.integers (valuation E)).dvd_iff_le]
  exact valuation_le_valuation_iff_coe E _ _

def integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) : 𝒪[E] →ₐ[𝒪[K]] 𝒪[F] where
  toFun x := ⟨IntermediateField.inclusion h x, by
    rw [mem_integer_intermediateField_iff]
    exact (mem_integer_intermediateField_iff E x).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω] {E F : IntermediateField K Ω}
    (h : E ≤ F) (x : 𝒪[E]) : (((integerInclusion h x : 𝒪[F]) : F) : Ω) = ((x : E) : Ω) :=
  rfl

/- English proof (translation)
Introduce `x y hxy`. Use `congrArg (fun z : 𝒪[F] ↦ ((z : F) : Ω)) hxy` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext this)`.
-/
theorem integerInclusion_injective [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : Function.Injective (integerInclusion h) := by
  intro x y hxy
  have := congrArg (fun z : 𝒪[F] ↦ ((z : F) : Ω)) hxy
  exact Subtype.ext (Subtype.ext this)

instance isLocalHom_integerInclusion [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : IsLocalHom (integerInclusion h) :=
  ⟨fun x hx ↦ by
    rw [isUnit_integer_intermediateField_iff] at hx ⊢
    exact hx⟩

end Ambient

section Discrete

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

/- English proof (translation)
Take `⟨L, hL, hxL⟩` from `mem_maximalUnramifiedExtension_iff.mp hx`. Use `hL.1` as an intermediate fact. Establish `he : ramificationIndex K L = 1` using `hL.ramificationIndex_eq_one`. Use `set y : L := ⟨x, hxL⟩`. Take `⟨a, ha, hay⟩` from `exists_ord_eq K (ord y)`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Establish `h1` using `ordRat_algebraMap_of_finite (K := K) (Ω := Ω) y`. Rewrite `h1` using `[he, Nat.cast_one, div_one]`. Rewrite using `[← ordRat_eq_ordRat_iff (K := K) hx0 ((_root_.map_ne_zero _).mpr ha), ordRat_algebraMap, hay]`. Conclude with `h1`.
-/
theorem exists_valuation_eq_algebraMap {x : Ω} (hx : x ∈ 𝔼) (hx0 : x ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ valuation Ω x = valuation Ω (algebraMap K Ω a) := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  have := hL.1
  have he : ramificationIndex K L = 1 := hL.ramificationIndex_eq_one
  set y : L := ⟨x, hxL⟩
  obtain ⟨a, ha, hay⟩ := exists_ord_eq K (ord y)
  refine ⟨a, ha, ?_⟩
  have h1 := ordRat_algebraMap_of_finite (K := K) (Ω := Ω) y
  rw [he, Nat.cast_one, div_one] at h1
  rw [← ordRat_eq_ordRat_iff (K := K) hx0 ((_root_.map_ne_zero _).mpr ha), ordRat_algebraMap,
    hay]
  exact h1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap_integer_intermediateField (E : IntermediateField K Ω) (a : 𝒪[K]) :
    (((algebraMap 𝒪[K] 𝒪[E] a : 𝒪[E]) : E) : Ω) = algebraMap K Ω (a : K) :=
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

/- English proof (translation)
Simplify using `using valuation_algebraMap_eq_iff (G := Ω) x 1`.
-/
theorem valuation_algebraMap_eq_one_iff (x : K) :
    valuation Ω (algebraMap K Ω x) = 1 ↔ valuation K x = 1 := by
  simpa using valuation_algebraMap_eq_iff (G := Ω) x 1

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω] in

/- English proof (translation)
Rewrite using `[isUnit_integer_intermediateField_iff, coe_algebraMap_integer_intermediateField, valuation_algebraMap_eq_one_iff]`. Conclude with `((Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hϖ).ne`.
-/
theorem not_isUnit_algebraMap_uniformizer (E : IntermediateField K Ω) {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) : ¬ IsUnit (algebraMap 𝒪[K] 𝒪[E] ϖ) := by
  rw [isUnit_integer_intermediateField_iff, coe_algebraMap_integer_intermediateField,
    valuation_algebraMap_eq_one_iff]
  exact ((Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hϖ).ne

/- English proof (translation)
Establish `hx0 : ((r : 𝔼) : Ω) ≠ 0`. Introduce `h`. Conclude with `hr (Subtype.ext (Subtype.ext h))`. Take `⟨a, ha, hva⟩` from `exists_valuation_eq_algebraMap (r : 𝔼).2 hx0`. Establish `haK : a ∈ 𝒪[K]`.

Rewrite using `[Valuation.mem_integer_iff, ← map_one (valuation K), ← valuation_algebraMap_le_iff (G := Ω), map_one, ← hva]`. Conclude with `(mem_integer_intermediateField_iff _ _).mp r.2`. Use `set a' : 𝒪[K] := ⟨a, haK⟩`. Establish `ha' : a' ≠ 0` using `fun h ↦ ha (congrArg Subtype.val h)`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha' hϖ`.

Establish `hu1 : valuation Ω (algebraMap K Ω ((u : 𝒪[K]) : K)) = 1`. Rewrite using `[valuation_algebraMap_eq_one_iff]`. Conclude with `(Valuation.integer.integers (valuation K)).valuation_unit u`. Establish `hv : valuation Ω ((r : 𝔼) : Ω) = valuation Ω (algebraMap K Ω (ϖ : K)) ^ n`. Establish `h2 : a = ((u : 𝒪[K]) : K) * (ϖ : K) ^ n`.

Use `congrArg Subtype.val hu` as an intermediate fact. Simplify `this` using `[a']`. Rewrite using `[hva, h2, map_mul, map_mul, hu1, one_mul, map_pow, map_pow]`. Establish `hv' : valuation Ω (((algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n : 𝒪[𝔼]) : 𝔼) : Ω) = valuation Ω (algebraMap K Ω (ϖ : K)) ^ n`. Rewrite using `[← map_pow]`.

Simplify using the standard rewrite rules. Apply the tactic sequence `refine ⟨n, associated_of_dvd_dvd ?_ ?_⟩ <;> rw [dvd_integer_intermediateField_iff, hv, hv']`.
-/
theorem exists_associated_pow {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {r : 𝒪[𝔼]} (hr : r ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n) r := by
  have hx0 : ((r : 𝔼) : Ω) ≠ 0 := by
    intro h
    exact hr (Subtype.ext (Subtype.ext h))
  obtain ⟨a, ha, hva⟩ := exists_valuation_eq_algebraMap (r : 𝔼).2 hx0
  have haK : a ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, ← map_one (valuation K), ← valuation_algebraMap_le_iff (G := Ω),
      map_one, ← hva]
    exact (mem_integer_intermediateField_iff _ _).mp r.2
  set a' : 𝒪[K] := ⟨a, haK⟩
  have ha' : a' ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha' hϖ
  have hu1 : valuation Ω (algebraMap K Ω ((u : 𝒪[K]) : K)) = 1 := by
    rw [valuation_algebraMap_eq_one_iff]
    exact (Valuation.integer.integers (valuation K)).valuation_unit u
  have hv : valuation Ω ((r : 𝔼) : Ω) = valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    have h2 : a = ((u : 𝒪[K]) : K) * (ϖ : K) ^ n := by
      have := congrArg Subtype.val hu
      simpa [a'] using this
    rw [hva, h2, map_mul, map_mul, hu1, one_mul, map_pow, map_pow]
  have hv' : valuation Ω (((algebraMap 𝒪[K] 𝒪[𝔼] ϖ ^ n : 𝒪[𝔼]) : 𝔼) : Ω) =
      valuation Ω (algebraMap K Ω (ϖ : K)) ^ n := by
    rw [← map_pow]
    simp
  refine ⟨n, associated_of_dvd_dvd ?_ ?_⟩ <;> rw [dvd_integer_intermediateField_iff, hv, hv']

/- English proof (translation)
Use `set p := algebraMap 𝒪[K] 𝒪[𝔼] ϖ`. Establish `hp` using `not_isUnit_algebraMap_uniformizer 𝔼 hϖ`. Establish `hp0 : p ≠ 0`. Introduce `h`. Establish `h'` using `congrArg (fun z : 𝒪[𝔼] ↦ ((z : 𝔼) : Ω)) h`.

Simplify using `only [p, coe_algebraMap_integer_intermediateField] at h'`. Rewrite `h'` using `[ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_eq_zero_iff _ (algebraMap K Ω).injective]`. Conclude with `hϖ.ne_zero (Subtype.ext h')`. Establish `hdvd : ∀ x : 𝒪[𝔼], ¬ IsUnit x → p ∣ x`. Introduce `x hx`.

Break down `eq_or_ne x 0 with rfl | hx0` into its components or cases. Conclude with `dvd_zero _`. Take `⟨n, hn⟩` from `exists_associated_pow hϖ hx0`. Break down `n with _ | n` into its components or cases. Conclude with `absurd (hn.isUnit (by simp)) hx`.

Conclude with `(dvd_pow_self p n.succ_ne_zero).trans hn.dvd`. Use `irreducible_iff.mpr ⟨hp, fun a b hab ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨c, rfl⟩` from `hdvd a h.1`.

Take `⟨d, rfl⟩` from `hdvd b h.2`. Establish `: p * (c * d) = 1`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises. Take the linear combination `hab.symm`. Conclude with `hp (isUnit_iff_exists_inv.mpr ⟨_, this⟩)`.
-/
theorem irreducible_algebraMap_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[𝔼] ϖ) := by
  set p := algebraMap 𝒪[K] 𝒪[𝔼] ϖ
  have hp := not_isUnit_algebraMap_uniformizer 𝔼 hϖ
  have hp0 : p ≠ 0 := by
    intro h
    have h' := congrArg (fun z : 𝒪[𝔼] ↦ ((z : 𝔼) : Ω)) h
    simp only [p, coe_algebraMap_integer_intermediateField] at h'
    rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_eq_zero_iff _ (algebraMap K Ω).injective] at h'
    exact hϖ.ne_zero (Subtype.ext h')
  have hdvd : ∀ x : 𝒪[𝔼], ¬ IsUnit x → p ∣ x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨n, hn⟩ := exists_associated_pow hϖ hx0
    rcases n with _ | n
    · exact absurd (hn.isUnit (by simp)) hx
    · exact (dvd_pow_self p n.succ_ne_zero).trans hn.dvd
  refine irreducible_iff.mpr ⟨hp, fun a b hab ↦ ?_⟩
  by_contra h
  push Not at h
  obtain ⟨c, rfl⟩ := hdvd a h.1
  obtain ⟨d, rfl⟩ := hdvd b h.2
  have : p * (c * d) = 1 := by
    apply mul_left_cancel₀ hp0
    linear_combination hab.symm
  exact hp (isUnit_iff_exists_inv.mpr ⟨_, this⟩)

instance isDiscreteValuationRing_integer : IsDiscreteValuationRing 𝒪[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, irreducible_algebraMap_uniformizer hϖ, fun hx ↦ exists_associated_pow hϖ hx⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, (irreducible_algebraMap_uniformizer hϖ).maximalIdeal_eq]`.
-/
theorem map_maximalIdeal_integer : (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[𝔼]) = 𝓂[𝔼] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
    (irreducible_algebraMap_uniformizer hϖ).maximalIdeal_eq]

end Discrete

section Automorphism

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsAlgebraic K L]

variable (K L) in

def integerAlgEquivOfIsAlgebraic : (L ≃ₐ[K] L) →* (𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L]) where
  toFun ρ :=
    { toFun x := ⟨ρ x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      invFun x := ⟨ρ.symm x, by
        rw [Valuation.mem_integer_iff, valuation_algEquiv_apply_of_isAlgebraic]
        exact x.2⟩
      left_inv x := Subtype.ext (ρ.symm_apply_apply _)
      right_inv x := Subtype.ext (ρ.apply_symm_apply _)
      map_mul' x y := Subtype.ext (map_mul ρ _ _)
      map_add' x y := Subtype.ext (map_add ρ _ _)
      commutes' a := Subtype.ext (ρ.commutes _) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_integerAlgEquivOfIsAlgebraic_apply (ρ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    (integerAlgEquivOfIsAlgebraic K L ρ x : L) = ρ x :=
  rfl

end Automorphism

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

omit [TopologicalSpace Ω] [IsValuativeTopology Ω] [Algebra.IsAlgebraic K Ω] in

instance isAlgebraic_maximalUnramifiedExtension : Algebra.IsAlgebraic K 𝔼 :=
  inferInstance

/- English proof (translation)
Take `⟨L, hL, hxL⟩` from `mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2`. Use `hL.1` as an intermediate fact. Establish `h` using `hL.ramificationIndex_eq_one`. Establish `hle` using `hL.le_maximalUnramifiedExtension`. Use `set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩`.

Establish `hxz : integerInclusion hle z = x` using `rfl`. Use `⟨Module.finrank K L, Module.finrank_pos.ne', ?_⟩` and prove the remaining obligations. Use `Fintype.ofFinite 𝓀[L]` as an intermediate fact. Establish `hz : z ^ (Nat.card 𝓀[K] ^ Module.finrank K L) - z ∈ 𝓂[L]`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← card_residueField_of_unramified K L h, Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]`.

Rewrite `hz`, the goal using `[mem_maximalIdeal_intermediateField_iff]`. Rewrite using `[← hxz]`. Simplify using `using hz`.
-/
theorem exists_pow_card_pow_sub_mem_maximalIdeal (x : 𝒪[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ x ^ (Nat.card 𝓀[K] ^ n) - x ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hxz : integerInclusion hle z = x := rfl
  refine ⟨Module.finrank K L, Module.finrank_pos.ne', ?_⟩
  have := Fintype.ofFinite 𝓀[L]
  have hz : z ^ (Nat.card 𝓀[K] ^ Module.finrank K L) - z ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, ← card_residueField_of_unramified K L h,
      Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  rw [← hxz]
  simpa using hz

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn`. Take `⟨hL, -⟩` from `isUnramifiedSubextension_adjoin hn hζ`. Use `set L := IntermediateField.adjoin K {ζ}`. Use `hL.1` as an intermediate fact. Establish `hle` using `hL.le_maximalUnramifiedExtension`.

Establish `hmK` using `natCast_card_pow_sub_one_ne_zero (K := K) hn`. Establish `hm : ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0` using `natCast_residueField_ne_zero L hmK`. Establish `hm0 : Nat.card 𝓀[K] ^ n - 1 ≠ 0`. Introduce and unpack `h0`. Rewrite `hmK` using `[h0, Nat.cast_zero]`.

Conclude with `hmK rfl`. Use `set ζL : L := IntermediateField.AdjoinSimple.gen K ζ`. Establish `hζL : IsPrimitiveRoot ζL (Nat.card 𝓀[K] ^ n - 1)` using `hζ.of_map_of_injective (f := L.val) Subtype.val_injective`. Use `set ζO : 𝒪[L] := ⟨ζL, mem_integer_of_pow_eq_one hm0 hζL.pow_eq_one⟩`. Establish `hζO : IsPrimitiveRoot ζO (Nat.card 𝓀[K] ^ n - 1)` using `hζL.of_map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective`.

Establish `hres` using `isPrimitiveRoot_residue hm hζO`. Use `⟨residue 𝒪[𝔼] (integerInclusion hle ζO), ?_⟩` and prove the remaining obligations. Use `⟨by rw [← map_pow, ← map_pow, hζO.pow_eq_one, map_one, map_one], fun l hl ↦ ?_⟩` and prove the remaining obligations. Use `hres.dvd_of_pow_eq_one l ?_` and prove the remaining obligations. Rewrite `hl` using `[← map_pow, ← map_pow]`.

Rewrite using `[← map_pow, ← map_one (residue 𝒪[L]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_intermediateField_iff]`. Rewrite `hl` using `[← map_one (residue 𝒪[𝔼]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal_intermediateField_iff]`. Simplify using `using hl`.
-/
theorem exists_isPrimitiveRoot_residue {n : ℕ} (hn : n ≠ 0) :
    ∃ ζ : ResidueField 𝒪[𝔼], IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1) := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  set L := IntermediateField.adjoin K {ζ}
  have := hL.1
  have hle := hL.le_maximalUnramifiedExtension
  have hmK := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have hm : ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[L]) ≠ 0 := natCast_residueField_ne_zero L hmK
  have hm0 : Nat.card 𝓀[K] ^ n - 1 ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hmK
    exact hmK rfl
  set ζL : L := IntermediateField.AdjoinSimple.gen K ζ
  have hζL : IsPrimitiveRoot ζL (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := L.val) Subtype.val_injective
  set ζO : 𝒪[L] := ⟨ζL, mem_integer_of_pow_eq_one hm0 hζL.pow_eq_one⟩
  have hζO : IsPrimitiveRoot ζO (Nat.card 𝓀[K] ^ n - 1) :=
    hζL.of_map_of_injective (f := (𝒪[L]).subtype) Subtype.val_injective
  have hres := isPrimitiveRoot_residue hm hζO
  refine ⟨residue 𝒪[𝔼] (integerInclusion hle ζO), ?_⟩
  refine ⟨by rw [← map_pow, ← map_pow, hζO.pow_eq_one, map_one, map_one], fun l hl ↦ ?_⟩
  refine hres.dvd_of_pow_eq_one l ?_
  rw [← map_pow, ← map_pow] at hl
  rw [← map_pow, ← map_one (residue 𝒪[L]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff]
  rw [← map_one (residue 𝒪[𝔼]), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
    mem_maximalIdeal_intermediateField_iff] at hl
  simpa using hl

variable [IsGalois K Ω]

/- English proof (translation)
Take `⟨L, hL, hxL⟩` from `mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2`. Use `hL.1` as an intermediate fact. Establish `h` using `hL.ramificationIndex_eq_one`. Establish `hle` using `hL.le_maximalUnramifiedExtension`. Take `⟨ξ, hξ, htop⟩` from `exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h`.

Establish `hn : Module.finrank K L ≠ 0` using `Module.finrank_pos.ne'`. Rewrite `hξ` using `[card_residueField_of_unramified K L h]`. Establish `hm` using `natCast_card_pow_sub_one_ne_zero (K := K) hn`. Establish `key : (maximalUnramifiedExtension K Ω).val.comp ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) = L.val.comp (frobenius K L h).toAlgHom`. Use `AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_` and prove the remaining obligations.

Introduce `y hy`. Rewrite `hy` using `[Set.mem_singleton_iff]`. Rewrite using `[hy]`. Establish `h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1`. Rewrite using `[← map_pow, hξ.pow_eq_one, map_one]`.

Simplify using `only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]`. Rewrite using `[maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1, frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]`. Simplify using the standard rewrite rules. Use `set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩`. Establish `hz` using `frobenius_sub_pow_mem_maximalIdeal K L h z`.

Rewrite `hz`, the goal using `[mem_maximalIdeal_intermediateField_iff]`. Establish `hk` using `congrArg (fun f : L →ₐ[K] Ω ↦ f ⟨(x : 𝔼), hxL⟩) key`. Simplify using `only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at hk`. Use `hz using 2` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `((maximalUnramifiedExtensionFrobenius K Ω (IntermediateField.inclusion hle ⟨(x : 𝔼), hxL⟩) : 𝔼) : Ω) - _ = ((frobenius K L h ⟨(x : 𝔼), hxL⟩ : L) : Ω) - _`.

Rewrite using `[hk]`. Both sides reduce to the same expression.
-/
theorem frobenius_integer_sub_pow_mem_maximalIdeal (x : 𝒪[𝔼]) :
    integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x -
      x ^ Nat.card 𝓀[K] ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hz := frobenius_sub_pow_mem_maximalIdeal K L h z
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f ⟨(x : 𝔼), hxL⟩) key
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at hk
  convert hz using 2
  change ((maximalUnramifiedExtensionFrobenius K Ω (IntermediateField.inclusion hle ⟨(x : 𝔼), hxL⟩) :
      𝔼) : Ω) - _ = ((frobenius K L h ⟨(x : 𝔼), hxL⟩ : L) : Ω) - _
  rw [hk]
  rfl

end Frobenius

section FiniteFieldClosure

open Polynomial

variable {k k' : Type*} [Field k] [Finite k] [Field k'] [Algebra k k']

/- English proof (translation)
Assemble the required witnesses or components as `⟨X ^ (Nat.card k ^ n) - X, FiniteField.X_pow_card_pow_sub_X_ne_zero k hn Finite.one_lt_card, by simp [hy]⟩`.
-/
theorem isAlgebraic_of_pow_card_pow_eq_self {y : k'} {n : ℕ} (hn : n ≠ 0)
    (hy : y ^ (Nat.card k ^ n) = y) : IsAlgebraic k y :=
  ⟨X ^ (Nat.card k ^ n) - X, FiniteField.X_pow_card_pow_sub_X_ne_zero k hn Finite.one_lt_card,
    by simp [hy]⟩

omit [Algebra k k'] in

/- English proof (translation)
Establish `h1 : 1 ≤ Nat.card k ^ m` using `Nat.one_le_pow _ _ Nat.card_pos`. Establish `: (X ^ (Nat.card k ^ m) - X : k'[X]) = X * (X ^ (Nat.card k ^ m - 1) - C 1)` using `by conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ]`. Rewrite using `[map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `Splits.X.mul (X_pow_sub_one_splits hζ)`.
-/
theorem splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot {m : ℕ} {ζ : k'}
    (hζ : IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) :
    Splits (X ^ (Nat.card k ^ m) - X : k'[X]) := by
  have h1 : 1 ≤ Nat.card k ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : (X ^ (Nat.card k ^ m) - X : k'[X]) = X * (X ^ (Nat.card k ^ m - 1) - C 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1, pow_succ]
    rw [map_one]
    ring
  rw [this]
  exact Splits.X.mul (X_pow_sub_one_splits hζ)

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p _ hirr ↦ ?_` and prove the remaining obligations. Use `Fact.mk hirr` as an intermediate fact. Set `A` to `AdjoinRoot p`. Set `α : A` to `AdjoinRoot.root p`. Establish `: Module.Finite k' A` using `(AdjoinRoot.powerBasis hirr.ne_zero).finite`.

Establish `: Algebra.IsAlgebraic k' A` using `Algebra.IsAlgebraic.of_finite _ _`. Establish `: Algebra.IsAlgebraic k A` using `Algebra.IsAlgebraic.trans k k' A`. Establish `hint : IsIntegral k α` using `(Algebra.IsAlgebraic.isAlgebraic α).isIntegral`. Set `F` to `IntermediateField.adjoin k {α}`. Establish `: FiniteDimensional k F` using `IntermediateField.adjoin.finiteDimensional hint`.

Establish `: Fintype k` using `Fintype.ofFinite k`. Establish `: Finite F` using `Module.finite_of_finite k`. Establish `: Fintype F` using `Fintype.ofFinite F`. Use `set m := Module.finrank k F`. Establish `hm : m ≠ 0` using `Module.finrank_pos.ne'`.

Establish `hcard : Fintype.card F = Nat.card k ^ m`. Rewrite using `[Module.card_eq_pow_finrank (K := k) (V := F), Nat.card_eq_fintype_card]`. Establish `hα : α ^ (Nat.card k ^ m) = α`. Use `FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k α)` as an intermediate fact. Rewrite `this` using `[hcard]`.

Conclude with `congrArg Subtype.val this`. Take `⟨ζ, hζ⟩` from `h m hm`. Establish `hroot : ((X ^ (Nat.card k ^ m) - X : k'[X]).map (algebraMap k' A)).IsRoot α`. Simplify using `only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow, eval_X, hα, sub_self]`. Take `⟨β, hβ⟩` from `(splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot hζ).mem_range_of_isRoot (FiniteField.X_pow_card_pow_sub_X_ne_zero k' hm Finite.one_lt_card) hroot`.

Use `⟨β, ?_⟩` and prove the remaining obligations. Establish `h0 : aeval α p = 0` using `by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]`. Rewrite `h0` using `[← hβ, aeval_algebraMap_apply_eq_algebraMap_eval]`. Conclude with `(map_eq_zero_iff _ (algebraMap k' A).injective).mp h0`.
-/
theorem isAlgClosed_of_isPrimitiveRoot [Algebra.IsAlgebraic k k']
    (h : ∀ m : ℕ, m ≠ 0 → ∃ ζ : k', IsPrimitiveRoot ζ (Nat.card k ^ m - 1)) : IsAlgClosed k' := by
  refine IsAlgClosed.of_exists_root _ fun p _ hirr ↦ ?_
  have := Fact.mk hirr
  let A := AdjoinRoot p
  let α : A := AdjoinRoot.root p
  have : Module.Finite k' A := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Algebra.IsAlgebraic k' A := Algebra.IsAlgebraic.of_finite _ _
  have : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.trans k k' A
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let F := IntermediateField.adjoin k {α}
  have : FiniteDimensional k F := IntermediateField.adjoin.finiteDimensional hint
  have : Fintype k := Fintype.ofFinite k
  have : Finite F := Module.finite_of_finite k
  have : Fintype F := Fintype.ofFinite F
  set m := Module.finrank k F
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hcard : Fintype.card F = Nat.card k ^ m := by
    rw [Module.card_eq_pow_finrank (K := k) (V := F), Nat.card_eq_fintype_card]
  have hα : α ^ (Nat.card k ^ m) = α := by
    have := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen k α)
    rw [hcard] at this
    exact congrArg Subtype.val this
  obtain ⟨ζ, hζ⟩ := h m hm
  have hroot : ((X ^ (Nat.card k ^ m) - X : k'[X]).map (algebraMap k' A)).IsRoot α := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, IsRoot.def, eval_sub, eval_pow,
      eval_X, hα, sub_self]
  obtain ⟨β, hβ⟩ := (splits_X_pow_card_pow_sub_X_of_isPrimitiveRoot hζ).mem_range_of_isRoot
    (FiniteField.X_pow_card_pow_sub_X_ne_zero k' hm Finite.one_lt_card) hroot
  refine ⟨β, ?_⟩
  have h0 : aeval α p = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [← hβ, aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  exact (map_eq_zero_iff _ (algebraMap k' A).injective).mp h0

end FiniteFieldClosure

section Residue

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]

local notation "𝔼" => maximalUnramifiedExtension K Ω

/- English proof (translation)
Take `⟨x, rfl⟩` from `residue_surjective y`. Take `⟨n, hn, hx⟩` from `exists_pow_card_pow_sub_mem_maximalIdeal x`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hx`.
-/
theorem exists_pow_card_pow_eq_self (y : 𝓀[𝔼]) :
    ∃ n : ℕ, n ≠ 0 ∧ y ^ (Nat.card 𝓀[K] ^ n) = y := by
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨n, hn, hx⟩ := exists_pow_card_pow_sub_mem_maximalIdeal x
  refine ⟨n, hn, ?_⟩
  rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact hx

instance isAlgebraic_residueField : Algebra.IsAlgebraic 𝓀[K] 𝓀[𝔼] := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨n, hn, hy⟩ := exists_pow_card_pow_eq_self y
  exact isAlgebraic_of_pow_card_pow_eq_self hn hy

instance isAlgClosed_residueField : IsAlgClosed 𝓀[𝔼] :=
  isAlgClosed_of_isPrimitiveRoot (k := 𝓀[K]) fun _ hm ↦ exists_isPrimitiveRoot_residue hm

instance isAlgClosure_residueField :
    letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
    IsAlgClosure 𝓀[K] 𝓀[𝔼] :=
  letI : Module.IsTorsionFree 𝓀[K] 𝓀[𝔼] := DivisionSemiring.to_moduleIsTorsionFree
  ⟨isAlgClosed_residueField, isAlgebraic_residueField⟩

end Residue

end GroundTheory.LocalField
