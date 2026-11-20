import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedFieldMaximalIdealDvdUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InertiaFixedDVR

/- English proof (translation)
Introduce `R K Ω _ _ _ _ _ _ _ _ _ _ V hV`. Use `set K' := IntermediateField.fixedField (inertia K V) with hK'`. Use `set W := V.comap (algebraMap K' Ω) with hW`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Use `set c : Ω := algebraMap K Ω (algebraMap R K π) with hc`.

Establish `hπK : algebraMap R K π ≠ 0`. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hπ.ne_zero`. Establish `hc0 : c ≠ 0` using `(map_ne_zero _).2 hπK`. Establish `hcV : c ∈ V`.

Establish `h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω)` using `by rw [hV]; exact ⟨π, rfl⟩`. Conclude with `h`. Establish `hcinv : c⁻¹ ∉ V`. Introduce `h`. Establish `h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω)`.

Express the relevant statement in the definitionally equal form `algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V`. Rewrite using `[map_inv₀]`. Conclude with `h`. Rewrite `h'` using `[hV]`. Take `⟨r, hr⟩` from `h'`.

Apply `hπ.not_isUnit` to reduce the goal to its premises. Use `isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr, map_one, mul_inv_cancel₀ hπK]`. Establish `hcK' : c ∈ K'` using `K'.algebraMap_mem _`. Set `j : W → Ω` to `fun w => ((w : K') : Ω)`.

Establish `hjinj : Function.Injective j` using `fun a b h => Subtype.ext (Subtype.ext h)`. Establish `hjV : ∀ w : W, j w ∈ V` using `fun w => w.2`. Establish `hjK : ∀ w : W, j w ∈ K'` using `fun w => (w : K').2`. Establish `hj_mul : ∀ a b : W, j (a * b) = j a * j b` using `fun _ _ => rfl`. Establish `hj_zero : j 0 = 0` using `rfl`.

Establish `hj_one : j 1 = 1` using `rfl`. Establish `hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n`. Introduce `a n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hj_one`.

Consider the case `succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]`. Set `mk : (y : Ω) → y ∈ K' → y ∈ V → W` to `fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩`. Establish `hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w`. Introduce `w h0 hinv`. Use `isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩` and prove the remaining obligations.

Rewrite using `[hj_mul, hj_one]`. Conclude with `mul_inv_cancel₀ h0`. Establish `hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u`. Introduce `w hw`. Establish `hnu : j w ∈ V.nonunits`.

Rewrite using `[GlobalTheory.FixInertUnram.mem_nonunits_iff']`. Distinguish the cases in `h0 : j w = 0`. Conclude with `Or.inl h0`. Conclude with `Or.inr fun h => hw (hunit w h0 h)`. Establish `hq` using `GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu`.

Use `⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩` and prove the remaining obligations. Rewrite using `[hj_mul]`. Express the relevant statement in the definitionally equal form `j w = c * (j w / c)`. Clear the denominators using the available nonvanishing facts. Use `set ϖ : W := mk c hcK' hcV with hϖ`.

Establish `hϖnu : ¬ IsUnit ϖ`. Introduce `h`. Take `⟨v, hv⟩` from `isUnit_iff_exists_inv.1 h`. Apply `hcinv` to reduce the goal to its premises. Establish `e : c * j v = 1`.

Use `congrArg j hv` as an intermediate fact. Rewrite `this` using `[hj_mul, hj_one]`. Conclude with `this`. Rewrite using `[inv_eq_of_mul_eq_one_right e]`. Conclude with `hjV v`.

Establish `hϖ0 : ϖ ≠ 0` using `fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)`. Establish `hirr : Irreducible ϖ`. Use `⟨hϖnu, fun a b hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Take `⟨a', rfl⟩` from `hdvd a hne.1`. Take `⟨b', rfl⟩` from `hdvd b hne.2`. Apply `hϖnu` to reduce the goal to its premises. Establish `e : ϖ * 1 = ϖ * (ϖ * (a' * b'))`. Rewrite using `[_root_.mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `mul_left_cancel₀ hϖ0 e`. Conclude with `isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩`. Use `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩` and prove the remaining obligations. Establish `hx0 : j x ≠ 0` using `fun h => hx (hjinj (h.trans hj_zero.symm))`.

Establish `hex : ∃ n : ℕ, j x / c ^ n ∉ V` using `GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0`. Take `⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V` from `⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩`. Establish `hn0 : n ≠ 0`. Introduce and unpack `rfl`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[pow_zero, div_one]`. Conclude with `hjV x`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `hmV : j x / c ^ m ∈ V` using `hmin m (by omega)`. Establish `hyK : j x / c ^ m ∈ K'` using `K'.div_mem (hjK x) (pow_mem hcK' m)`.

Establish `hy0 : j x / c ^ m ≠ 0` using `div_ne_zero hx0 (pow_ne_zero _ hc0)`. Establish `hyinv : (j x / c ^ m)⁻¹ ∈ V`. Assume the negation of the conclusion as `hyi`. Establish `hq` using `GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[pow_succ, ← div_div]`. Conclude with `hq`. Establish `hu : IsUnit (mk (j x / c ^ m) hyK hmV)` using `hunit _ hy0 hyinv`. Use `⟨m, hu.unit, hjinj ?_⟩` and prove the remaining obligations. Rewrite using `[IsUnit.unit_spec, hj_mul, hj_pow]`.

Express the relevant statement in the definitionally equal form `c ^ m * (j x / c ^ m) = j x`. Clear the denominators using the available nonvanishing facts.
-/
theorem isDiscreteValuationRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    IsDiscreteValuationRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV
  classical
  set K' := IntermediateField.fixedField (inertia K V) with hK'
  set W := V.comap (algebraMap K' Ω) with hW
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c : Ω := algebraMap K Ω (algebraMap R K π) with hc
  have hπK : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have hc0 : c ≠ 0 := (map_ne_zero _).2 hπK
  have hcV : c ∈ V := by
    have h : algebraMap R K π ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨π, rfl⟩
    exact h
  have hcinv : c⁻¹ ∉ V := by
    intro h
    have h' : (algebraMap R K π)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K π)⁻¹ ∈ V
      rw [map_inv₀]; exact h
    rw [hV] at h'
    obtain ⟨r, hr⟩ := h'
    apply hπ.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨r, IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr, map_one, mul_inv_cancel₀ hπK]
  have hcK' : c ∈ K' := K'.algebraMap_mem _

  let j : W → Ω := fun w => ((w : K') : Ω)
  have hjinj : Function.Injective j := fun a b h => Subtype.ext (Subtype.ext h)
  have hjV : ∀ w : W, j w ∈ V := fun w => w.2
  have hjK : ∀ w : W, j w ∈ K' := fun w => (w : K').2
  have hj_mul : ∀ a b : W, j (a * b) = j a * j b := fun _ _ => rfl
  have hj_zero : j 0 = 0 := rfl
  have hj_one : j 1 = 1 := rfl
  have hj_pow : ∀ (a : W) (n : ℕ), j (a ^ n) = j a ^ n := by
    intro a n
    induction n with
    | zero => simpa using hj_one
    | succ n ih => rw [pow_succ, hj_mul, ih, pow_succ]
  let mk : (y : Ω) → y ∈ K' → y ∈ V → W := fun y h1 h2 => ⟨⟨y, h1⟩, h2⟩
  have hunit : ∀ w : W, j w ≠ 0 → (j w)⁻¹ ∈ V → IsUnit w := by
    intro w h0 hinv
    refine isUnit_iff_exists_inv.2 ⟨mk (j w)⁻¹ (K'.inv_mem (hjK w)) hinv, hjinj ?_⟩
    rw [hj_mul, hj_one]
    exact mul_inv_cancel₀ h0
  have hdvd : ∀ w : W, ¬ IsUnit w → ∃ u : W, w = mk c hcK' hcV * u := by
    intro w hw
    have hnu : j w ∈ V.nonunits := by
      rw [GlobalTheory.FixInertUnram.mem_nonunits_iff']
      by_cases h0 : j w = 0
      · exact Or.inl h0
      · exact Or.inr fun h => hw (hunit w h0 h)
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j w) (hjK w) hnu
    refine ⟨mk (j w / c) (K'.div_mem (hjK w) hcK') hq, hjinj ?_⟩
    rw [hj_mul]
    change j w = c * (j w / c)
    field_simp
  set ϖ : W := mk c hcK' hcV with hϖ
  have hϖnu : ¬ IsUnit ϖ := by
    intro h
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 h
    apply hcinv
    have e : c * j v = 1 := by
      have := congrArg j hv
      rw [hj_mul, hj_one] at this
      exact this
    rw [inv_eq_of_mul_eq_one_right e]
    exact hjV v
  have hϖ0 : ϖ ≠ 0 := fun h => hc0 (by have := congrArg j h; rw [hj_zero] at this; exact this)
  have hirr : Irreducible ϖ := by
    refine ⟨hϖnu, fun a b hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨a', rfl⟩ := hdvd a hne.1
    obtain ⟨b', rfl⟩ := hdvd b hne.2
    apply hϖnu
    have e : ϖ * 1 = ϖ * (ϖ * (a' * b')) := by
      rw [_root_.mul_one]
      calc ϖ = ϖ * a' * (ϖ * b') := hab
        _ = ϖ * (ϖ * (a' * b')) := by ring
    have h1 := mul_left_cancel₀ hϖ0 e
    exact isUnit_iff_exists_inv.2 ⟨a' * b', h1.symm⟩
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨ϖ, hirr, fun {x} hx => ?_⟩
  have hx0 : j x ≠ 0 := fun h => hx (hjinj (h.trans hj_zero.symm))
  have hex : ∃ n : ℕ, j x / c ^ n ∉ V := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ (j x) hx0
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, j x / c ^ n ∉ V ∧ ∀ k < n, j x / c ^ k ∈ V :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => by simpa using Nat.find_min hex hk⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hn
    rw [pow_zero, div_one]
    exact hjV x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hmV : j x / c ^ m ∈ V := hmin m (by omega)
  have hyK : j x / c ^ m ∈ K' := K'.div_mem (hjK x) (pow_mem hcK' m)
  have hy0 : j x / c ^ m ≠ 0 := div_ne_zero hx0 (pow_ne_zero _ hc0)
  have hyinv : (j x / c ^ m)⁻¹ ∈ V := by
    by_contra hyi
    have hq := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ (j x / c ^ m) hyK
      ((GlobalTheory.FixInertUnram.mem_nonunits_iff' V _).2 (Or.inr hyi))
    apply hn
    rw [pow_succ, ← div_div]
    exact hq
  have hu : IsUnit (mk (j x / c ^ m) hyK hmV) := hunit _ hy0 hyinv
  refine ⟨m, hu.unit, hjinj ?_⟩
  rw [IsUnit.unit_spec, hj_mul, hj_pow]
  change c ^ m * (j x / c ^ m) = j x
  field_simp

end GlobalTheory.InertiaFixedDVR
