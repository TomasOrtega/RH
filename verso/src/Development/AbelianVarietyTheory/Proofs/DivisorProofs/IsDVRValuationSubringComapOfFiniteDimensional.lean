import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory.RestrictDVR

/- English proof (translation)
Use `letI := φ.toAlgebra`. Use `set E := V.comap φ with hE`. Establish `memE : ∀ x : K, x ∈ E ↔ φ x ∈ V` using `fun x => ValuationSubring.mem_comap`. Set `g : E →+* V` to `(φ.comp E.subtype).codRestrict V (fun x => (memE x).1 x.2)`. Establish `hg : ∀ x : E, ((g x : V) : L) = φ x` using `fun x => rfl`.

Establish `hpid : IsPrincipalIdealRing E`. Use `⟨fun I => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Conclude with `bot_isPrincipal`.

Take `⟨x, hxI, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Set `f : E → ℕ∞` to `fun y => IsDiscreteValuationRing.addVal V (g y)`. Set `s : Set E` to `{y | y ∈ I ∧ y ≠ 0}`. Establish `hs : x ∈ s` using `⟨hxI, hx0⟩`. Use `set x0 := Function.argminOn f s ⟨x, hs⟩ with hx0def`.

Establish `hx0s : x0 ∈ s` using `Function.argminOn_mem f s ⟨x, hs⟩`. Use `⟨x0, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `y hy`. Rewrite using `[Ideal.submodule_span_eq, Ideal.mem_span_singleton']`. Distinguish the cases in `hy0 : y = 0`.

Conclude with `⟨0, by simp [hy0]⟩`. Establish `hle : f x0 ≤ f y` using `Function.argminOn_le f s ⟨hy, hy0⟩`. Take `⟨c, hc⟩` from `(IsDiscreteValuationRing.addVal_le_iff_dvd).1 hle`. Establish `hx0K : (x0 : K) ≠ 0` using `fun h => hx0s.2 (Subtype.ext h)`. Establish `hφx0 : φ x0 ≠ 0` using `(map_ne_zero φ).2 hx0K`.

Establish `hcL : φ ((y : K) / x0) = (c : L)`. Use `congrArg Subtype.val hc` as an intermediate fact. Simplify using `only [hg, MulMemClass.coe_mul] at this`. Rewrite using `[map_div₀, this]`. Clear the denominators using the available nonvanishing facts.

Use `⟨⟨(y : K) / x0, (memE _).2 (hcL ▸ c.2)⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [MulMemClass.coe_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]`. Conclude with `hx0s.1`.

Establish `hnf : IsLocalRing.maximalIdeal E ≠ ⊥`. Introduce `hbot`. Establish `hall : ∀ x : K, φ x ∈ V`. Introduce `x`. Break down `E.mem_or_inv_mem x with h | h` into its components or cases.

Conclude with `(memE x).1 h`. Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Establish `hu : IsUnit (⟨x⁻¹, h⟩ : E)`. Assume the negation of the conclusion as `hnu`.

Establish `: (⟨x⁻¹, h⟩ : E) ∈ IsLocalRing.maximalIdeal E` using `hnu`. Rewrite `this` using `[hbot, Ideal.mem_bot]`. Conclude with `inv_ne_zero hx (congrArg Subtype.val this)`. Take `⟨u, hu⟩` from `hu.exists_right_inv`. Establish `: x = (u : K)`.

Establish `h1` using `congrArg Subtype.val hu`. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1`. Clear denominators, using `at h1` for the nonvanishing conditions. Conclude with `h1.symm`. Rewrite using `[this]`.

Conclude with `(memE _).1 u.2`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `hπ0 : (π : L) ≠ 0` using `fun h => hπ.ne_zero (Subtype.ext h)`. Set `ψ : K →+* V` to `φ.codRestrict V hall`. Establish `hint : IsIntegral K ((π : L)⁻¹)` using `Algebra.IsIntegral.isIntegral _`.

Take `⟨p, hpm, hp⟩` from `hint`. Establish `hintV : IsIntegral V ((π : L)⁻¹)`. Use `⟨p.map ψ, hpm.map ψ, ?_⟩` and prove the remaining obligations. Establish `hcomp : (algebraMap V L).comp ψ = algebraMap K L` using `by ext; rfl`. Rewrite using `[Polynomial.eval₂_map, hcomp]`.

Conclude with `hp`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hintV`. Apply `hπ.not_isUnit` to reduce the goal to its premises. Use `IsUnit.of_mul_eq_one y (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `only [MulMemClass.coe_mul, OneMemClass.coe_one]`.

Establish `: (y : L) = (π : L)⁻¹` using `hy`. Rewrite using `[this, mul_inv_cancel₀ hπ0]`. Conclude with `{ hpid with not_a_field' := hnf }`.
-/
theorem isDiscreteValuationRing_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (hfin : (letI := φ.toAlgebra; FiniteDimensional K L))
    (V : ValuationSubring L) [IsDiscreteValuationRing V] :
    IsDiscreteValuationRing (V.comap φ) := by
  letI := φ.toAlgebra
  set E := V.comap φ with hE
  have memE : ∀ x : K, x ∈ E ↔ φ x ∈ V := fun x => ValuationSubring.mem_comap
  let g : E →+* V := (φ.comp E.subtype).codRestrict V (fun x => (memE x).1 x.2)
  have hg : ∀ x : E, ((g x : V) : L) = φ x := fun x => rfl

  have hpid : IsPrincipalIdealRing E := by
    refine ⟨fun I => ?_⟩
    by_cases hI : I = ⊥
    · subst hI; exact bot_isPrincipal
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    let f : E → ℕ∞ := fun y => IsDiscreteValuationRing.addVal V (g y)
    let s : Set E := {y | y ∈ I ∧ y ≠ 0}
    have hs : x ∈ s := ⟨hxI, hx0⟩
    set x0 := Function.argminOn f s ⟨x, hs⟩ with hx0def
    have hx0s : x0 ∈ s := Function.argminOn_mem f s ⟨x, hs⟩
    refine ⟨x0, le_antisymm ?_ ?_⟩
    · intro y hy
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      by_cases hy0 : y = 0
      · exact ⟨0, by simp [hy0]⟩
      have hle : f x0 ≤ f y := Function.argminOn_le f s ⟨hy, hy0⟩
      obtain ⟨c, hc⟩ := (IsDiscreteValuationRing.addVal_le_iff_dvd).1 hle
      have hx0K : (x0 : K) ≠ 0 := fun h => hx0s.2 (Subtype.ext h)
      have hφx0 : φ x0 ≠ 0 := (map_ne_zero φ).2 hx0K
      have hcL : φ ((y : K) / x0) = (c : L) := by
        have := congrArg Subtype.val hc
        simp only [hg, MulMemClass.coe_mul] at this
        rw [map_div₀, this]; field_simp
      refine ⟨⟨(y : K) / x0, (memE _).2 (hcL ▸ c.2)⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul]
      field_simp
    · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
      exact hx0s.1

  have hnf : IsLocalRing.maximalIdeal E ≠ ⊥ := by
    intro hbot
    have hall : ∀ x : K, φ x ∈ V := by
      intro x
      rcases E.mem_or_inv_mem x with h | h
      · exact (memE x).1 h
      by_cases hx : x = 0
      · simp [hx]
      have hu : IsUnit (⟨x⁻¹, h⟩ : E) := by
        by_contra hnu
        have : (⟨x⁻¹, h⟩ : E) ∈ IsLocalRing.maximalIdeal E := hnu
        rw [hbot, Ideal.mem_bot] at this
        exact inv_ne_zero hx (congrArg Subtype.val this)
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have : x = (u : K) := by
        have h1 := congrArg Subtype.val hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
        field_simp at h1; exact h1.symm
      rw [this]; exact (memE _).1 u.2
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    let ψ : K →+* V := φ.codRestrict V hall
    have hint : IsIntegral K ((π : L)⁻¹) := Algebra.IsIntegral.isIntegral _
    obtain ⟨p, hpm, hp⟩ := hint
    have hintV : IsIntegral V ((π : L)⁻¹) := by
      refine ⟨p.map ψ, hpm.map ψ, ?_⟩
      have hcomp : (algebraMap V L).comp ψ = algebraMap K L := by ext; rfl
      rw [Polynomial.eval₂_map, hcomp]
      exact hp
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := L)).mp hintV
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one y (Subtype.ext ?_)
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one]
    have : (y : L) = (π : L)⁻¹ := hy
    rw [this, mul_inv_cancel₀ hπ0]
  exact { hpid with not_a_field' := hnf }

/- English proof (translation)
Introduce `K L _ _ φ hfin V _`. Conclude with `isDiscreteValuationRing_comap K L φ hfin V`.
-/
theorem main : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) := by
  intro K L _ _ φ hfin V _
  exact isDiscreteValuationRing_comap K L φ hfin V

end GlobalTheory.RestrictDVR
