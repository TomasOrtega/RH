import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open GlobalTheory GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

/- English proof (translation)
Use `letI : Algebra ℂ R := (cK.codRestrict R hR.const_mem).toAlgebra`. Use `haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType`. Use `haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R`. Use `haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hR.frac z`.

Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Use `show z = a / b`. Rewrite using `[← e, mul_div_cancel_right₀ _ hb0]`. Use `set S := primeLocalSubalgebra K p with hS`. Establish `hmem : ∀ x : K, x ∈ S ↔ ∃ s : R, s ∉ p ∧ ∃ a : R, (a : K) = s * x`.

Introduce `x`. Rewrite using `[hS, mem_primeLocalSubalgebra_iff]`. Both sides reduce to the same expression. Establish `hne : ∀ s : R, s ∉ p → (s : K) ≠ 0` using `fun s hs h => hs ((Subtype.ext h : s = 0) ▸ p.zero_mem)`. Establish `h1p : (1 : R) ∉ p` using `(Ideal.ne_top_iff_one p).mp hpp.ne_top`.

Establish `hRS : ∀ r : R, (r : K) ∈ S` using `fun r => (hmem _).2 ⟨1, h1p, r, by simp⟩`. Establish `hinv : ∀ s : R, s ∉ p → (s : K)⁻¹ ∈ S` using `fun s hs => (hmem _).2 ⟨s, hs, 1, by simp [mul_inv_cancel₀ (hne s hs)]⟩`. Establish `hor : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S`. Introduce `x`. Distinguish the cases in `hx : x = 0`.

Conclude with `Or.inl (hx ▸ S.zero_mem)`. Rewrite using `[mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx, mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero hx), heightOneOrd_vw_inv]`. Use linear arithmetic over natural numbers and integers. Set `V : ValuationSubring K` to `{ S.toSubring with mem_or_inv_mem' := hor }`. Establish `hV : ∀ x : K, x ∈ V ↔ x ∈ S` using `fun _ => Iff.rfl`.

Set `ι : R →+* V` to `{ toFun := fun r => ⟨r, hRS r⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Use `letI : Algebra R V := ι.toAlgebra`. Establish `hunit : ∀ s : R, s ∉ p → IsUnit (algebraMap R V s)` using `fun s hs => isUnit_iff_exists_inv.mpr ⟨⟨(s : K)⁻¹, hinv s hs⟩, Subtype.ext (mul_inv_cancel₀ (hne s hs))⟩`. Use `haveI hloc : IsLocalization.AtPrime V p := by`. Use `⟨fun y => hunit y y.2, fun z => ?_, fun {x y} h => ?_⟩` and prove the remaining obligations.

Take `⟨s, hs, a, e⟩` from `(hmem z).1 z.2`. Use `⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (z : K) * s = a`. Rewrite using `[e, mul_comm]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Establish `hxy : (x : K) = y` using `congrArg (fun z : V => (z : K)) h`. Establish `: x = y` using `Subtype.ext hxy`. Rewrite using `[this]`. Use `haveI : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V`. Establish `hc : ∀ a, cK a ∈ V` using `fun a => hRS ⟨cK a, hR.const_mem a⟩`.

Establish `hess : (cK.codRestrict V hc).EssFiniteType`. Establish `h0 : (cK.codRestrict R hR.const_mem).EssFiniteType` using `hR.essFiniteType`. Establish `h1 : (algebraMap R V).EssFiniteType` using `RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization V p.primeCompl)`. Use `h0.comp h1 using 1` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext fun _ => rfl`.

Set `P0 : Place cK` to `⟨V, hc, inferInstance, hess⟩`. Use `⟨P0, ⟨fun f hf => hRS ⟨f, hf⟩, fun f hf => ?_⟩, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, a, e⟩` from `(hmem f).1 hf`. Use `⟨a, a.2, s, s.2, hne s hs, P0.ord_eq_zero (u := algebraMap R V s) (hunit s hs), ?_⟩` and prove the remaining obligations. Rewrite using `[e, mul_comm]`.

Establish `hg0 : (g : K) ≠ 0` using `fun h => hg (Subtype.ext h)`. Prove the components needed by the constructor for the conclusion. Introduce `h hgp`. Establish `h' : 0 ≤ P0.ord (g : K)⁻¹` using `by rw [P0.ord_inv, h]; rfl`. Take `⟨s, hs, a, e⟩` from `(hmem _).1 ((P0.ord_nonneg_iff (inv_ne_zero hg0)).1 h')`.

Establish `: s = a * g` using `Subtype.ext (by show (s : K) = a * g`. Rewrite using `[e, mul_assoc, inv_mul_cancel₀ hg0, mul_one])`. Conclude with `hs (this ▸ p.mul_mem_left a hgp)`. Introduce `hgp`. Conclude with `P0.ord_eq_zero (u := algebraMap R V g) (hunit g hgp)`.
-/
theorem exists_place_isPrimeOf_of_height_eq_one {K : Type} [Field K] (cK : ℂ →+* K)
    (R : Subring K) (hR : IsLocModel cK R) (hic : IsIntegrallyClosed R) (p : Ideal R)
    (hpp : p.IsPrime) (hp : p.height = 1) :
    ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ g ∉ p) := by
  classical
  letI : Algebra ℂ R := (cK.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    show z = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  set S := primeLocalSubalgebra K p with hS
  have hmem : ∀ x : K, x ∈ S ↔ ∃ s : R, s ∉ p ∧ ∃ a : R, (a : K) = s * x := by
    intro x
    rw [hS, mem_primeLocalSubalgebra_iff]
    rfl
  have hne : ∀ s : R, s ∉ p → (s : K) ≠ 0 := fun s hs h =>
    hs ((Subtype.ext h : s = 0) ▸ p.zero_mem)
  have h1p : (1 : R) ∉ p := (Ideal.ne_top_iff_one p).mp hpp.ne_top
  have hRS : ∀ r : R, (r : K) ∈ S := fun r =>
    (hmem _).2 ⟨1, h1p, r, by simp⟩
  have hinv : ∀ s : R, s ∉ p → (s : K)⁻¹ ∈ S := fun s hs =>
    (hmem _).2 ⟨s, hs, 1, by simp [mul_inv_cancel₀ (hne s hs)]⟩
  have hor : ∀ x : K, x ∈ S ∨ x⁻¹ ∈ S := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ S.zero_mem)
    rw [mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp hx,
      mem_primeLocalSubalgebra_iff_heightOneOrd_vw_nonneg p hp (inv_ne_zero hx),
      heightOneOrd_vw_inv]
    omega
  let V : ValuationSubring K := { S.toSubring with mem_or_inv_mem' := hor }
  have hV : ∀ x : K, x ∈ V ↔ x ∈ S := fun _ => Iff.rfl
  let ι : R →+* V :=
    { toFun := fun r => ⟨r, hRS r⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra R V := ι.toAlgebra
  have hunit : ∀ s : R, s ∉ p → IsUnit (algebraMap R V s) := fun s hs =>
    isUnit_iff_exists_inv.mpr ⟨⟨(s : K)⁻¹, hinv s hs⟩, Subtype.ext (mul_inv_cancel₀ (hne s hs))⟩
  haveI hloc : IsLocalization.AtPrime V p := by
    refine ⟨fun y => hunit y y.2, fun z => ?_, fun {x y} h => ?_⟩
    · obtain ⟨s, hs, a, e⟩ := (hmem z).1 z.2
      refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
      show (z : K) * s = a
      rw [e, mul_comm]
    · refine ⟨1, ?_⟩
      have hxy : (x : K) = y := congrArg (fun z : V => (z : K)) h
      have : x = y := Subtype.ext hxy
      rw [this]
  haveI : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  have hc : ∀ a, cK a ∈ V := fun a => hRS ⟨cK a, hR.const_mem a⟩
  have hess : (cK.codRestrict V hc).EssFiniteType := by
    have h0 : (cK.codRestrict R hR.const_mem).EssFiniteType := hR.essFiniteType
    have h1 : (algebraMap R V).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization V p.primeCompl)
    convert h0.comp h1 using 1
    exact RingHom.ext fun _ => rfl
  let P0 : Place cK := ⟨V, hc, inferInstance, hess⟩
  refine ⟨P0, ⟨fun f hf => hRS ⟨f, hf⟩, fun f hf => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨s, hs, a, e⟩ := (hmem f).1 hf
    refine ⟨a, a.2, s, s.2, hne s hs, P0.ord_eq_zero (u := algebraMap R V s) (hunit s hs), ?_⟩
    rw [e, mul_comm]
  · have hg0 : (g : K) ≠ 0 := fun h => hg (Subtype.ext h)
    constructor
    · intro h hgp
      have h' : 0 ≤ P0.ord (g : K)⁻¹ := by rw [P0.ord_inv, h]; rfl
      obtain ⟨s, hs, a, e⟩ := (hmem _).1 ((P0.ord_nonneg_iff (inv_ne_zero hg0)).1 h')
      have : s = a * g := Subtype.ext (by
        show (s : K) = a * g
        rw [e, mul_assoc, inv_mul_cancel₀ hg0, mul_one])
      exact hs (this ▸ p.mul_mem_left a hgp)
    · intro hgp
      exact P0.ord_eq_zero (u := algebraMap R V g) (hunit g hgp)

end GlobalTheory.FieldPair
