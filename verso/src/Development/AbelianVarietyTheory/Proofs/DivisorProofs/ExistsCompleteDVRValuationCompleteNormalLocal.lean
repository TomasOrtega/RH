import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteDvrInjectiveLocal
open IsLocalRing GlobalTheory.TorRef

namespace GlobalTheory.DivBound

/- English proof (translation)
Introduce `V _ _ _ hV ν h1 h2 hm`. Take `⟨-, -, -, h0⟩` from `hV`. Take `⟨m, hmm, hm0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hm`. Establish `hmK : algebraMap V (FractionRing V) m ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hm0`. Use `haveI : ν.IsNontrivial := ⟨algebraMap V (FractionRing V) m, (ν.ne_zero_iff).2 hmK, (h2 m hmm).ne⟩`.

Use `haveI : IsDiscreteValuationRing ν.valuationSubring := inferInstance`. Use `haveI : CharZero (FractionRing V) := charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))`. Use `haveI : CharZero ν.valuationSubring := RingHom.charZero (algebraMap ν.valuationSubring (FractionRing V))`. Take `⟨W', _, _, _, g, hW', hg, hgl⟩` from `GlobalTheory.LocalCompletion.exists_cDvr_embedding ν.valuationSubring inferInstance inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) inferInstance`. Take `⟨hdvr, hc, hz⟩` from `hW'`.

Set `i : V →+* ν.valuationSubring` to `(algebraMap V (FractionRing V)).codRestrict ν.valuationSubring.toSubring (fun v => h1 v)`. Establish `hi : ∀ v : V, ((i v : ν.valuationSubring) : FractionRing V) = algebraMap V (FractionRing V) v` using `fun _ => rfl`. Establish `hiinj : Function.Injective i` using `fun a b h => IsFractionRing.injective V (FractionRing V) (by rw [← hi, ← hi, h])`. Establish `hnu : ∀ w : ν.valuationSubring, ν (w : FractionRing V) < 1 → ¬ IsUnit w` using `fun w hw hu => hw.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers ν)).mp hu)`. Use `haveI hil : IsLocalHom i := ⟨fun a ha => by`.

Assume the negation of the conclusion as `hna`. Conclude with `hnu (i a) (by rw [hi]; exact h2 a ((mem_maximalIdeal _).2 hna)) ha⟩`. Use `haveI := hgl`. Set `g' : ν.valuationSubring →+* FractionRing W'` to `(algebraMap W' (FractionRing W')).comp g`. Establish `hg' : Function.Injective g'` using `(IsFractionRing.injective W' (FractionRing W')).comp hg`.

Set `k : FractionRing V →+* FractionRing W'` to `IsFractionRing.lift (A := ν.valuationSubring) hg'`. Establish `hk : ∀ w : ν.valuationSubring, k (w : FractionRing V) = algebraMap W' (FractionRing W') (g w)` using `fun w => IsFractionRing.lift_algebraMap (A := ν.valuationSubring) hg' w`. Use `⟨W', inferInstance, inferInstance, inferInstance, hdvr, g.comp i, k, ⟨inferInstance, inferInstance, hc, hz⟩, hg.comp hiinj, inferInstance, fun v => by rw [← hi, hk]; rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `x y ⟨r, hr⟩`. Distinguish the cases in `hy : y = 0`.

Establish `: k x = 0` using `by rw [hr, hy, map_zero, mul_zero]`. Rewrite using `[(map_eq_zero_iff k k.injective).1 this, hy]`. Assume the negation of the conclusion as `hxy`. Rewrite `hxy` using `[not_le]`. Use `set z := x / y with hz'`.

Establish `hyν : ν y ≠ 0` using `(ν.ne_zero_iff).2 hy`. Establish `hz1 : 1 < ν z`. Rewrite using `[hz', map_div₀]`. Conclude with `(one_lt_div₀ (zero_lt_iff.2 hyν)).2 hxy`. Establish `hz0 : z ≠ 0`.

Introduce `h`. Rewrite `hz1` using `[h, map_zero]`. Conclude with `not_lt_zero' hz1`. Establish `hzi : ν z⁻¹ < 1`. Rewrite using `[map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ hz1`. Set `w : ν.valuationSubring` to `⟨z⁻¹, hzi.le⟩`. Establish `hkz : k z = algebraMap W' (FractionRing W') r`. Rewrite using `[hz', map_div₀, hr, mul_div_assoc, div_self ((map_ne_zero k).2 hy), mul_one]`. Establish `hkw : k (w : FractionRing V) = (k z)⁻¹`.

Express the relevant statement in the definitionally equal form `k z⁻¹ = _`. Rewrite using `[map_inv₀]`. Rewrite `hkw` using `[hk, hkz]`. Establish `hunit : IsUnit (g w)`. Establish `h : g w * r = 1`.

Apply `IsFractionRing.injective W' (FractionRing W')` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, hkw, inv_mul_cancel₀]`. Rewrite using `[← hkz]`. Conclude with `(map_ne_zero k).2 hz0`. Conclude with `⟨⟨g w, r, h, by rw [mul_comm]; exact h⟩, rfl⟩`.

Conclude with `hnu w hzi (IsUnit.of_map g w hunit)`.
-/
theorem exists_cdvr_valuation_le : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) → (∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1) → maximalIdeal V ≠ ⊥ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (k : FractionRing V →+* FractionRing V'), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ (∀ v : V, k (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (j v)) ∧ ∀ x y : FractionRing V, (∃ r : V', k x = algebraMap V' (FractionRing V') r * k y) → ν x ≤ ν y := by
  intro V _ _ _ hV ν h1 h2 hm
  obtain ⟨-, -, -, h0⟩ := hV
  obtain ⟨m, hmm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hmK : algebraMap V (FractionRing V) m ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hm0
  haveI : ν.IsNontrivial := ⟨algebraMap V (FractionRing V) m, (ν.ne_zero_iff).2 hmK, (h2 m hmm).ne⟩
  haveI : IsDiscreteValuationRing ν.valuationSubring := inferInstance
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_ringHom (IsFractionRing.injective V (FractionRing V))
  haveI : CharZero ν.valuationSubring :=
    RingHom.charZero (algebraMap ν.valuationSubring (FractionRing V))
  obtain ⟨W', _, _, _, g, hW', hg, hgl⟩ := GlobalTheory.LocalCompletion.exists_cDvr_embedding ν.valuationSubring
    inferInstance inferInstance (IsDiscreteValuationRing.ringKrullDim_eq_one _) inferInstance
  obtain ⟨hdvr, hc, hz⟩ := hW'

  let i : V →+* ν.valuationSubring := (algebraMap V (FractionRing V)).codRestrict ν.valuationSubring.toSubring (fun v => h1 v)
  have hi : ∀ v : V, ((i v : ν.valuationSubring) : FractionRing V) = algebraMap V (FractionRing V) v := fun _ => rfl
  have hiinj : Function.Injective i := fun a b h =>
    IsFractionRing.injective V (FractionRing V) (by rw [← hi, ← hi, h])

  have hnu : ∀ w : ν.valuationSubring, ν (w : FractionRing V) < 1 → ¬ IsUnit w := fun w hw hu =>
    hw.ne ((Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers ν)).mp hu)
  haveI hil : IsLocalHom i := ⟨fun a ha => by
    by_contra hna
    exact hnu (i a) (by rw [hi]; exact h2 a ((mem_maximalIdeal _).2 hna)) ha⟩
  haveI := hgl
  let g' : ν.valuationSubring →+* FractionRing W' := (algebraMap W' (FractionRing W')).comp g
  have hg' : Function.Injective g' :=
    (IsFractionRing.injective W' (FractionRing W')).comp hg
  let k : FractionRing V →+* FractionRing W' := IsFractionRing.lift (A := ν.valuationSubring) hg'
  have hk : ∀ w : ν.valuationSubring, k (w : FractionRing V) = algebraMap W' (FractionRing W') (g w) := fun w =>
    IsFractionRing.lift_algebraMap (A := ν.valuationSubring) hg' w
  refine ⟨W', inferInstance, inferInstance, inferInstance, hdvr, g.comp i, k, ⟨inferInstance, inferInstance, hc, hz⟩,
    hg.comp hiinj, inferInstance, fun v => by rw [← hi, hk]; rfl, ?_⟩
  rintro x y ⟨r, hr⟩
  by_cases hy : y = 0
  · have : k x = 0 := by rw [hr, hy, map_zero, mul_zero]
    rw [(map_eq_zero_iff k k.injective).1 this, hy]
  by_contra hxy
  rw [not_le] at hxy
  set z := x / y with hz'
  have hyν : ν y ≠ 0 := (ν.ne_zero_iff).2 hy
  have hz1 : 1 < ν z := by
    rw [hz', map_div₀]
    exact (one_lt_div₀ (zero_lt_iff.2 hyν)).2 hxy
  have hz0 : z ≠ 0 := by
    intro h; rw [h, map_zero] at hz1; exact not_lt_zero' hz1
  have hzi : ν z⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hz1
  let w : ν.valuationSubring := ⟨z⁻¹, hzi.le⟩
  have hkz : k z = algebraMap W' (FractionRing W') r := by
    rw [hz', map_div₀, hr, mul_div_assoc, div_self ((map_ne_zero k).2 hy), mul_one]
  have hkw : k (w : FractionRing V) = (k z)⁻¹ := by
    change k z⁻¹ = _
    rw [map_inv₀]
  rw [hk, hkz] at hkw
  have hunit : IsUnit (g w) := by
    have h : g w * r = 1 := by
      apply IsFractionRing.injective W' (FractionRing W')
      rw [map_mul, map_one, hkw, inv_mul_cancel₀]
      rw [← hkz]; exact (map_ne_zero k).2 hz0
    exact ⟨⟨g w, r, h, by rw [mul_comm]; exact h⟩, rfl⟩
  exact hnu w hzi (IsUnit.of_map g w hunit)

end GlobalTheory.DivBound
