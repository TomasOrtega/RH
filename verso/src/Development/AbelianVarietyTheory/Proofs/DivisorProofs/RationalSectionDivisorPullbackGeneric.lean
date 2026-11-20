import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModpFramesPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.MultPull

open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull

/- English proof (translation)
Introduce `c c' h`. Establish `l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit))` using `fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩`. Establish `h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit))` using `l h`. Establish `h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)` using `(genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁`. Establish `e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit)))`.

Express the relevant statement in the definitionally equal form `∏ _k : PUnit, _ = _`. Conclude with `(Fintype.prod_unique _).trans (zpow_one _)`. Express the relevant statement in the definitionally equal form `fnMap j hη (r (c PUnit.unit) : X.functionField) = fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) * fnMap j hη (r (c' PUnit.unit) : X.functionField)`. Rewrite using `[hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]`. Use `first`.

Consider the case `exact congrArg (· * _) (fnOf_resG l h _)`. Consider the case `exact congrArg (· * _) (fnOf_resG l h _).symm`.
-/
theorem isRatSec_pull_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) :
    IsRatSec (L.pull j) fun c => Units.map (fnMap j hη).toMonoidHom (r (c PUnit.unit)) := by
  intro c c' h
  have l : (L.pull j).U c ⊓ (L.pull j).U c' ≤ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have h₁ : genericPoint Y ∈ j ⁻¹ᵁ (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)) := l h
  have h₀ : genericPoint X ∈ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    (genericPoint_specializes _).mem_open (L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit)).isOpen h₁
  have e : (L.pull j).g c c' = res l (pullU j _ (L.g (c PUnit.unit) (c' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  change fnMap j hη (r (c PUnit.unit) : X.functionField) =
    fnOf _ h ((L.pull j).g c c' : Γ(Y, (L.pull j).U c ⊓ (L.pull j).U c')) *
      fnMap j hη (r (c' PUnit.unit) : X.functionField)
  rw [hr _ _ h₀, map_mul, fnMap_fnOf j hη h₀ h₁, e]
  first
    | exact congrArg (· * _) (fnOf_resG l h _)
    | exact congrArg (· * _) (fnOf_resG l h _).symm

/- English proof (translation)
Set `e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y` to `(asIso (j.stalkMap y)).commRingCatIsoToRingEquiv`. Establish `he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a` using `rfl`. Establish `hc : Order.coheight y = Order.coheight (j y)`. Use `ringKrullDim_eq_of_ringEquiv e` as an intermediate fact. Rewrite `this` using `[ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]`.

Conclude with `this.symm` after adjusting the coercions. Distinguish the cases in `hz : Order.coheight (j y) = 1`. Use `swap`. Rewrite using `[Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]`. Establish `hz' : Order.coheight y = 1` using `hc.trans hz`.

Establish `key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) : Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y = Scheme.ord (algebraMap _ X.functionField a) (j y)`. Establish `ha' : j.stalkMap y a ≠ 0` using `by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha`. Rewrite using `[fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]`. Conclude with `congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)`. Distinguish the cases in `hf : f = 0`.

Simplify using `[hf]`. Take `⟨a, b, hb, hab⟩` from `IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hb' : algebraMap _ X.functionField b ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hf (by rw [← hab, map_zero, zero_div])`. Establish `hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a`. Rewrite using `[← hab, div_mul_cancel₀ _ hb']`. Establish `h₁` using `Scheme.ord_mul (x := j y) hf hb'`.

Establish `hfm : fnMap j hη f ≠ 0` using `(map_ne_zero_iff _ (fnMap j hη).injective).2 hf`. Establish `hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0` using `(map_ne_zero_iff _ (fnMap j hη).injective).2 hb'`. Establish `h₂` using `Scheme.ord_mul (x := y) hfm hbm`. Rewrite `h₂` using `[← map_mul, hfb]`. Rewrite `h₁` using `[hfb]`.

Rewrite `h₂` using `[key a ha0, key b hb0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem ord_fnMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) (y : Y)
    [IsIso (j.stalkMap y)] (f : X.functionField) :
    Scheme.ord (fnMap j hη f) y = Scheme.ord f (j y) := by
  let e : X.presheaf.stalk (j y) ≃+* Y.presheaf.stalk y :=
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  have he (a : X.presheaf.stalk (j y)) : e a = j.stalkMap y a := rfl
  have hc : Order.coheight y = Order.coheight (j y) := by
    have := ringKrullDim_eq_of_ringEquiv e
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at this
    exact_mod_cast this.symm
  by_cases hz : Order.coheight (j y) = 1
  swap
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one (hc ▸ hz), Scheme.ord_eq_zero_of_coheight_neq_one hz]
  have hz' : Order.coheight y = 1 := hc.trans hz
  have key (a : X.presheaf.stalk (j y)) (ha : a ≠ 0) :
      Scheme.ord (fnMap j hη (algebraMap _ X.functionField a)) y =
        Scheme.ord (algebraMap _ X.functionField a) (j y) := by
    have ha' : j.stalkMap y a ≠ 0 := by rw [← he]; exact (map_ne_zero_iff _ e.injective).2 ha
    rw [fnMap_algebraMap, ord_algebraMap hz' ha', ord_algebraMap hz ha, ← he]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) (ord_map_ringEquiv e a)
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (j y)) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap _ X.functionField b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (by rw [← hab, map_zero, zero_div])
  have hfb : f * algebraMap _ X.functionField b = algebraMap _ X.functionField a := by
    rw [← hab, div_mul_cancel₀ _ hb']
  have h₁ := Scheme.ord_mul (x := j y) hf hb'
  have hfm : fnMap j hη f ≠ 0 := (map_ne_zero_iff _ (fnMap j hη).injective).2 hf
  have hbm : fnMap j hη (algebraMap _ X.functionField b) ≠ 0 :=
    (map_ne_zero_iff _ (fnMap j hη).injective).2 hb'
  have h₂ := Scheme.ord_mul (x := y) hfm hbm
  rw [← map_mul, hfb] at h₂
  rw [hfb] at h₁
  rw [key a ha0, key b hb0] at h₂
  omega

end GlobalTheory.MultPull

open GlobalTheory.MultPull GlobalTheory.TrueGeo.SmallSec in

/- English proof (translation)
Introduce `G Y _ _ _ _ j hj hiso M hM r hr`. Establish `hη : j (genericPoint G) ⤳ genericPoint Y` using `hj ▸ specializes_rfl`. Use `⟨_, isRatSec_pull_map j hη hr, fun x => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_chart (LB.isLB_pull hM j) x`. Establish `hc' : j x ∈ M.U (c PUnit.unit)` using `Set.mem_iInter.1 hc PUnit.unit`.

Rewrite using `[((presents_divOfRatSec _ _).isEqn c x hc).mult_eq, ((presents_divOfRatSec hM hr).isEqn _ _ hc').mult_eq]`. Use `hiso x` as an intermediate fact. Conclude with `ord_fnMap j hη x _`.
-/
theorem GlobalTheory.MultPull.exists_isRatSec_pull_mult : ∀ (G Y : Scheme.{0}) [IsIntegral G] [IsIntegral Y] [IsLocallyNoetherian G] [IsLocallyNoetherian Y] (j : G ⟶ Y), j (genericPoint G) = genericPoint Y → (∀ x : G, IsIso (j.stalkMap x)) → ∀ (M : LB Y) (hM : M.IsLB) (r : M.ι → Y.functionFieldˣ) (hr : IsRatSec M r), ∃ (r' : (M.pull j).ι → G.functionFieldˣ) (hr' : IsRatSec (M.pull j) r'), ∀ x : G, (divOfRatSec (LB.isLB_pull hM j) hr').mult x = (divOfRatSec hM hr).mult (j x) := by
  intro G Y _ _ _ _ j hj hiso M hM r hr
  have hη : j (genericPoint G) ⤳ genericPoint Y := hj ▸ specializes_rfl
  refine ⟨_, isRatSec_pull_map j hη hr, fun x => ?_⟩
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull hM j) x
  have hc' : j x ∈ M.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c x hc).mult_eq,
    ((presents_divOfRatSec hM hr).isEqn _ _ hc').mult_eq]
  have := hiso x
  exact ord_fnMap j hη x _
