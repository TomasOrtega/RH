import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.ScaleEqv

/- English proof (translation)
Introduce `R _ _ D A F _ _ N lab E h c`. Set `gg : F →+* Γ((TFK (R` to `R) F ⊗ A.A).left, ⊤) := (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom`. Establish `hgg : ∀ u : F, gg u = (fst (TFK (R` using `R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl`. Establish `inv1 : ∀ (W : (TFK (R` using `R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by`. Introduce `W u`.

Simplify using `only [resTop]`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Set `S : F → SecK A.L (snd (TFK (R` to `R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N := fun u t => DVR.SecOps.secScale (gg u) t`. Establish `Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j` using `fun _ _ _ => rfl`. Establish `SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t`.

Introduce `u t`. Apply `DVR.SecOps.sec_ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]`. Establish `SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t`.

Introduce `u t`. Use `SS u⁻¹ t` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis. Use `⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce `s t hst`. Apply `h.bij.1` to reduce the goal to its premises. Use `congrArg (S (c⁻¹).val) hst` as an intermediate fact. Simplify `this` using `only [SS']`. Introduce `t`.

Take `⟨s, hs⟩` from `h.bij.2 (S (c⁻¹).val t)`. Conclude with `⟨s, by simp only [hs, SS]⟩`. Introduce `s s' s'' hs j`. Simplify using `only [Sf]`. Rewrite using `[h.add s s' s'' hs j, mul_add]`.

Introduce `u s s' hs j`. Simplify using `only [Sf]`. Rewrite using `[h.smul u s s' hs j, mul_left_comm]`. Introduce `p w θ s s' hw hθ hph j`. Establish `key` using `h.act p w θ s s' hw hθ hph j`.

Establish `e : (translT A.A θ.pt).left ≫ (fst (TFK (R` using `R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by`. Rewrite using `[← Over.comp_left, translT, lift_fst]`. Establish `hψ : ∀ (W : (TFK (R` using `R) F ⊗ A.A).left.Opens), ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) = resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by`. Introduce `W`. Simplify using `only [resTop]`.

Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]`. Use `congr 1`. Rewrite using `[hgg]`. Establish `hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R` using `R) F) A.A).left.appTop).hom (fnF F c.val)) = ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]`.

Conclude with `hT`. Use `erw [Sf, Sf]`. Use `erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]`.
-/
theorem eqv_scale : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) lab E, Eqv D A F N lab E → ∀ c : Fˣ, ∃ E', Eqv D A F N lab E' ∧ ∀ s j, (E' s).f j = liftFun A.A _ (fnF F c.val) * (E s).f j := by
  intro R _ _ D A F _ _ N lab E h c
  let gg : F →+* Γ((TFK (R := R) F ⊗ A.A).left, ⊤) :=
    (fst (TFK (R := R) F) A.A).left.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hgg : ∀ u : F, gg u = (fst (TFK (R := R) F) A.A).left.appTop.hom (fnF F u) := fun _ => rfl
  have inv1 : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens) (u : Fˣ), resTop W (gg u.val) * resTop W (gg (u⁻¹).val) = 1 := by
    intro W u
    simp only [resTop]
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  let S : F → SecK A.L (snd (TFK (R := R) F) A.A).left N → SecK A.L (snd (TFK (R := R) F) A.A).left N :=
    fun u t => DVR.SecOps.secScale (gg u) t
  have Sf : ∀ u t j, (S u t).f j = resTop _ (gg u) * t.f j := fun _ _ _ => rfl
  have SS : ∀ (u : Fˣ) t, S u.val (S (u⁻¹).val t) = t := by
    intro u t
    apply DVR.SecOps.sec_ext
    intro j
    rw [Sf, Sf, ← _root_.mul_assoc, inv1, _root_.one_mul]
  have SS' : ∀ (u : Fˣ) t, S (u⁻¹).val (S u.val t) = t := by
    intro u t
    have := SS u⁻¹ t
    rwa [inv_inv] at this
  refine ⟨fun s => S c.val (E s), ⟨?_, ?_, ?_, h.onto, h.frame, h.lift, ?_⟩, fun s j => rfl⟩
  · constructor
    · intro s t hst
      apply h.bij.1
      have := congrArg (S (c⁻¹).val) hst
      simpa only [SS'] using this
    · intro t
      obtain ⟨s, hs⟩ := h.bij.2 (S (c⁻¹).val t)
      exact ⟨s, by simp only [hs, SS]⟩
  · intro s s' s'' hs j
    simp only [Sf]
    rw [h.add s s' s'' hs j, mul_add]
  · intro u s s' hs j
    simp only [Sf]
    rw [h.smul u s s' hs j, mul_left_comm]
  · intro p w θ s s' hw hθ hph j
    have key := h.act p w θ s s' hw hθ hph j
    have e : (translT A.A θ.pt).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A.A).left := by
      rw [← Over.comp_left, translT, lift_fst]
    have hψ : ∀ (W : (TFK (R := R) F ⊗ A.A).left.Opens),
        ((translT A.A θ.pt).left.app W).hom (resTop W (gg c.val)) =
          resTop ((translT A.A θ.pt).left ⁻¹ᵁ W) (gg c.val) := by
      intro W
      simp only [resTop]
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      congr 1
      rw [hgg]
      have hT : ((translT A.A θ.pt).left.appTop).hom (((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val)) =
          ((fst (TFK (R := R) F) A.A).left.appTop).hom (fnF F c.val) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e]
      exact hT
    erw [Sf, Sf]
    erw [map_mul, map_mul, map_mul, hψ, key, DVR.SecOps.resTop_res, DVR.SecOps.resTop_res, mul_left_comm]

end GlobalTheory.Mum.ScaleEqv
