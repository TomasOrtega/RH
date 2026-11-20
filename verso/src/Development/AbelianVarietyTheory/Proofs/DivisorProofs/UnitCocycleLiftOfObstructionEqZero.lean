import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

def unitOneSub {B : Type} [CommRing B] (w : B) (h : w * w = 0) : Bˣ where
  val := 1 - w
  inv := 1 + w
  val_inv := by linear_combination (-1 : B) * h
  inv_val := by linear_combination (-1 : B) * h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unitOneSub_val {B : Type} [CommRing B] (w : B) (h : w * w = 0) : (unitOneSub w h : B) = 1 - w := rfl

/- English proof (translation)
Establish `h` using `Ideal.mul_mem_mul hx hy`. Rewrite `h` using `[← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot]`. Simplify using `using h`.
-/
theorem mul_eq_zero_of_mem {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {x y : B} (hx : x ∈ I.map (algebraMap R B)) (hy : y ∈ I.map (algebraMap R B)) : x * y = 0 := by
  have h := Ideal.mul_mem_mul hx hy
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u h`. Take `⟨v, σ, z, hv, hσ, hz, hzv⟩` from `h`. Take `⟨f, hf⟩` from `(H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm`. Establish `hw : ∀ (T T' : C) (a : T ⟶ T'), σ T' (f T T' a) ∈ I.map (algebraMap R (L.B T'))` using `fun T T' a ↦ (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T') (σ T') (hσ T')).1 _`. Use `⟨fun T T' a ↦ v T T' a * unitOneSub (σ T' (f T T' a)) (mul_eq_zero_of_mem hI (hw T T' a) (hw T T' a)), fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩` and prove the remaining obligations.

Establish `h0 : L.p T' (σ T' (f T T' a)) = 0` using `(L.ker T' _).2 (hw T T' a)`. Simplify using `only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one, h0, sub_zero, mul_one, hv]`. Conclude with `mul_one _`. Establish `hnat` using `(GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T') (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b) (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)`. Establish `e` using `congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b`.

Establish `hs : σ T'' (z.1 T T' T'' a b) = L.ρ b (σ T' (f T T' a)) - σ T'' (f T T'' (a ≫ b)) + σ T'' (f T' T'' b)`. Rewrite using `[← e, d1_apply, map_add, map_sub, hnat]`. Both sides reduce to the same expression. Establish `hx` using `hw T T' a`. Establish `hρx : L.ρ b (σ T' (f T T' a)) ∈ I.map (algebraMap R (L.B T''))`.

Rewrite using `[hnat]`. Conclude with `(GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (σ T'') (hσ T'')).1 _`. Establish `hW` using `hw T T'' (a ≫ b)`. Establish `hy` using `hw T' T'' b`. Use `set x := L.ρ b (σ T' (f T T' a)) with hxdef`.

Use `set W := σ T'' (f T T'' (a ≫ b))`. Use `set y := σ T'' (f T' T'' b)`. Establish `hxx` using `mul_eq_zero_of_mem hI hρx hρx`. Establish `hxy` using `mul_eq_zero_of_mem hI hρx hy`. Establish `hyy` using `mul_eq_zero_of_mem hI hy hy`.

Establish `hWx` using `mul_eq_zero_of_mem hI hW hρx`. Establish `hWy` using `mul_eq_zero_of_mem hI hW hy`. Establish `key : (1 + (x - W + y)) * ((1 - x) * (1 - y)) = 1 - W`. Take the linear combination `-hxx - hxy - hyy + hWx + hWy + y * hxx - y * hWx + y * hxy`. Establish `hz'` using `(hzv T T' T'' a b).2`.

Simplify using `only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one]`. Rewrite using `[← hxdef]`. Take the linear combination `(-(1 - x) * (1 - y)) * hz' + (-(v T T'' (a ≫ b) : L.B T'') * (1 - x) * (1 - y)) * hs - (v T T'' (a ≫ b) : L.B T'') * key`.
-/
theorem lift_of_isObU_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ), IsObU L α u 0 → ∃ v : ∀ (T T' : C) (_ : T ⟶ T'), (L.B T')ˣ, (∀ T T' a, L.p T' (v T T' a : L.B T') = (u T T' a : F.obj T')) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), (v T T'' (a ≫ b) : L.B T'') = L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u h
  obtain ⟨v, σ, z, hv, hσ, hz, hzv⟩ := h
  obtain ⟨f, hf⟩ := (H2.mk_eq_zero (F := ext R₁ F)).1 hz.symm
  have hw : ∀ (T T' : C) (a : T ⟶ T'), σ T' (f T T' a) ∈ I.map (algebraMap R (L.B T')) := fun T T' a ↦
    (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (σ T') (hσ T')).1 _
  refine ⟨fun T T' a ↦ v T T' a * unitOneSub (σ T' (f T T' a)) (mul_eq_zero_of_mem hI (hw T T' a) (hw T T' a)),
    fun T T' a ↦ ?_, fun T T' T'' a b ↦ ?_⟩
  · have h0 : L.p T' (σ T' (f T T' a)) = 0 := (L.ker T' _).2 (hw T T' a)
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one, h0, sub_zero, mul_one, hv]
    exact mul_one _
  · have hnat := (GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α (L.B T') (F.obj T') (L.p T') (L.semi T') (L.surj T')
      (L.ker T') (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'') (L.ker T'') (L.ρ b) (mp F b)
      (L.nat b) (σ T') (σ T'') (hσ T') (hσ T'')).1 (f T T' a)
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b
    have hs : σ T'' (z.1 T T' T'' a b) = L.ρ b (σ T' (f T T' a)) - σ T'' (f T T'' (a ≫ b)) + σ T'' (f T' T'' b) := by
      rw [← e, d1_apply, map_add, map_sub, hnat]
      rfl
    have hx := hw T T' a
    have hρx : L.ρ b (σ T' (f T T' a)) ∈ I.map (algebraMap R (L.B T'')) := by
      rw [hnat]
      exact (GlobalTheory.Obs.sig_basic R R₀ I hI π hπ hk R₁ α (L.B T'') (F.obj T'') (L.p T'') (L.semi T'') (L.surj T'')
        (L.ker T'') (σ T'') (hσ T'')).1 _
    have hW := hw T T'' (a ≫ b)
    have hy := hw T' T'' b
    set x := L.ρ b (σ T' (f T T' a)) with hxdef
    set W := σ T'' (f T T'' (a ≫ b))
    set y := σ T'' (f T' T'' b)
    have hxx := mul_eq_zero_of_mem hI hρx hρx
    have hxy := mul_eq_zero_of_mem hI hρx hy
    have hyy := mul_eq_zero_of_mem hI hy hy
    have hWx := mul_eq_zero_of_mem hI hW hρx
    have hWy := mul_eq_zero_of_mem hI hW hy
    have key : (1 + (x - W + y)) * ((1 - x) * (1 - y)) = 1 - W := by
      linear_combination -hxx - hxy - hyy + hWx + hWy + y * hxx - y * hWx + y * hxy
    have hz' := (hzv T T' T'' a b).2
    simp only [Units.val_mul, unitOneSub_val, map_mul, map_sub, map_one]
    rw [← hxdef]
    linear_combination (-(1 - x) * (1 - y)) * hz' + (-(v T T'' (a ≫ b) : L.B T'') * (1 - x) * (1 - y)) * hs
      - (v T T'' (a ≫ b) : L.B T'') * key

end GlobalTheory.LBLift
