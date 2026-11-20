import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.NotIsGlobalPrimePow

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LevelZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.Models GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

/- English proof (translation)
Establish `ha' : (a : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 ha.ne'`. Establish `hc' : (c : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hc.ne'`. Rewrite using `[zeta, zeta, ← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem zeta_mul_pow {a c : ℕ} (ha : 0 < a) (hc : 0 < c) : zeta (a * c) ^ c = zeta a := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha.ne'
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/- English proof (translation)
Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `x (rfl | rfl)`. Conclude with `IntermediateField.subset_adjoin _ _ (by simp)`. Take `⟨c, hc⟩` from `h`. Establish `hc0 : 0 < c` using `Nat.pos_of_ne_zero fun h0 => l₂.A_pos.ne' (by rw [hc, h0, mul_zero])`.

Rewrite using `[← zeta_mul_pow l.A_pos hc0, ← hc]`. Conclude with `pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _`.
-/
theorem KA_le {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l ≤ KA l₂ := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · obtain ⟨c, hc⟩ := h
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h0 => l₂.A_pos.ne' (by rw [hc, h0, mul_zero])
    rw [← zeta_mul_pow l.A_pos hc0, ← hc]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

def simOne (hD : D.p + D.q = 0) : Sim D :=
  have := subsingleton_La hD
  { f := fun _ => LinearMap.id
    ν := fun _ => 1
    tower := fun _ _ _ _ _ => ⟨0, Subsingleton.elim _ _⟩
    inv := fun _ _ => ⟨LinearMap.id, fun _ => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
    mult := fun _ _ a b => by
      rw [Subsingleton.elim b 0]
      simp }

/- English proof (translation)
Use `subsingleton_La hD` as an intermediate fact. Use `⟨by simp [simOne], fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim ((simOne hD).f l.M a - a) 0]`. Conclude with `zero_mem _`.
-/
theorem simOne_inGam (hD : D.p + D.q = 0) (l l₂ : Level H) : (simOne hD).InGam l l₂ := by
  have := subsingleton_La hD
  refine ⟨by simp [simOne], fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim ((simOne hD).f l.M a - a) 0]
  exact zero_mem _

/- English proof (translation)
Use `subsingleton_La hD` as an intermediate fact. Use `⟨fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim (g.f l₂.M a - a) 0]`. Conclude with `zero_mem _`.
-/
theorem trivAt (hD : D.p + D.q = 0) (g : Sim D) (l₂ : Level H) : g.TrivAt l₂ := by
  have := subsingleton_La hD
  refine ⟨fun a => ?_, fun a => ⟨0, Subsingleton.elim _ _⟩⟩
  rw [Subsingleton.elim (g.f l₂.M a - a) 0]
  exact zero_mem _

/- English proof (translation)
Substitute `h` using the available equality. Establish `: (IntermediateField.inclusion (le_refl F)).toRingHom = RingHom.id F` using `RingHom.ext fun _ => rfl`. Rewrite using `[this]`. Establish `e : spMap (RingHom.id F) = 𝟙 _` using `Spec.map_id _`. Rewrite using `[e]`.

Use `infer_instance`.
-/
theorem isIso_spMap_inclusion {F F' : IntermediateField ℚ ℂ} (h : F = F') :
    IsIso (spMap (IntermediateField.inclusion h.le).toRingHom) := by
  subst h
  have : (IntermediateField.inclusion (le_refl F)).toRingHom = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this]
  have e : spMap (RingHom.id F) = 𝟙 _ := Spec.map_id _
  rw [e]
  infer_instance

def jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) : KA l →+* KA l₂ := (IntermediateField.inclusion (KA_le h)).toRingHom

/- English proof (translation)
The claim follows from `IntermediateField.coe_inclusion (KA_le h) x`.
-/
theorem coe_jKA {l l₂ : Level H} (h : l.A ∣ l₂.A) (x : KA l) : ((jKA h x : KA l₂) : ℂ) = ((x : KA l) : ℂ) :=
  IntermediateField.coe_inclusion (KA_le h) x

/- English proof (translation)
Rewrite using `[RankZero.spMap_comp, RankZero.spMap_comp]`. Conclude with `congrArg spMap (RingHom.ext fun x => Subtype.ext rfl)`.
-/
theorem spMap_square {l l₂ : Level H} (h : l.A ∣ l₂.A) (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) :
    spMap (IntermediateField.inclusion c₂.le).toRingHom ≫ spMap (jKA h) =
      spMap (IntermediateField.inclusion hc.le).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [RankZero.spMap_comp, RankZero.spMap_comp]
  exact congrArg spMap (RingHom.ext fun x => Subtype.ext rfl)

/- English proof (translation)
Establish `hw : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s = (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_square h c c₂ hc, Category.assoc]`. Establish `h₂` using `pullback.lift_snd _ _ hw`. Use `isIso_spMap_inclusion hc` as an intermediate fact. Conclude with `⟨pullback.lift _ _ hw, pullback.lift_fst _ _ hw, h₂, IsIso.of_isIso_fac_right h₂⟩`.
-/
theorem exists_isIso_rF {l l₂ : Level H} (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hs : IsIso Xo.s) (hs₂ : IsIso Xo₂.s)
    (h : l.A ∣ l₂.A) (r : Xo₂.X ⟶ Xo.X) (hr : r ≫ Xo.s = Xo₂.s ≫ spMap (jKA h)) (c : Coeff l) (c₂ : Coeff l₂)
    (hc : c.F = c₂.F) : ∃ rF : Xo₂.XF c₂ ⟶ Xo.XF c,
      rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r ∧
      rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom ∧ IsIso rF := by
  have hw : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, spMap_square h c c₂ hc, Category.assoc]
  have h₂ := pullback.lift_snd _ _ hw
  have := isIso_spMap_inclusion hc
  exact ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ hw, h₂, IsIso.of_isIso_fac_right h₂⟩

/- English proof (translation)
Introduce `l l₂ Xo Xo₂ hd`. Take `⟨hs, hG⟩` from `isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo`. Take `⟨hs₂, hG₂⟩` from `isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂`. Take `⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (jKA hd.2.2)` from `⟨Xo₂.s ≫ spMap (jKA hd.2.2) ≫ inv Xo.s, by simp⟩`. Take `⟨m⟩` from `nonempty_sabMap hG₂ hG r`.

Take `⟨ν⟩` from `nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom`. Establish `hlev : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _)` using `fun g => ⟨Category.id_comp _, ν, fun a => sec_comm hG₂ ν.cart.1.w _ _, fun a => sec_comm hG₂ ν.cart.1.w _ _⟩`. Use `⟨r, jKA hd.2.2, m, coe_jKA _, hr, fun a => sec_comm hG m.cart.1.w _ _, fun a => sec_comm hG m.cart.1.w _ _, fun g _ => ⟨Iso.refl _, hlev g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩` and prove the remaining obligations. Take `⟨rF, h₁, h₂, hF⟩` from `exists_isIso_rF Xo Xo₂ hs hs₂ hd.2.2 r hr c c₂ hc`. Use `⟨rF, h₁, h₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ?_⟩` and prove the remaining obligations.

Take `rfl : y = y'` from `(cancel_mono rF).1 h`. Conclude with `⟨⟨simOne hD, Iso.refl _, simOne_inGam hD l l₂, hlev _, Category.id_comp _, by simp only [Iso.refl_hom, Category.comp_id]⟩, fun g _ _ _ _ => trivAt hD g l₂⟩`.
-/
theorem lev_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (jKA hd.2.2) :=
    ⟨Xo₂.s ≫ spMap (jKA hd.2.2) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
  have hlev : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g =>
    ⟨Category.id_comp _, ν, fun a => sec_comm hG₂ ν.cart.1.w _ _, fun a => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, jKA hd.2.2, m, coe_jKA _, hr, fun a => sec_comm hG m.cart.1.w _ _, fun a => sec_comm hG m.cart.1.w _ _,
    fun g _ => ⟨Iso.refl _, hlev g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  obtain ⟨rF, h₁, h₂, hF⟩ := exists_isIso_rF Xo Xo₂ hs hs₂ hd.2.2 r hr c c₂ hc
  refine ⟨rF, h₁, h₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ?_⟩
  obtain rfl : y = y' := (cancel_mono rF).1 h
  exact ⟨⟨simOne hD, Iso.refl _, simOne_inGam hD l l₂, hlev _, Category.id_comp _,
    by simp only [Iso.refl_hom, Category.comp_id]⟩, fun g _ _ _ _ => trivAt hD g l₂⟩

/- English proof (translation)
Introduce `_ _ _ _ _ _ hD` and use `⟨lev_rank_zero hD, GoodModel.hecke_rank_zero hD⟩`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D) :=
  fun _ _ _ _ _ _ hD => ⟨lev_rank_zero hD, GoodModel.hecke_rank_zero hD⟩

end GlobalTheory.CompanionTheory.Ar.Top.LevelZero

end
