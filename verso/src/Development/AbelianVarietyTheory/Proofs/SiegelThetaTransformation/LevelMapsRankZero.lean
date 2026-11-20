import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Models.RankZero

namespace GlobalTheory.LevelMapsAnyRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

def unitSim (D : Datum H) : Sim D where
  f _ := LinearMap.id
  ν _ := 1
  tower _ _ _ _ _ := ⟨0, by simp⟩
  inv _ _ := ⟨LinearMap.id, fun _ => ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩⟩
  mult _ _ _ _ := by simp

/- English proof (translation)
Introduce `l l₂ Xo Xo₂ hd`. Establish `hsub` using `subsingleton_La hD`. Take `⟨hs, hG⟩` from `isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo`. Take `⟨hs₂, hG₂⟩` from `isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂`. Establish `hA : l.A ∣ l₂.A` using `hd.2.2`.

Take `⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (levelFieldIncl hA)` from `⟨(Xo₂.s ≫ spMap (levelFieldIncl hA)) ≫ inv Xo.s, by simp⟩`. Take `⟨m⟩` from `nonempty_sabMap hG₂ hG r`. Establish `haut : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _)` using `fun g => by`. Take `⟨ν⟩` from `nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom`. Conclude with `⟨Category.id_comp _, ν, fun _ => sec_comm hG₂ ν.cart.1.w _ _, fun _ => sec_comm hG₂ ν.cart.1.w _ _⟩`.

Use `⟨r, levelFieldIncl hA, m, coe_levelFieldIncl hA, hr, fun _ => sec_comm hG m.cart.1.w _ _, fun _ => sec_comm hG m.cart.1.w _ _, fun g _ => ⟨Iso.refl _, haut g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩` and prove the remaining obligations. Establish `hring : (IntermediateField.inclusion c₂.le).toRingHom.comp (levelFieldIncl hA) = (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom`. Use extensionality with `x`. Conclude with `coe_levelFieldIncl hA x`. Establish `w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s = (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ spMap (IntermediateField.inclusion hc.le).toRingHom) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`.

Rewrite using `[Category.assoc, hr, pullback.condition_assoc, Category.assoc, GlobalTheory.Models.RankZero.spMap_comp, GlobalTheory.Models.RankZero.spMap_comp, hring]`. Establish `e₁` using `pullback.lift_fst _ _ w`. Establish `e₂` using `pullback.lift_snd _ _ w`. Establish `i₀ : IsIso (spMap (IntermediateField.inclusion hc.le).toRingHom)`. Establish `: IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom)` using `(ConcreteCategory.isIso_iff_bijective _).2 ⟨IntermediateField.inclusion_injective hc.le, fun x => ⟨⟨x.1, hc.ge x.2⟩, rfl⟩⟩`.

Conclude with `inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom)))`. Establish `i₁ : IsIso (pullback.lift _ _ w)` using `IsIso.of_isIso_fac_right e₂`. Use `⟨pullback.lift _ _ w, e₁, e₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `rfl` from `(cancel_mono _).1 h`. Conclude with `⟨unitSim D, Iso.refl _, ⟨by simp [unitSim], fun a => by rw [Subsingleton.elim (_ - a) 0]; exact zero_mem _, fun a => ⟨0, Subsingleton.elim _ _⟩⟩, haut _, Category.id_comp _, congrArg (y ≫ ·) (Category.comp_id _).symm⟩`.

Introduce `g _ _ _ _`. Conclude with `⟨fun a => by rw [Subsingleton.elim (g.f l₂.M a - a) 0]; exact zero_mem _, fun a => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem levelMaps_rank_zero (hD : D.p + D.q = 0) : ToroidalLevelCompatibility (H := H) (D := D) := by
  intro l l₂ Xo Xo₂ hd
  have hsub := subsingleton_La hD
  obtain ⟨hs, hG⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo
  obtain ⟨hs₂, hG₂⟩ := isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo₂
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨r, hr⟩ : ∃ r : Xo₂.X ⟶ Xo.X, r ≫ Xo.s = Xo₂.s ≫ spMap (levelFieldIncl hA) :=
    ⟨(Xo₂.s ≫ spMap (levelFieldIncl hA)) ≫ inv Xo.s, by simp⟩
  obtain ⟨m⟩ := nonempty_sabMap hG₂ hG r
  have haut : ∀ g : Sim D, Xo₂.LevAut g (Iso.refl _) := fun g => by
    obtain ⟨ν⟩ := nonempty_sabMap hG₂ hG₂ (Iso.refl Xo₂.X).hom
    exact ⟨Category.id_comp _, ν, fun _ => sec_comm hG₂ ν.cart.1.w _ _, fun _ => sec_comm hG₂ ν.cart.1.w _ _⟩
  refine ⟨r, levelFieldIncl hA, m, coe_levelFieldIncl hA, hr, fun _ => sec_comm hG m.cart.1.w _ _,
    fun _ => sec_comm hG m.cart.1.w _ _, fun g _ => ⟨Iso.refl _, haut g, Category.id_comp _⟩, fun c c₂ hc => ?_⟩
  have hring : (IntermediateField.inclusion c₂.le).toRingHom.comp (levelFieldIncl hA) =
      (IntermediateField.inclusion hc.le).toRingHom.comp (IntermediateField.inclusion c.le).toRingHom := by
    ext x
    exact coe_levelFieldIncl hA x
  have w : (pullback.fst Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫ r) ≫ Xo.s =
      (pullback.snd Xo₂.s (spMap (IntermediateField.inclusion c₂.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hc.le).toRingHom) ≫
        spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [Category.assoc, hr, pullback.condition_assoc, Category.assoc, GlobalTheory.Models.RankZero.spMap_comp,
      GlobalTheory.Models.RankZero.spMap_comp, hring]
  have e₁ := pullback.lift_fst _ _ w
  have e₂ := pullback.lift_snd _ _ w
  have i₀ : IsIso (spMap (IntermediateField.inclusion hc.le).toRingHom) := by
    have : IsIso (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).2 ⟨IntermediateField.inclusion_injective hc.le,
        fun x => ⟨⟨x.1, hc.ge x.2⟩, rfl⟩⟩
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (IntermediateField.inclusion hc.le).toRingHom)))
  have i₁ : IsIso (pullback.lift _ _ w) := IsIso.of_isIso_fac_right e₂
  refine ⟨pullback.lift _ _ w, e₁, e₂, inferInstance, inferInstance, inferInstance, fun k _ _ y y' h => ⟨?_, ?_⟩⟩
  · obtain rfl := (cancel_mono _).1 h
    exact ⟨unitSim D, Iso.refl _, ⟨by simp [unitSim], fun a => by rw [Subsingleton.elim (_ - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩, haut _, Category.id_comp _,
      congrArg (y ≫ ·) (Category.comp_id _).symm⟩
  · intro g _ _ _ _
    exact ⟨fun a => by rw [Subsingleton.elim (g.f l₂.M a - a) 0]; exact zero_mem _,
      fun a => ⟨0, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos (D.p + D.q) with h | h` into its components or cases. Conclude with `levelMaps_rank_zero h`. Conclude with `(GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h).1`.
-/
theorem levelMaps (D : Datum H) : ToroidalLevelCompatibility (H := H) (D := D) := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · exact levelMaps_rank_zero h
  · exact (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H D h).1

end GlobalTheory.LevelMapsAnyRank
