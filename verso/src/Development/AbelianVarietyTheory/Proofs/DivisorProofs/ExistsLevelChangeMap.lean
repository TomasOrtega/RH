import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

namespace GlobalTheory.LevelMapBase

/- English proof (translation)
Introduce `E _ _ _ H Dw l l' Xo Xo' c c' hle hpq hd`. Take `⟨r₀, jK, m, hk, -, -, -, -, hc⟩` from `(GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l l' Xo Xo' hd`. Establish `hle₁ : KA l ≤ c'.F` using `fun x hx => by`. Use `c'.le (jK ⟨x, hx⟩).2` as an intermediate fact. Rewrite `this` using `[hk]`. Then use the resulting hypothesis.

Set `c₁ : Coeff l` to `{ F := c'.F fin := c'.fin conj := c'.conj zeta_mem := by`. Take `⟨e, he⟩` from `GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (a := l.M') (GlobalTheory.LevelExist.M'_pos l') (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l.M' ∣ l'.M')`. Rewrite using `[he]`. Conclude with `pow_mem c'.zeta_mem e`. Use `le := hle₁ }`.

Take `⟨rF, e1, e2, f1, f2, f3, -⟩` from `hc c₁ c' rfl`. Establish `hid : spMap (IntermediateField.inclusion (le_refl c'.F)).toRingHom = 𝟙 (Sp c'.F)`. Rewrite using `[← Spec.map_id]`. Both sides reduce to the same expression. Establish `e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _` using `e2.trans ((congrArg _ hid).trans (Category.comp_id _))`.

Establish `hi : spMap (IntermediateField.inclusion hle).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom = spMap (IntermediateField.inclusion c₁.le).toRingHom`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Set `b : Xo.XF c₁ ⟶ Xo.XF c` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom) (by rw [Category.assoc, hi, pullback.condition])`. Establish `hb1 : b ≫ pullback.fst _ _ = pullback.fst _ _` using `pullback.lift_fst _ _ _`.

Establish `hb2 : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom` using `pullback.lift_snd _ _ _`. Establish `hp : IsPullback b (pullback.snd _ _) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap (IntermediateField.inclusion hle).toRingHom)`. Use `IsPullback.of_right ?_ hb2 (IsPullback.of_hasPullback _ _)` and prove the remaining obligations. Rewrite using `[hb1, hi]`. Conclude with `IsPullback.of_hasPullback _ _`.

Establish `h : (rF ≫ b) ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) = pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom`. Rewrite using `[Category.assoc, hb2, reassoc_of% e2']`. Establish `hlift : pullback.lift (rF ≫ b) _ h = rF ≫ hp.isoPullback.hom`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]`.

Rewrite using `[pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, e2']`. Use `⟨rF ≫ b, h, r₀, m, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hb1, e1]`. Rewrite using `[hlift]`. Use `infer_instance`.

Rewrite using `[hlift]`. Use `infer_instance`. Rewrite using `[hlift]`. Use `infer_instance`.
-/
theorem levelMap_coeff_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' hle hpq hd
  obtain ⟨r₀, jK, m, hk, -, -, -, -, hc⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l l' Xo Xo' hd
  have hle₁ : KA l ≤ c'.F := fun x hx => by
    have := c'.le (jK ⟨x, hx⟩).2
    rwa [hk] at this
  let c₁ : Coeff l :=
    { F := c'.F
      fin := c'.fin
      conj := c'.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (a := l.M') (GlobalTheory.LevelExist.M'_pos l')
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l.M' ∣ l'.M')
        rw [he]
        exact pow_mem c'.zeta_mem e
      le := hle₁ }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₁ c' rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c'.F)).toRingHom = 𝟙 (Sp c'.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion hle).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom =
      spMap (IntermediateField.inclusion c₁.le).toRingHom := by
    rw [← Spec.map_comp]
    rfl
  let b : Xo.XF c₁ ⟶ Xo.XF c :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (by rw [Category.assoc, hi, pullback.condition])
  have hb1 : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom :=
    pullback.lift_snd _ _ _
  have hp : IsPullback b (pullback.snd _ _) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (IntermediateField.inclusion hle).toRingHom) := by
    refine IsPullback.of_right ?_ hb2 (IsPullback.of_hasPullback _ _)
    rw [hb1, hi]
    exact IsPullback.of_hasPullback _ _
  have h : (rF ≫ b) ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
      pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, hb2, reassoc_of% e2']
  have hlift : pullback.lift (rF ≫ b) _ h = rF ≫ hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, e2']
  refine ⟨rF ≫ b, h, r₀, m, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hb1, e1]
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance

end GlobalTheory.LevelMapBase
