import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

/- English proof (translation)
Use `haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance`. Use `haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f`. Conclude with `IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range`.
-/
theorem isClosedImmersion_subschemeι_comp {R : Type} [CommRing R] {W W' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) [IsSeparated f] [IsImmersion π]
    (T : W'.IdealSheafData) [IsProper (T.subschemeι ≫ π ≫ f)] :
    IsClosedImmersion (T.subschemeι ≫ π) := by
  haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f
  exact IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range

/- English proof (translation)
Express the relevant statement in the definitionally equal form `IsProper (g.imageι ≫ f)`. Establish `hg : g.imageι = inv g.toImage ≫ g` using `(IsIso.eq_inv_comp _).2 g.toImage_imageι`. Rewrite using `[hg, Category.assoc]`. Use `infer_instance`.
-/
theorem isProper_ker_subschemeι_comp {X Y S : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (f : Y ⟶ S) [IsProper (g ≫ f)] : IsProper (g.ker.subschemeι ≫ f) := by
  change IsProper (g.imageι ≫ f)
  have hg : g.imageι = inv g.toImage ≫ g := (IsIso.eq_inv_comp _).2 g.toImage_imageι
  rw [hg, Category.assoc]
  infer_instance

/- English proof (translation)
Introduce `R _ I W W' f π hf hπ t ht hp`. Establish `hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π)` using `fun e => haveI := hp e`. Use `isClosedImmersion_subschemeι_comp f π (t e)`. Use `⟨fun e => ?_, fun e => ?_, fun e => ?_⟩` and prove the remaining obligations. Use `show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))`.

Establish `hle : t (e + 1) ≤ t e` using `by rw [ht e]; exact le_sup_left`. Establish `hι : IsClosedImmersion (t (e + 1)).subschemeι` using `inferInstance`. Establish `h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e`. Use `(GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ (t e)).1` as an intermediate fact. Rewrite `this` using `[bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι, sup_eq_right.2 hle]`.

Conclude with `this`. Establish `hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥`. Use `(GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ ⊥).2` as an intermediate fact. Rewrite `this` using `[Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]`. Then use the resulting hypothesis. Establish `h2 : (t e).comap (t (e + 1)).subschemeι = (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π)` using `by conv_lhs => rw [ht e]`.

Rewrite using `[Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.assoc]`. Establish `h3` using `(GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1`. Rewrite `h3` using `[bot_sup_eq, Scheme.IdealSheafData.map_bot]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`.

Use `_ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by`. Rewrite using `[Scheme.IdealSheafData.map_comp]`. Use `_ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]`. Use `_ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl`. Use `haveI := hci e`.

Use `haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e`. Conclude with `isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f`. Use `haveI := hci e`. Use `le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_` and prove the remaining obligations. Use `show t e ≤ (((t e).subschemeι ≫ π).ker).comap π`.

Rewrite using `[← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]`. Establish `h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι`. Rewrite using `[← cancel_mono π, pullback.condition, Category.assoc]`. Rewrite using `[h]`. Use `conv_lhs => rw [← (t e).ker_subschemeι]`.

Conclude with `Scheme.Hom.le_ker_comp _ _`.
-/
theorem mapSystem : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π →
    ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) →
    IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧
      ∀ e, ((t e).map π).comap π = t e := by
  intro R _ I W W' f π hf hπ t ht hp
  have hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π) := fun e =>
    haveI := hp e; isClosedImmersion_subschemeι_comp f π (t e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))
    have hle : t (e + 1) ≤ t e := by rw [ht e]; exact le_sup_left
    have hι : IsClosedImmersion (t (e + 1)).subschemeι := inferInstance
    have h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ (t e)).1
      rw [bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
        sup_eq_right.2 hle] at this
      exact this
    have hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥ := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ ⊥).2
      rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    have h2 : (t e).comap (t (e + 1)).subschemeι =
        (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π) := by
      conv_lhs => rw [ht e]
      rw [Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1,
        Category.assoc]
    have h3 := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1
    rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h3
    calc (t e).map π = (((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι).map π := by
          rw [h1]
      _ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by
          rw [Scheme.IdealSheafData.map_comp]
      _ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]
      _ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl
  ·
    haveI := hci e
    haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e
    exact isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f
  ·
    haveI := hci e
    refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
    show t e ≤ (((t e).subschemeι ≫ π).ker).comap π
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι := by
      rw [← cancel_mono π, pullback.condition, Category.assoc]
    rw [h]
    conv_lhs => rw [← (t e).ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.FormalAlg
