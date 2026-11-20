import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Establish `inj : ∀ (s s' : SAB H (Sp T)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' → (Over.pullback (spMap (algebraMap T K))).map F = (Over.pullback (spMap (algebraMap T K))).map F' → F = F'`. Introduce `s s' F F' hF hF' h`. Conclude with `(hx T K s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩`. Establish `A : ∀ {X Y : Over (Sp T)} (a : X ⟶ Y), ((Over.pullback (spMap (algebraMap T K))).map a).left ≫ pullback.fst Y.hom _ = pullback.fst X.hom _ ≫ a.left` using `fun a => pullback.lift_fst _ _ _`. Take `⟨e, he, hφ⟩` from `grpPullback_iso m.cart (isGrpPullback_pullback t.G _)`.

Take `⟨e', he', hφ'⟩` from `grpPullback_iso m'.cart (isGrpPullback_pullback t'.G _)`. Take `⟨F, ⟨hF, hFf⟩, -⟩` from `hx T K t.G t'.G t.semi t'.semi (e.inv ≫ e'.hom) inferInstance`. Take `⟨F', ⟨hF', hFf'⟩, -⟩` from `hx T K t'.G t.G t'.semi t.semi (e'.inv ≫ e.hom) inferInstance`. Establish `key : m.cm.F ≫ F.left = m'.cm.F`. Rewrite using `[← hφ, Category.assoc, ← A, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, hφ']`.

Use `⟨⟨F, F', inj _ _ _ _ inferInstance inferInstance ?_, inj _ _ _ _ inferInstance inferInstance ?_⟩, hF, key, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, hFf, hFf']`. Simplify using the standard rewrite rules. Rewrite using `[Functor.map_comp, hFf, hFf']`. Simplify using the standard rewrite rules.

Use `show t.act.act a ≫ F = F ≫ t'.act.act a`. Use `t.act.hom a` as an intermediate fact. Use `t'.act.hom a` as an intermediate fact. Use `inj _ _ _ _ inferInstance inferInstance ?_` and prove the remaining obligations. Rewrite using `[← cancel_epi e.hom]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, Category.assoc, A]`. Rewrite using `[reassoc_of% hφ, reassoc_of% hφ, ← reassoc_of% m.act a, reassoc_of% key, key, m'.act]`. Conclude with `(Over.w _).trans (Over.w _).symm`.
-/
theorem sab_group_iso_of_generic
    (hx : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G',
      IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (t t' : SAB H (Sp T)) (tK : SAB H (Sp K))
    (m : SABMap tK t (spMap (algebraMap T K))) (m' : SABMap tK t' (spMap (algebraMap T K))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  have inj : ∀ (s s' : SAB H (Sp T)) (F F' : s.G ⟶ s'.G), IsMonHom F → IsMonHom F' →
      (Over.pullback (spMap (algebraMap T K))).map F = (Over.pullback (spMap (algebraMap T K))).map F' → F = F' := by
    intro s s' F F' hF hF' h
    exact (hx T K s.G s'.G s.semi s'.semi _ inferInstance).unique ⟨hF, rfl⟩ ⟨hF', h.symm⟩
  have A : ∀ {X Y : Over (Sp T)} (a : X ⟶ Y),
      ((Over.pullback (spMap (algebraMap T K))).map a).left ≫ pullback.fst Y.hom _ =
        pullback.fst X.hom _ ≫ a.left := fun a => pullback.lift_fst _ _ _
  obtain ⟨e, he, hφ⟩ := grpPullback_iso m.cart (isGrpPullback_pullback t.G _)
  obtain ⟨e', he', hφ'⟩ := grpPullback_iso m'.cart (isGrpPullback_pullback t'.G _)
  obtain ⟨F, ⟨hF, hFf⟩, -⟩ := hx T K t.G t'.G t.semi t'.semi (e.inv ≫ e'.hom) inferInstance
  obtain ⟨F', ⟨hF', hFf'⟩, -⟩ := hx T K t'.G t.G t'.semi t.semi (e'.inv ≫ e.hom) inferInstance
  have key : m.cm.F ≫ F.left = m'.cm.F := by
    rw [← hφ, Category.assoc, ← A, hFf, ← Category.assoc, ← Over.comp_left, e.hom_inv_id_assoc, hφ']
  refine ⟨⟨F, F', inj _ _ _ _ inferInstance inferInstance ?_, inj _ _ _ _ inferInstance inferInstance ?_⟩, hF, key,
    fun a => ?_⟩
  · rw [Functor.map_comp, hFf, hFf']; simp
  · rw [Functor.map_comp, hFf, hFf']; simp
  · show t.act.act a ≫ F = F ≫ t'.act.act a
    have := t.act.hom a
    have := t'.act.hom a
    refine inj _ _ _ _ inferInstance inferInstance ?_
    rw [← cancel_epi e.hom]
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, A]
      rw [reassoc_of% hφ, reassoc_of% hφ, ← reassoc_of% m.act a, reassoc_of% key, key, m'.act]
    · exact (Over.w _).trans (Over.w _).symm

end GlobalTheory
