import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `p f hp κ kb _ _ _ hκ X t h τ hτ`. Establish `K : absFrob (geom kb t) p f hp h ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (τ : kb →+* kb))`. Distinguish the cases in `hk : (p : kb) = 0`. Establish `hk' : (p : Γ(Spec (CommRingCat.of kb), ⊤)) = 0`. Rewrite using `[← map_natCast (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom p]`.

Use `erw [hk]`. Conclude with `map_zero _`. Rewrite using `[GlobalTheory.SS.FrobField.absFrob_nat _ p f hp h hk']`. Use `congr 1`. Conclude with `GlobalTheory.SS.FrobField.absFrob_spec kb p f hp hk' (τ : kb →+* kb) hτ`.

Use `haveI : IsEmpty (geom kb t) := by`. Use `⟨fun x => hk ?_⟩` and prove the remaining obligations. Establish `hinj` using `(((geom kb t).presheaf.germ ⊤ x trivial).hom.comp ((pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom)).injective`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Simplify using `only [RingHom.comp_apply]`. Rewrite using `[map_natCast, map_natCast, h, map_zero]`. Conclude with `isInitialOfIsEmpty.hom_ext _ _`. Establish `hc : (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ t = pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (algebraMap κ kb))`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, K, Category.assoc, ← Spec.map_comp]`.

Use `congr 2`. Use extensionality with `c`. Simplify using the standard rewrite rules. Use `⟨pullback.lift (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) hc, pullback.lift_snd _ _ _, ?_, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, galMap_fst, pullback.lift_fst]`. Rewrite using `[Category.assoc, galMap_snd, ← Category.assoc, pullback.lift_snd, K]`. Introduce `Ω _ φ hφ x`. Establish `hΩ` using `GlobalTheory.SS.FrobField.cast_zero_of_hom x h`. Establish `e` using `GlobalTheory.SS.FrobField.absFrob_nat x p f hp hΩ h`.

Establish `e2 : absFrob (gp Ω) p f hp hΩ = Mod.sp φ` using `GlobalTheory.SS.FrobField.absFrob_spec Ω p f hp hΩ φ hφ`. Rewrite using `[pullback.lift_fst, ← Category.assoc, ← e, e2, Category.assoc]`.
-/
theorem UpperTheory.Gal.Mod.frEx :
    FrEx := by
  intro p f hp κ kb _ _ _ hκ X t h τ hτ
  have K : absFrob (geom kb t) p f hp h ≫ pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (τ : kb →+* kb)) := by
    by_cases hk : (p : kb) = 0
    · have hk' : (p : Γ(Spec (CommRingCat.of kb), ⊤)) = 0 := by
        rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom p]
        erw [hk]
        exact map_zero _
      rw [GlobalTheory.SS.FrobField.absFrob_nat _ p f hp h hk']
      congr 1
      exact GlobalTheory.SS.FrobField.absFrob_spec kb p f hp hk' (τ : kb →+* kb) hτ
    · haveI : IsEmpty (geom kb t) := by
        refine ⟨fun x => hk ?_⟩
        have hinj := (((geom kb t).presheaf.germ ⊤ x trivial).hom.comp
          ((pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))).appTop.hom.comp
            (Scheme.ΓSpecIso (CommRingCat.of kb)).inv.hom)).injective
        apply hinj
        rw [map_zero]
        simp only [RingHom.comp_apply]
        rw [map_natCast, map_natCast, h, map_zero]
      exact isInitialOfIsEmpty.hom_ext _ _
  have hc : (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) ≫ t =
      pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))) ≫ Spec.map (CommRingCat.ofHom (algebraMap κ kb)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, K, Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    simp
  refine ⟨pullback.lift (absFrob (geom kb t) p f hp h ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap κ kb))))
    (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap κ kb)))) hc, pullback.lift_snd _ _ _, ?_, ?_⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, galMap_fst, pullback.lift_fst]
    · rw [Category.assoc, galMap_snd, ← Category.assoc, pullback.lift_snd, K]
  · intro Ω _ φ hφ x
    have hΩ := GlobalTheory.SS.FrobField.cast_zero_of_hom x h
    have e := GlobalTheory.SS.FrobField.absFrob_nat x p f hp hΩ h
    have e2 : absFrob (gp Ω) p f hp hΩ = Mod.sp φ := GlobalTheory.SS.FrobField.absFrob_spec Ω p f hp hΩ φ hφ
    rw [pullback.lift_fst, ← Category.assoc, ← e, e2, Category.assoc]
