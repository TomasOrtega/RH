import Development.EtaleCohomology.CohomologicalPurity.LeafHsRelPfSplit

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

/- English proof (translation)
Establish `h : ComplexShape.embeddingDownNat.f p = -(p : ℤ)` using `rfl`. Express the relevant statement in the definitionally equal form `_ = (HomologicalComplex.extendMap ((chainsN R).map f) _).f _ ≫ _`. Rewrite using `[HomologicalComplex.extendMap_f _ _ h]`. Simplify using `only [chainsXIso]`. Use `erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]`.

Both sides reduce to the same expression.
-/
theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) _).f _ ≫ _
  rw [HomologicalComplex.extendMap_f _ _ h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

instance freePresSpan (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

/- English proof (translation)
Establish `h0 : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P)` using `IsPushout.of_hasPushout P.hom P.hom`. Establish `h1` using `h0.map ((evaluation _ PSh).obj (op (SimplexCategory.mk p)))`. Conclude with `h1.map (free R)`.
-/
theorem free_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inl P).app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inr P).app (op (SimplexCategory.mk p)))) := by
  have h0 : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout P.hom P.hom
  have h1 := h0.map ((evaluation _ PSh).obj (op (SimplexCategory.mk p)))
  exact h1.map (free R)

/- English proof (translation)
The claim follows from `(free_isPushout R P p).of_iso' (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)`.
-/
theorem chains_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout (((chains R).map P.hom).f (-(p : ℤ))) (((chains R).map P.hom).f (-(p : ℤ)))
      (((chains R).map (dbl.inl P)).f (-(p : ℤ))) (((chains R).map (dbl.inr P)).f (-(p : ℤ))) :=
  (free_isPushout R P p).of_iso' (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p)
    (chainsXIso R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)
    (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)

/- English proof (translation)
Introduce `R _ P _ n`. Distinguish the cases in `hn : ∃ p : ℕ, -(p : ℤ) = n`. Take `⟨p, rfl⟩` from `hn`. Conclude with `isIso_cokernel_map_of_isPushout (chains_isPushout R P p)`. Use `push Not at hn`.

Establish `hz : ∀ E : Spc, IsZero (((chains R).obj E).X n)` using `fun E => HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)`. Establish `hc : ∀ {E E' : Spc} (f : E ⟶ E'), IsZero (cokernel (((chains R).map f).f n))` using `fun f => by`. Rewrite using `[IsZero.iff_id_eq_zero]`. Conclude with `coequalizer.hom_ext ((hz _).eq_of_src _ _)`. Conclude with `⟨⟨0, (hc _).eq_of_src _ _, (hc _).eq_of_src _ _⟩⟩`.
-/
theorem leafDblCok_of : LeafDblCok := by
  intro R _ P _ n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    exact isIso_cokernel_map_of_isPushout (chains_isPushout R P p)
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains R).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hc : ∀ {E E' : Spc} (f : E ⟶ E'), IsZero (cokernel (((chains R).map f).f n)) := fun f => by
      rw [IsZero.iff_id_eq_zero]
      exact coequalizer.hom_ext ((hz _).eq_of_src _ _)
    exact ⟨⟨0, (hc _).eq_of_src _ _, (hc _).eq_of_src _ _⟩⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
