import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ChainsIso

variable (R : Type) [CommRing R]

/- English proof (translation)
Establish `h1 : ((chains R).map g).f (-(p : ℤ)) = (chainsXIso R E p).hom ≫ (((chainsN R).map g).f p) ≫ (chainsXIso R E' p).inv` using `HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl`. Rewrite using `[h1]`. Both sides reduce to the same expression.
-/
theorem chains_map_f {E E' : Spc} (g : E ⟶ E') (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv := by
  have h1 : ((chains R).map g).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (((chainsN R).map g).f p) ≫ (chainsXIso R E' p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1]
  rfl

/- English proof (translation)
Apply `HomologicalComplex.isZero_extend_X` to reduce the goal to its premises. Introduce `n h`. Express the relevant statement in the definitionally equal form `-(n : ℤ) = i at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem chains_isZero (E : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj E).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -(n : ℤ) = i at h
  omega

end ChainsIso

open ChainsIso in

/- English proof (translation)
Introduce `R _ P₁ P₂ Q f₁ f₂ h`. It suffices to establish `hc : ∀ i, IsIso ((biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))).f i) from HomologicalComplex.Hom.isIso_of_components _`. Introduce `i`. Establish `e` using `biprod.mapBiprod_hom_desc (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i) (f := (chains R).map (disc.map f₁)) (g := (chains R).map (disc.map f₂))`. Express the relevant statement in the definitionally equal form `IsIso ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i).map _)`.

Rewrite using `[← e]`. It suffices to establish `hs : IsIso (biprod.desc (((chains R).map (disc.map f₁)).f i) (((chains R).map (disc.map f₂)).f i)) by`. Conclude with `IsIso.comp_isIso' inferInstance hs`. Break down `lt_or_ge 0 i with hi | hi` into its components or cases. Establish `h1` using `chains_isZero R (disc.obj P₁) i hi`.

Establish `h2` using `chains_isZero R (disc.obj P₂) i hi`. Establish `hQ` using `chains_isZero R (disc.obj Q) i hi`. Use `⟨⟨0, ?_, hQ.eq_of_src _ _⟩⟩` and prove the remaining obligations. Apply `biprod.hom_ext'` to reduce the goal to its premises. Conclude with `h1.eq_of_src _ _`.

Conclude with `h2.eq_of_src _ _`. Take `⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ)` from `⟨i.natAbs, by omega⟩`. Rewrite using `[chains_map_f, chains_map_f]`. Establish `hfree : IsIso (biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p)))) ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p)))))` using `h`. Establish `hc : biprod.desc ((chainsXIso R (disc.obj P₁) p).hom ≫ (free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))) ≫ (chainsXIso R (disc.obj Q) p).inv) ((chainsXIso R (disc.obj P₂) p).hom ≫ (free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))) ≫ (chainsXIso R (disc.obj Q) …`.

Apply the tactic sequence `apply biprod.hom_ext' <;> simp`. Rewrite using `[hc]`. Conclude with `IsIso.comp_isIso' (show IsIso (biprod.mapIso (chainsXIso R (disc.obj P₁) p) (chainsXIso R (disc.obj P₂) p)).hom from inferInstance) (IsIso.comp_isIso' hfree inferInstance)`.
-/
theorem chains_disc_biprod_isIso : ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f₁ : P₁ ⟶ Q) (f₂ : P₂ ⟶ Q),
    IsIso (biprod.desc ((free R).map f₁) ((free R).map f₂)) →
      IsIso (biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))) := by
  intro R _ P₁ P₂ Q f₁ f₂ h
  suffices hc : ∀ i, IsIso ((biprod.desc ((chains R).map (disc.map f₁)) ((chains R).map (disc.map f₂))).f i) from
    HomologicalComplex.Hom.isIso_of_components _
  intro i
  have e := biprod.mapBiprod_hom_desc (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i)
    (f := (chains R).map (disc.map f₁)) (g := (chains R).map (disc.map f₂))
  change IsIso ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) i).map _)
  rw [← e]
  suffices hs : IsIso (biprod.desc (((chains R).map (disc.map f₁)).f i) (((chains R).map (disc.map f₂)).f i)) by
    exact IsIso.comp_isIso' inferInstance hs
  rcases lt_or_ge 0 i with hi | hi
  · have h1 := chains_isZero R (disc.obj P₁) i hi
    have h2 := chains_isZero R (disc.obj P₂) i hi
    have hQ := chains_isZero R (disc.obj Q) i hi
    refine ⟨⟨0, ?_, hQ.eq_of_src _ _⟩⟩
    apply biprod.hom_ext'
    · exact h1.eq_of_src _ _
    · exact h2.eq_of_src _ _
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨i.natAbs, by omega⟩
    rw [chains_map_f, chains_map_f]
    have hfree : IsIso (biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
        ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))))) := h
    have hc : biprod.desc ((chainsXIso R (disc.obj P₁) p).hom ≫ (free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv)
        ((chainsXIso R (disc.obj P₂) p).hom ≫ (free R).map ((disc.map f₂).app (op (SimplexCategory.mk p))) ≫
          (chainsXIso R (disc.obj Q) p).inv) =
        biprod.map (chainsXIso R (disc.obj P₁) p).hom (chainsXIso R (disc.obj P₂) p).hom ≫
          biprod.desc ((free R).map ((disc.map f₁).app (op (SimplexCategory.mk p))))
            ((free R).map ((disc.map f₂).app (op (SimplexCategory.mk p)))) ≫ (chainsXIso R (disc.obj Q) p).inv := by
      apply biprod.hom_ext' <;> simp
    rw [hc]
    exact IsIso.comp_isIso' (show IsIso (biprod.mapIso (chainsXIso R (disc.obj P₁) p) (chainsXIso R (disc.obj P₂) p)).hom
      from inferInstance) (IsIso.comp_isIso' hfree inferInstance)

end GlobalTheory.EtC
end
