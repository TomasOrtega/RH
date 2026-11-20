import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FChart
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.FRiCalc

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

/- English proof (translation)
Establish `: κ.Full` using `h.full`. Establish `: κ.Faithful` using `h.faithful`. Establish `: (Z.lift κ hκ ⋙ Z.ι).Full` using `h.full`. Establish `: (Z.lift κ hκ ⋙ Z.ι).Faithful` using `h.faithful`. Use `⟨Functor.Full.of_comp_faithful _ Z.ι, Functor.Faithful.of_comp _ Z.ι, fun T => h.mem T, ?_⟩` and prove the remaining obligations.

Introduce `T hT`. Take `⟨T₁, ⟨f⟩⟩` from `h.ess T.obj hT`. Conclude with `⟨T₁, ⟨Z.ι.preimageIso f⟩⟩`.
-/
lemma gl_onto {D : Type u} [Category.{v} D] {D₁ : Type u'} [Category.{v'} D₁] (Z : ObjectProperty D)
    (κ : D₁ ⥤ D) (hκ : ∀ T, Z (κ.obj T)) (W : D → Prop) (h : Onto κ W) :
    Onto (Z.lift κ hκ) (fun T => W T.obj) := by
  have : κ.Full := h.full
  have : κ.Faithful := h.faithful
  have : (Z.lift κ hκ ⋙ Z.ι).Full := h.full
  have : (Z.lift κ hκ ⋙ Z.ι).Faithful := h.faithful
  refine ⟨Functor.Full.of_comp_faithful _ Z.ι, Functor.Faithful.of_comp _ Z.ι, fun T => h.mem T, ?_⟩
  intro T hT
  obtain ⟨T₁, ⟨f⟩⟩ := h.ess T.obj hT
  exact ⟨T₁, ⟨Z.ι.preimageIso f⟩⟩

end CrystallineSemistableComparison.B

/- English proof (translation)
Introduce `R _ C _ C' _ F G A Q s n hQ hP hP' hS`. Set `Pr : ObjectProperty C` to `fun T => ∃ α, Q α T`. Set `Pr' : ObjectProperty C'` to `fun T => ∃ α, Q α (G.obj T)`. Set `Gq : Pr'.FullSubcategory ⥤ Pr.FullSubcategory` to `Pr.lift (Pr'.ι ⋙ G) (fun T => T.property)`. Set `Fq : Pr.FullSubcategory ⥤ ModuleCat.{w} R` to `Pr.ι ⋙ F`.

Establish `hc : RI (s ^ (2 * n + 3)) n Fq Gq`. Use `P.chart Fq Gq (fun α T => Q α T.obj) s n (fun α T T' f h => hQ α f.hom h) (fun T => T.property) ?_` and prove the remaining obligations. Introduce `S hSn`. Take `⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩` from `hS S hSn`. Take `⟨α₀, hα₀⟩` from `hSn`.

Set `ιq : C₁ ⥤ Pr.FullSubcategory` to `Pr.lift ι (fun T => ⟨α₀, hO.mem T α₀ hα₀⟩)`. Set `ιq' : C₁' ⥤ Pr'.FullSubcategory` to `Pr'.lift ι' (fun T => ⟨α₀, hO'.mem T α₀ hα₀⟩)`. Use `⟨C₁, inferInstance, C₁', inferInstance, ιq, ιq', G₁, ?_, ?_, ?_, hR⟩` and prove the remaining obligations. Conclude with `gl_onto Pr ι _ (fun T => ∀ α ∈ S, Q α T) hO`. Conclude with `gl_onto Pr' ι' _ (fun T => ∀ α ∈ S, Q α (G.obj T)) hO'`.

Conclude with `⟨Functor.fullyFaithfulCancelRight Pr.ι e⟩`. Establish `h1 : RI (1 * s ^ (2 * n + 3)) n F (Gq ⋙ Pr.ι)` using `(P.ri_calc F Pr.ι Gq 1 _ n).1 hP hc`. Establish `h2 : RI (1 * (1 * s ^ (2 * n + 3))) n F G` using `(P.ri_calc F G Pr'.ι 1 _ n).2.2.1 hP' h1`. Rewrite `h2` using `[one_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem CrystallineSemistableComparison.B.P.glob : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (G : C' ⥤ C) {A : Type} (Q : A → C → Prop) (s : R) (n : ℕ), (∀ α ⦃T T' : C⦄, (T ⟶ T') → Q α T → Q α T') → RI 1 n F (ObjectProperty.ι fun T => ∃ α, Q α T) → RI 1 n (G ⋙ F) (ObjectProperty.ι fun T => ∃ α, Q α (G.obj T)) → (∀ S : Set A, S.Nonempty → ∃ (C₁ : Type u) (_ : Category.{v} C₁) (C₁' : Type u') (_ : Category.{v'} C₁') (ι : C₁ ⥤ C) (ι' : C₁' ⥤ C') (G₁ : C₁' ⥤ C₁), Onto ι (fun T => ∀ α ∈ S, Q α T) ∧ Onto ι' (fun T => ∀ α ∈ S, Q α (G.obj T)) ∧ Nonempty (G₁ ⋙ ι ≅ ι' ⋙ G) ∧ RI s (n + 1) (ι ⋙ F) G₁) → RI (s ^ (2 * n + 3)) n F G := by
  intro R _ C _ C' _ F G A Q s n hQ hP hP' hS
  let Pr : ObjectProperty C := fun T => ∃ α, Q α T
  let Pr' : ObjectProperty C' := fun T => ∃ α, Q α (G.obj T)
  let Gq : Pr'.FullSubcategory ⥤ Pr.FullSubcategory := Pr.lift (Pr'.ι ⋙ G) (fun T => T.property)
  let Fq : Pr.FullSubcategory ⥤ ModuleCat.{w} R := Pr.ι ⋙ F
  have hc : RI (s ^ (2 * n + 3)) n Fq Gq := by
    refine P.chart Fq Gq (fun α T => Q α T.obj) s n (fun α T T' f h => hQ α f.hom h) (fun T => T.property) ?_
    intro S hSn
    obtain ⟨C₁, _, C₁', _, ι, ι', G₁, hO, hO', ⟨e⟩, hR⟩ := hS S hSn
    obtain ⟨α₀, hα₀⟩ := hSn
    let ιq : C₁ ⥤ Pr.FullSubcategory := Pr.lift ι (fun T => ⟨α₀, hO.mem T α₀ hα₀⟩)
    let ιq' : C₁' ⥤ Pr'.FullSubcategory := Pr'.lift ι' (fun T => ⟨α₀, hO'.mem T α₀ hα₀⟩)
    refine ⟨C₁, inferInstance, C₁', inferInstance, ιq, ιq', G₁, ?_, ?_, ?_, hR⟩
    · exact gl_onto Pr ι _ (fun T => ∀ α ∈ S, Q α T) hO
    · exact gl_onto Pr' ι' _ (fun T => ∀ α ∈ S, Q α (G.obj T)) hO'
    · exact ⟨Functor.fullyFaithfulCancelRight Pr.ι e⟩
  have h1 : RI (1 * s ^ (2 * n + 3)) n F (Gq ⋙ Pr.ι) := (P.ri_calc F Pr.ι Gq 1 _ n).1 hP hc
  have h2 : RI (1 * (1 * s ^ (2 * n + 3))) n F G := (P.ri_calc F G Pr'.ι 1 _ n).2.2.1 hP' h1
  rwa [one_mul, one_mul] at h2
