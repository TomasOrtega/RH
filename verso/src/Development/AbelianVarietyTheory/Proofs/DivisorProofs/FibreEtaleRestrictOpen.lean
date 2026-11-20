import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

/- English proof (translation)
Introduce `T X Z T' X' Z' S p q h hh p' q' h' hh' iT iX iZ _ _ _ sZ sh x x' sx W w hw hz hE`. Establish `hp : p' ≫ iT = iX ≫ p`. Simplify using `only [← hh, ← hh', Category.assoc, ← sZ]`. Simplify using `only [← Category.assoc, sh]`. Establish `hs : x' ≫ iT = 𝟙 S ≫ x` using `by simp [sx]`.

Set `j` to `pullback.map p' x' p x iX (𝟙 S) iT hp hs`. Set `jZ` to `pullback.map q' x' q x iZ (𝟙 S) iT sZ.symm hs`. Take `⟨a', ha'⟩` from `hz`. Establish `hwr : w ∈ Set.range j`. Rewrite using `[Scheme.Pullback.range_map]`.

Conclude with `⟨⟨a', ha'⟩, ⟨pullback.snd p x w, by simp⟩⟩`. Take `⟨w', rfl⟩` from `hwr`. Use `set F := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp) with hF`. Use `set F' := pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp) with hF'`. Establish `hnat : j ≫ F = F' ≫ jZ`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [j, jZ, F, F', Category.assoc]`. Rewrite using `[pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, sh]`. Simplify using `only [j, jZ, F, F', Category.assoc]`. Rewrite using `[pullback.lift_snd, pullback.lift_snd]`.

Simplify using `only [Category.comp_id]`. Conclude with `(pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm`. Use `⟨j ⁻¹ᵁ W, w', hw, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : j ≫ pullback.fst p x = pullback.fst p' x' ≫ iX` using `pullback.lift_fst _ _ _`. Establish `e2` using `congrArg (fun f : pullback p' x' ⟶ X => f w') e1`.

Simplify using `only [Scheme.Hom.comp_apply] at e2`. Conclude with `e2.symm`. Establish `e : ((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ = (j ∣_ W) ≫ (W.ι ≫ F)`. Rewrite using `[Category.assoc, ← hnat, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]`. Establish `: Etale (((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ)`.

Rewrite using `[e]`. Use `infer_instance`. Conclude with `Etale.of_comp _ jZ`.
-/
theorem fibre_etale_restrict_open : ∀ (T X Z T' X' Z' S : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p) (p' : X' ⟶ T') (q' : Z' ⟶ T') (h' : X' ⟶ Z') (hh' : h' ≫ q' = p') (iT : T' ⟶ T) (iX : X' ⟶ X) (iZ : Z' ⟶ Z) [IsOpenImmersion iT] [IsOpenImmersion iX] [IsOpenImmersion iZ] (sZ : iZ ≫ q = q' ≫ iT) (sh : iX ≫ h = h' ≫ iZ) (x : S ⟶ T) (x' : S ⟶ T') (sx : x' ≫ iT = x) (W : (pullback p x).Opens) (w : ↥(pullback p x)) (hw : w ∈ W) (hz : pullback.fst p x w ∈ Set.range iX), Etale (W.ι ≫ pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp)) → ∃ (W' : (pullback p' x').Opens) (w' : ↥(pullback p' x')), w' ∈ W' ∧ iX (pullback.fst p' x' w') = pullback.fst p x w ∧ Etale (W'.ι ≫ pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp)) := by
  intro T X Z T' X' Z' S p q h hh p' q' h' hh' iT iX iZ _ _ _ sZ sh x x' sx W w hw hz hE
  have hp : p' ≫ iT = iX ≫ p := by
    simp only [← hh, ← hh', Category.assoc, ← sZ]
    simp only [← Category.assoc, sh]
  have hs : x' ≫ iT = 𝟙 S ≫ x := by simp [sx]
  let j := pullback.map p' x' p x iX (𝟙 S) iT hp hs
  let jZ := pullback.map q' x' q x iZ (𝟙 S) iT sZ.symm hs
  obtain ⟨a', ha'⟩ := hz
  have hwr : w ∈ Set.range j := by
    rw [Scheme.Pullback.range_map]
    exact ⟨⟨a', ha'⟩, ⟨pullback.snd p x w, by simp⟩⟩
  obtain ⟨w', rfl⟩ := hwr
  set F := pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp) with hF
  set F' := pullback.map p' x' q' x' h' (𝟙 _) (𝟙 _) (by simp [hh']) (by simp) with hF'
  have hnat : j ≫ F = F' ≫ jZ := by
    apply pullback.hom_ext
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc, Category.assoc, sh]
    · simp only [j, jZ, F, F', Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd]
      simp only [Category.comp_id]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨j ⁻¹ᵁ W, w', hw, ?_, ?_⟩
  · have e1 : j ≫ pullback.fst p x = pullback.fst p' x' ≫ iX := pullback.lift_fst _ _ _
    have e2 := congrArg (fun f : pullback p' x' ⟶ X => f w') e1
    simp only [Scheme.Hom.comp_apply] at e2
    exact e2.symm
  · have e : ((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ = (j ∣_ W) ≫ (W.ι ≫ F) := by
      rw [Category.assoc, ← hnat, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    have : Etale (((j ⁻¹ᵁ W).ι ≫ F') ≫ jZ) := by
      rw [e]; infer_instance
    exact Etale.of_comp _ jZ

end GlobalTheory
