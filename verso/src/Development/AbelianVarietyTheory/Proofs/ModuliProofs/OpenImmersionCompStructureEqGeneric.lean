import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

/- English proof (translation)
Rewrite using `[Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]`.
-/
theorem Cpt.openImmersion_comp_structure_eq_generic {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {U : Scheme.{0}} {F O : Type}
    [Field F] [CommRing O] {c : U ⟶ Sp F} {t : SAB H U} {β : O →+* F} (C : Cpt c t β) :
    C.j ≫ C.s = c ≫ spMap β := by
  rw [Cpt.j, Category.assoc, pullback.condition, ← Category.assoc, C.jQ_over]

/- English proof (translation)
Unfold `spMap`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private theorem spMap_comp_moduli_spaces {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (g : A →+* B) (g' : B →+* D) :
    spMap (g'.comp g) = spMap g' ≫ spMap g := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Introduce `E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf hD hβ hc hj hφ`. Take `⟨⟨hdom, hDed⟩, -, hFrac⟩` from `hD`. Set `_ : Algebra O'' F''` to `β''.toAlgebra`. Use `hdom` as an intermediate fact. Establish `: IsDedekindDomain O''` using `hDed`.

Establish `: IsFractionRing O'' F''` using `hFrac`. Take `⟨hN, -, -, hPre, hFl, hDom, hQC⟩` from `GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat C''.proj C''.jQ_open C''.jQ_dense`. Establish `: IsLocallyNoetherian C''.X` using `hN`. Establish `hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b`. Rewrite using `[hf, Category.assoc, spMap_comp_moduli_spaces]`.

Establish `hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over)`. Use `a.fin` as an intermediate fact. Use `infer_instance`. Establish `hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [Category.assoc, pullback.lift_fst, a.j_comm, hj]`. Simplify using `only [Category.assoc, pullback.lift_snd]`. Rewrite using `[Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ, spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]`. Take `⟨h, ⟨h1, h2⟩, -⟩` from `GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal hPre hFl hDom hQC _ _ _ hq hsq`. Establish `hπ : h ≫ a.π = f`.

Simplify `congrArg (· ≫ pullback.fst _ _) h2` using `only [Category.assoc, pullback.lift_fst]`. Establish `hh : h ≫ C'.s = C''.s ≫ spMap b'`. Simplify `congrArg (· ≫ pullback.snd _ _) h2` using `only [Category.assoc, pullback.lift_snd]`. Use `clear h2 hsq hbase`. Substitute `hπ` using the available equality.

Take `⟨mu', hmu'⟩` from `sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu`. Use `⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩` and prove the remaining obligations. Apply `a.mu.2.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc] erw [← hmu', hφ, a.φ_comm]`. Establish `w1` using `mu'.2.1.w`.

Establish `w2` using `C''.m.2.1.w`. Establish `w3` using `ν'.2.1.w`. Establish `w4` using `C'.m.2.1.w`. Establish `h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _`. Simplify `h1` using `only [Cpt.j, Category.assoc]`.

Simplify using `only [Category.assoc] at w1 w2 w3 w4 ⊢`. Use `erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]`. Introduce `hfin`. Establish `: IsProper C'.s` using `projProper O' C'.X C'.s C'.proj`. Set `p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b))` to `pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by`.

Rewrite using `[Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])`. Establish `hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [p, Category.assoc]`. Rewrite using `[pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]`.

Simplify using `only [p, Category.assoc]`. Rewrite using `[pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]`. Establish `: IsSeparated p`. Establish `e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b')` using `pullback.lift_snd _ _ _`. Establish `: IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b)))`.

Rewrite using `[e]`. Use `infer_instance`. Conclude with `IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))`. Rewrite `hfin` using `[← hp]`. Conclude with `IsFinite.of_comp _ p`.
-/
theorem Cpt.Above.exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (U : Scheme.{0}) (F O : Type) [Field F] [CommRing O] (c : U ⟶ Sp F) (t : SAB H U) (β : O →+* F) (U' : Scheme.{0}) (F' O' : Type) [Field F'] [CommRing O'] (c' : U' ⟶ Sp F') (t' : SAB H U') (β' : O' →+* F') (U'' : Scheme.{0}) (F'' O'' : Type) [Field F''] [CommRing O''] (c'' : U'' ⟶ Sp F'') (t'' : SAB H U'') (β'' : O'' →+* F'') (C : Cpt c t β) (C' : Cpt c' t' β') (C'' : Cpt c'' t'' β'') (b : O →+* O') (b' : O' →+* O'') (k' : F' →+* F'') (r : U' ⟶ U) (ν : SABMap t' t r) (a : C'.Above C b r ν) (r' : U'' ⟶ U') (ν' : SABMap t'' t' r') (f : C''.X ⟶ C.X) (mu : SABMap C''.t C.t f) (hf : f ≫ C.s = C''.s ≫ spMap (b'.comp b)), IsDedFrac β'' → β''.comp b' = k'.comp β' → r' ≫ c' = c'' ≫ spMap k' → C''.j ≫ f = r' ≫ r ≫ C.j → C''.m.φ ≫ mu.φ = ν'.φ ≫ ν.φ ≫ C.m.φ → ∃ (h : C''.X ⟶ C'.X) (mu' : SABMap C''.t C'.t h) (hh : h ≫ C'.s = C''.s ≫ spMap b'), h ≫ a.π = f ∧ mu'.φ ≫ a.mu.φ = mu.φ ∧ C''.j ≫ h = r' ≫ C'.j ∧ C''.m.φ ≫ mu'.φ = ν'.φ ≫ C'.m.φ ∧ (IsFinite (pullback.lift f C''.s hf) → IsFinite (pullback.lift h C''.s hh)) := by
  intro E _ _ _ H U F O _ _ c t β U' F' O' _ _ c' t' β' U'' F'' O'' _ _ c'' t'' β'' C C' C'' b b' k' r ν a r' ν' f mu hf
    hD hβ hc hj hφ
  obtain ⟨⟨hdom, hDed⟩, -, hFrac⟩ := hD
  let _ : Algebra O'' F'' := β''.toAlgebra
  have := hdom
  have : IsDedekindDomain O'' := hDed
  have : IsFractionRing O'' F'' := hFrac
  obtain ⟨hN, -, -, hPre, hFl, hDom, hQC⟩ := GlobalTheory.genericPart_dense_proOpen O'' F'' C''.X U'' C''.s C''.jQ C''.flat
    C''.proj C''.jQ_open C''.jQ_dense
  have : IsLocallyNoetherian C''.X := hN

  have hbase : f ≫ C.s = (C''.s ≫ spMap b') ≫ spMap b := by
    rw [hf, Category.assoc, spMap_comp_moduli_spaces]
  have hq : IsIntegralHom (pullback.lift a.π C'.s a.π_over) := by
    have := a.fin
    infer_instance
  have hsq : (r' ≫ C'.j) ≫ pullback.lift a.π C'.s a.π_over = C''.j ≫ pullback.lift f (C''.s ≫ spMap b') hbase := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, a.j_comm, hj]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [Cpt.openImmersion_comp_structure_eq_generic C', ← Category.assoc r', hc, Category.assoc, ← spMap_comp_moduli_spaces, ← hβ,
        spMap_comp_moduli_spaces, ← Category.assoc C''.j, Cpt.openImmersion_comp_structure_eq_generic C'', Category.assoc]
  obtain ⟨h, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_lift_of_densePart C''.X U'' (pullback C.s (spMap b)) C'.X C''.j C''.normal
    hPre hFl hDom hQC _ _ _ hq hsq
  have hπ : h ≫ a.π = f := by
    simpa only [Category.assoc, pullback.lift_fst] using congrArg (· ≫ pullback.fst _ _) h2
  have hh : h ≫ C'.s = C''.s ≫ spMap b' := by
    simpa only [Category.assoc, pullback.lift_snd] using congrArg (· ≫ pullback.snd _ _) h2
  clear h2 hsq hbase
  subst hπ
  obtain ⟨mu', hmu'⟩ := sabCancel pullCubCancel E H C.X C'.X C''.X C.t C'.t C''.t a.π h a.mu mu
  refine ⟨h, mu', hh, rfl, hmu'.symm, h1, ?_, ?_⟩
  · apply a.mu.2.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      erw [← hmu', hφ, a.φ_comm]
    · have w1 := mu'.2.1.w
      have w2 := C''.m.2.1.w
      have w3 := ν'.2.1.w
      have w4 := C'.m.2.1.w
      have h1' : C''.jQ ≫ pullback.fst _ _ ≫ h = r' ≫ C'.jQ ≫ pullback.fst _ _ := by
        simpa only [Cpt.j, Category.assoc] using h1
      simp only [Category.assoc] at w1 w2 w3 w4 ⊢
      erw [w1, reassoc_of% w2, h1', w4, reassoc_of% w3]
  · intro hfin
    have : IsProper C'.s := projProper O' C'.X C'.s C'.proj
    let p : pullback C'.s (spMap b') ⟶ pullback C.s (spMap (b'.comp b)) :=
      pullback.lift (pullback.fst _ _ ≫ a.π) (pullback.snd _ _) (by
        rw [Category.assoc, a.π_over, ← Category.assoc, pullback.condition, Category.assoc, spMap_comp_moduli_spaces])
    have hp : pullback.lift h C''.s hh ≫ p = pullback.lift (h ≫ a.π) C''.s hf := by
      apply pullback.hom_ext
      · simp only [p, Category.assoc]
        rw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
      · simp only [p, Category.assoc]
        rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
    have : IsSeparated p := by
      have e : p ≫ pullback.snd C.s (spMap (b'.comp b)) = pullback.snd C'.s (spMap b') := pullback.lift_snd _ _ _
      have : IsSeparated (p ≫ pullback.snd C.s (spMap (b'.comp b))) := by
        rw [e]
        infer_instance
      exact IsSeparated.of_comp p (pullback.snd C.s (spMap (b'.comp b)))
    rw [← hp] at hfin
    exact IsFinite.of_comp _ p

end GlobalTheory.Models
