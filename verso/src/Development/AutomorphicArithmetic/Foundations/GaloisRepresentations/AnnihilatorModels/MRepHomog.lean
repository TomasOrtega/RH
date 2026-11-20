import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private lemma spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  dsimp only [spMap]
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private lemma spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
private lemma spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have h' : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
private lemma exists_algHom {κ B C : Type} [Field κ] [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    (f : Sp C ⟶ Sp B) (hf : f ≫ spMap (algebraMap κ B) = spMap (algebraMap κ C)) :
    ∃ φ : B →ₐ[κ] C, spMap φ.toRingHom = f := by
  obtain ⟨φ, rfl⟩ : ∃ φ, f = Spec.map φ := ⟨Spec.preimage f, (Spec.map_preimage f).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ C := by
    apply spMap_inj
    rw [← spMap_comp']
    exact hf
  exact ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, rfl⟩

private noncomputable def ptOf {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) :
    𝟙_ (Over (Sp κ)) ⟶ algPt κ B :=
  Over.homMk (spMap ε.toRingHom) (by
    show spMap ε.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
    rw [spMap_comp', ← spMap_id']
    congr 1
    ext r
    simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma ptOf_left {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) :
    (ptOf ε).left = spMap ε.toRingHom := rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
private lemma ptOf_surj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (y : 𝟙_ (Over (Sp κ)) ⟶ algPt κ B) :
    ∃ ε : B →ₐ[κ] κ, ptOf ε = y := by
  obtain ⟨ε, hε⟩ := exists_algHom (C := κ) y.left (by
    rw [Algebra.algebraMap_self, spMap_id']
    exact Over.w y)
  refine ⟨ε, Over.OverMorphism.ext ?_⟩
  rw [← hε]
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
private lemma ptOf_inj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] {ε ε' : B →ₐ[κ] κ}
    (h : ptOf ε = ptOf ε') : ε = ε' := by
  have h1 : spMap ε.toRingHom = spMap ε'.toRingHom := congrArg CommaMorphism.left h
  have h2 := spMap_inj h1
  ext x
  exact RingHom.congr_fun h2 x

end UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.repHomog_of :
    RepHomog := by
  intro κ _ A _ P hSub B _ _ i hmono hiff
  haveI : Mono i := hmono
  refine ⟨?_, ?_⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun ε => (⟨ptOf ε ≫ i, (hiff _ _).1 ⟨_, rfl⟩⟩ : { g // P (𝟙_ (Over (Sp κ))) g })) ⟨?_, ?_⟩)
    · intro a b h
      apply ptOf_inj
      exact (cancel_mono i).1 (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg
      obtain ⟨ε, rfl⟩ := ptOf_surj y
      exact ⟨ε, Subtype.ext hy⟩
  · obtain ⟨y, hy⟩ := (hiff _ _).2 (hSub (𝟙_ (Over (Sp κ)))).1
    obtain ⟨ε₀, rfl⟩ := ptOf_surj y
    refine ⟨ε₀, ?_, fun ε => ?_⟩
    · show spMap ε₀.toRingHom ≫ i.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left
      rw [← hy]
      rfl
    · let c : algPt κ B ⟶ A := toUnit (algPt κ B) ≫ ptOf ε ≫ i
      have hc : c = toUnit (algPt κ B) ≫ ptOf ε ≫ i := rfl
      have hcP : P _ c := (hiff _ _).1 ⟨toUnit _ ≫ ptOf ε, by rw [hc, Category.assoc]⟩
      have hiP : P _ i := (hiff _ _).1 ⟨𝟙 _, Category.id_comp _⟩
      have hcinvP : P _ c⁻¹ := by
        have h' := (hSub (algPt κ B)).2 1 c (hSub _).1 hcP
        simpa using h'
      have hm : P _ (i * c) := by
        have h' := (hSub (algPt κ B)).2 i c⁻¹ hiP hcinvP
        simpa using h'
      have hm' : P _ (i * c⁻¹) := (hSub _).2 i c hiP hcP
      obtain ⟨s, hs⟩ := (hiff _ _).2 hm
      obtain ⟨s', hs'⟩ := (hiff _ _).2 hm'
      have hsc : ∀ t : algPt κ B ⟶ algPt κ B, t ≫ c = c := by
        intro t
        rw [hc, ← Category.assoc, comp_toUnit]
      have h1 : s ≫ s' = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs', comp_mul, hs, GrpObj.comp_inv, hsc, Category.id_comp,
          mul_inv_cancel_right]
      have h2 : s' ≫ s = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hs', hsc, Category.id_comp, inv_mul_cancel_right]
      have hpt : ptOf ε₀ ≫ s = ptOf ε := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hy, _root_.one_mul, hc, ← Category.assoc,
          toUnit_unique (ptOf ε₀ ≫ toUnit _) (𝟙 _), Category.id_comp]
      obtain ⟨τ, hτ⟩ := exists_algHom (C := B) s.left (Over.w s)
      obtain ⟨τ', hτ'⟩ := exists_algHom (C := B) s'.left (Over.w s')
      have e1 : τ.comp τ' = AlgHom.id κ B := by
        have h' : spMap (τ.comp τ').toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ.toRingHom.comp τ'.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h1
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      have e2 : τ'.comp τ = AlgHom.id κ B := by
        have h' : spMap (τ'.comp τ).toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ'.toRingHom.comp τ.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h2
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      refine ⟨AlgEquiv.ofAlgHom τ τ' e1 e2, ?_⟩
      rw [AlgEquiv.coe_algHom_ofAlgHom]
      apply ptOf_inj
      apply Over.OverMorphism.ext
      show spMap (ε₀.toRingHom.comp τ.toRingHom) = (ptOf ε).left
      rw [← hpt]
      show _ = spMap ε₀.toRingHom ≫ s.left
      rw [← hτ, spMap_comp']
