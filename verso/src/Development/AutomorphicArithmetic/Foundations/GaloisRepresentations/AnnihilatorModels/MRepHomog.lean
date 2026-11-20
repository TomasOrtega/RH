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
Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
private lemma spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  dsimp only [spMap]
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Simplify using `[spMap]`.
-/
private lemma spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

/- English proof (translation)
Establish `h' : CommRingCat.ofHom f = CommRingCat.ofHom g` using `Spec.map_injective h`. Conclude with `congrArg CommRingCat.Hom.hom h'`.
-/
private lemma spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have h' : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

/- English proof (translation)
Take `⟨φ, rfl⟩ : ∃ φ, f = Spec.map φ` from `⟨Spec.preimage f, (Spec.map_preimage f).symm⟩`. Establish `hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ C`. Apply `spMap_inj` to reduce the goal to its premises. Rewrite using `[← spMap_comp']`. Conclude with `hf`.

Conclude with `⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, rfl⟩`.
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
Take `⟨ε, hε⟩` from `exists_algHom (C := κ) y.left (by`. Rewrite using `[Algebra.algebraMap_self, spMap_id']`. Conclude with `Over.w y)`. Use `⟨ε, Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[← hε]`.

Both sides reduce to the same expression.
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
Establish `h1 : spMap ε.toRingHom = spMap ε'.toRingHom` using `congrArg CommaMorphism.left h`. Establish `h2` using `spMap_inj h1`. Use extensionality with `x`. Conclude with `RingHom.congr_fun h2 x`.
-/
private lemma ptOf_inj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] {ε ε' : B →ₐ[κ] κ}
    (h : ptOf ε = ptOf ε') : ε = ε' := by
  have h1 : spMap ε.toRingHom = spMap ε'.toRingHom := congrArg CommaMorphism.left h
  have h2 := spMap_inj h1
  ext x
  exact RingHom.congr_fun h2 x

end UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Introduce `κ _ A _ P hSub B _ _ i hmono hiff`. Use `haveI : Mono i := hmono`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `Nat.card_congr (Equiv.ofBijective (fun ε => (⟨ptOf ε ≫ i, (hiff _ _).1 ⟨_, rfl⟩⟩ : { g // P (𝟙_ (Over (Sp κ))) g })) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce `a b h`.

Apply `ptOf_inj` to reduce the goal to its premises. Conclude with `(cancel_mono i).1 (congrArg Subtype.val h)`. Introduce and unpack `⟨g, hg⟩`. Take `⟨y, hy⟩` from `(hiff _ _).2 hg`. Take `⟨ε, rfl⟩` from `ptOf_surj y`.

Conclude with `⟨ε, Subtype.ext hy⟩`. Take `⟨y, hy⟩` from `(hiff _ _).2 (hSub (𝟙_ (Over (Sp κ)))).1`. Take `⟨ε₀, rfl⟩` from `ptOf_surj y`. Use `⟨ε₀, ?_, fun ε => ?_⟩` and prove the remaining obligations. Use `show spMap ε₀.toRingHom ≫ i.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left`.

Rewrite using `[← hy]`. Both sides reduce to the same expression. Set `c : algPt κ B ⟶ A` to `toUnit (algPt κ B) ≫ ptOf ε ≫ i`. Establish `hc : c = toUnit (algPt κ B) ≫ ptOf ε ≫ i` using `rfl`. Establish `hcP : P _ c` using `(hiff _ _).1 ⟨toUnit _ ≫ ptOf ε, by rw [hc, Category.assoc]⟩`.

Establish `hiP : P _ i` using `(hiff _ _).1 ⟨𝟙 _, Category.id_comp _⟩`. Establish `hcinvP : P _ c⁻¹`. Establish `h'` using `(hSub (algPt κ B)).2 1 c (hSub _).1 hcP`. Simplify using `using h'`. Establish `hm : P _ (i * c)`.

Establish `h'` using `(hSub (algPt κ B)).2 i c⁻¹ hiP hcinvP`. Simplify using `using h'`. Establish `hm' : P _ (i * c⁻¹)` using `(hSub _).2 i c hiP hcP`. Take `⟨s, hs⟩` from `(hiff _ _).2 hm`. Take `⟨s', hs'⟩` from `(hiff _ _).2 hm'`.

Establish `hsc : ∀ t : algPt κ B ⟶ algPt κ B, t ≫ c = c`. Introduce `t`. Rewrite using `[hc, ← Category.assoc, comp_toUnit]`. Establish `h1 : s ≫ s' = 𝟙 _`. Apply `(cancel_mono i).1` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hs', comp_mul, hs, GrpObj.comp_inv, hsc, Category.id_comp, mul_inv_cancel_right]`. Establish `h2 : s' ≫ s = 𝟙 _`. Apply `(cancel_mono i).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs, comp_mul, hs', hsc, Category.id_comp, inv_mul_cancel_right]`. Establish `hpt : ptOf ε₀ ≫ s = ptOf ε`.

Apply `(cancel_mono i).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, hs, comp_mul, hy, _root_.one_mul, hc, ← Category.assoc, toUnit_unique (ptOf ε₀ ≫ toUnit _) (𝟙 _), Category.id_comp]`. Take `⟨τ, hτ⟩` from `exists_algHom (C := B) s.left (Over.w s)`. Take `⟨τ', hτ'⟩` from `exists_algHom (C := B) s'.left (Over.w s')`. Establish `e1 : τ.comp τ' = AlgHom.id κ B`.

Establish `h' : spMap (τ.comp τ').toRingHom = spMap (RingHom.id B)`. Rewrite using `[spMap_id']`. Use `show spMap (τ.toRingHom.comp τ'.toRingHom) = _`. Rewrite using `[← spMap_comp', hτ, hτ']`. Conclude with `congrArg CommaMorphism.left h1`.

Conclude with `AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x`. Establish `e2 : τ'.comp τ = AlgHom.id κ B`. Establish `h' : spMap (τ'.comp τ).toRingHom = spMap (RingHom.id B)`. Rewrite using `[spMap_id']`. Use `show spMap (τ'.toRingHom.comp τ.toRingHom) = _`.

Rewrite using `[← spMap_comp', hτ, hτ']`. Conclude with `congrArg CommaMorphism.left h2`. Conclude with `AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x`. Use `⟨AlgEquiv.ofAlgHom τ τ' e1 e2, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.coe_algHom_ofAlgHom]`.

Apply `ptOf_inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show spMap (ε₀.toRingHom.comp τ.toRingHom) = (ptOf ε).left`. Rewrite using `[← hpt]`. Use `show _ = spMap ε₀.toRingHom ≫ s.left`.

Rewrite using `[← hτ, spMap_comp']`.
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
