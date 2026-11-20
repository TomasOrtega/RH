import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

/- English proof (translation)
Establish `: IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget S').map e.hom))`. Establish `h₀ : IsPullback e.hom.left A.hom B.hom (𝟙 S')` using `IsPullback.of_horiz_isIso ⟨by simp⟩`. Use `⟨by simpa using h₀.paste_horiz h.1, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations. Establish `k` using `h.2 T (x ≫ e.hom) (y ≫ e.hom) x₀ y₀ (by rw [hx, Over.comp_left, Category.assoc]) (by rw [hy, Over.comp_left, Category.assoc])`. Rewrite using `[k, ← MonObj.mul_comp, Over.comp_left, Category.assoc]`.
-/
private theorem isGrpPullback_iso_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {A B : Over S'} [GrpObj A] [GrpObj B]
    {G : Over S} [GrpObj G] (e : A ≅ B) [IsMonHom e.hom] {ψ : B.left ⟶ G.left} (h : IsGrpPullback B G f ψ) :
    IsGrpPullback A G f (e.hom.left ≫ ψ) := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have h₀ : IsPullback e.hom.left A.hom B.hom (𝟙 S') := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine ⟨by simpa using h₀.paste_horiz h.1, fun T x y x₀ y₀ hx hy => ?_⟩
  have k := h.2 T (x ≫ e.hom) (y ≫ e.hom) x₀ y₀ (by rw [hx, Over.comp_left, Category.assoc])
    (by rw [hy, Over.comp_left, Category.assoc])
  rw [k, ← MonObj.mul_comp, Over.comp_left, Category.assoc]

/- English proof (translation)
Establish `: QuasiCompact (genPt C)` using `inferInstance`. Establish `: IsDominant (genPt C)`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hm : genericPoint C ∈ Set.range (genPt C)` using `⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩`. Establish `hd : Dense ({genericPoint C} : Set C)`.

Rewrite using `[dense_iff_closure_eq]`. Conclude with `genericPoint_closure C`. Conclude with `hd.mono (Set.singleton_subset_iff.2 hm)`. Conclude with `⟨inferInstance, .of_isDominant _⟩`.
-/
private theorem genPt_dominant (C : Scheme.{0}) [IsIntegral C] :
    QuasiCompact (genPt C) ∧ IsSchemeTheoreticallyDominant (genPt C) := by
  have : QuasiCompact (genPt C) := inferInstance
  have : IsDominant (genPt C) := by
    refine ⟨?_⟩
    have hm : genericPoint C ∈ Set.range (genPt C) :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint C} : Set C) := by
      rw [dense_iff_closure_eq]
      exact genericPoint_closure C
    exact hd.mono (Set.singleton_subset_iff.2 hm)
  exact ⟨inferInstance, .of_isDominant _⟩

/- English proof (translation)
Introduce `O _ c C _ G B _ _ hG hB i X _ _ _ u q hu hq ⟨G', _, i', φ, u', P, qP, j, hφ, hT, hP, hj, hR⟩`. Take `⟨_, _⟩` from `genPt_dominant C`. Take `⟨_, _⟩` from `ExtUnique.flat_and_isSeparated_of_isSemiAbelian B hB`. Establish `hψ` using `isGrpPullback_pullback B (genPt C)`. Take `⟨q', hq', sq⟩` from `IsKer.baseChange hφ.1 hψ hT hq`.

Take `⟨_, _, _, _, k₁⟩` from `hP`. Take `⟨_, _, _, _, k₂⟩` from `hq'`. Take `⟨β, hβ, hβq⟩` from `FlatQuotient.exists_desc qP u' q' k₁ k₂.w`. Take `⟨δ, -, hδq⟩` from `FlatQuotient.exists_desc q' u' qP k₂ k₁.w`. Use `FlatQuotient.epi_of_flat_surjective qP` as an intermediate fact.

Use `FlatQuotient.epi_of_flat_surjective q'` as an intermediate fact. Set `e : P.A ≅ (Over.pullback (genPt C)).obj B` to `⟨β, δ, by rw [← cancel_epi qP, ← Category.assoc, hβq, hδq, Category.comp_id], by rw [← cancel_epi q', ← Category.assoc, hδq, hβq, Category.comp_id]⟩`. Establish `he : IsMonHom e.hom` using `hβ`. Establish `hT'` using `torusCompat_iff.1 hT`. Establish `hker : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]`.

Introduce `a`. Use `j.hom a` as an intermediate fact. Establish `hs : Smooth (splitTorus C X).hom` using `inferInstance`. Establish `h₁ : u' ≫ i'.act a ≫ q' = u' ≫ q'`. Rewrite using `[k₂.w, ← hβq, reassoc_of% hj a, k₁.w_assoc, IsMonHom.one_hom_assoc, IsMonHom.one_hom]`.

Establish `h₂ : u'.left ≫ (i'.act a).left ≫ q'.left = u'.left ≫ q'.left` using `congrArg CommaMorphism.left h₁`. Rewrite using `[← hq.2.2.2.2.w]`. Use `ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (genPt C) X) ?_` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, Over.comp_left, reassoc_of% hT', reassoc_of% hT', ← reassoc_of% hφ.2 a, sq.w, reassoc_of% h₂]`. Take `⟨iB, hiB⟩` from `hq.exists_oAct i hker`.

Use `⟨iB, hiB, P, j, e.hom.left ≫ pullback.fst B.hom (genPt C), ⟨isGrpPullback_iso_comp e hψ, fun a => ?_⟩, hR⟩` and prove the remaining obligations. Establish `: Epi qP.left` using `Flat.epi_of_flat_of_surjective _`. Establish `h₁ : (i'.act a).left ≫ qP.left = qP.left ≫ (j.act a).left` using `congrArg CommaMorphism.left (hj a)`. Establish `h₂ : (i.act a).left ≫ q.left = q.left ≫ (iB.act a).left` using `congrArg CommaMorphism.left (hiB a)`. Establish `h₃ : qP.left ≫ e.hom.left ≫ pullback.fst B.hom (genPt C) = φ ≫ q.left`.

Rewrite using `[sq.w, ← hβq]`. Conclude with `(Category.assoc _ _ _).symm`. Rewrite using `[← cancel_epi qP.left, ← reassoc_of% h₁, h₃, ← Category.assoc qP.left, h₃, reassoc_of% hφ.2 a, h₂, Category.assoc]`.
-/
theorem UpperTheory.abelian_quotient_inherits_action :
    ∀ (O : Type) [CommRing O] (c : O →+* O) (C : Scheme.{0}) [IsIntegral C] (G B : Over C) [GrpObj G] [GrpObj B],
        IsSemiAbelian G → IsSemiAbelian B → ∀ (i : OAct O G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
        (u : splitTorus C X ⟶ G) (q : G ⟶ B), IsMonHom u → IsKer u q → TorPol c i u (genPt C) →
        ∃ i' : OAct O B, (∀ a, i.act a ≫ q = q ≫ i'.act a) ∧ AbGen c i' := by
  intro O _ c C _ G B _ _ hG hB i X _ _ _ u q hu hq ⟨G', _, i', φ, u', P, qP, j, hφ, hT, hP, hj, hR⟩
  obtain ⟨_, _⟩ := genPt_dominant C
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian B hB
  have hψ := isGrpPullback_pullback B (genPt C)
  obtain ⟨q', hq', sq⟩ := IsKer.baseChange hφ.1 hψ hT hq
  obtain ⟨_, _, _, _, k₁⟩ := hP
  obtain ⟨_, _, _, _, k₂⟩ := hq'
  obtain ⟨β, hβ, hβq⟩ := FlatQuotient.exists_desc qP u' q' k₁ k₂.w
  obtain ⟨δ, -, hδq⟩ := FlatQuotient.exists_desc q' u' qP k₂ k₁.w
  have := FlatQuotient.epi_of_flat_surjective qP
  have := FlatQuotient.epi_of_flat_surjective q'
  let e : P.A ≅ (Over.pullback (genPt C)).obj B := ⟨β, δ,
    by rw [← cancel_epi qP, ← Category.assoc, hβq, hδq, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hδq, hβq, Category.comp_id]⟩
  have he : IsMonHom e.hom := hβ
  have hT' := torusCompat_iff.1 hT
  have hker : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B] := by
    intro a
    have := j.hom a
    have hs : Smooth (splitTorus C X).hom := inferInstance
    have h₁ : u' ≫ i'.act a ≫ q' = u' ≫ q' := by
      rw [k₂.w, ← hβq, reassoc_of% hj a, k₁.w_assoc, IsMonHom.one_hom_assoc, IsMonHom.one_hom]
    have h₂ : u'.left ≫ (i'.act a).left ≫ q'.left = u'.left ≫ q'.left := congrArg CommaMorphism.left h₁
    rw [← hq.2.2.2.2.w]
    refine ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (genPt C) X) ?_
    rw [Over.comp_left, Over.comp_left, Over.comp_left, reassoc_of% hT', reassoc_of% hT', ← reassoc_of% hφ.2 a,
      sq.w, reassoc_of% h₂]
  obtain ⟨iB, hiB⟩ := hq.exists_oAct i hker
  refine ⟨iB, hiB, P, j, e.hom.left ≫ pullback.fst B.hom (genPt C), ⟨isGrpPullback_iso_comp e hψ, fun a => ?_⟩, hR⟩
  have : Epi qP.left := Flat.epi_of_flat_of_surjective _
  have h₁ : (i'.act a).left ≫ qP.left = qP.left ≫ (j.act a).left := congrArg CommaMorphism.left (hj a)
  have h₂ : (i.act a).left ≫ q.left = q.left ≫ (iB.act a).left := congrArg CommaMorphism.left (hiB a)
  have h₃ : qP.left ≫ e.hom.left ≫ pullback.fst B.hom (genPt C) = φ ≫ q.left := by
    rw [sq.w, ← hβq]
    exact (Category.assoc _ _ _).symm
  rw [← cancel_epi qP.left, ← reassoc_of% h₁, h₃, ← Category.assoc qP.left, h₃, reassoc_of% hφ.2 a, h₂,
    Category.assoc]
