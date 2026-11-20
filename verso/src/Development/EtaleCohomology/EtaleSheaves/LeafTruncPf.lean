import Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut

noncomputable section
open CategoryTheory Limits Pretriangulated Triangulated

namespace LateralTheory.E.LeafTruncPf

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/- English proof (translation)
Establish `hT` using `DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y`. Use `(DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2 (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)` as an intermediate fact. Conclude with `this`.
-/
lemma mono_H_ι (Y : DerivedCategory C) (n : ℤ) :
    Mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (n + 1) Y
  have := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (n - 1) n (by lia)).2
    (IsZero.eq_of_src (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by lia)) _ _)
  exact this

/- English proof (translation)
Establish `hT` using `DerivedCategory.TStructure.t.triangleLTGE_distinguished n X`. Use `(DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2 (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)` as an intermediate fact. Conclude with `this`.
-/
lemma epi_H_π (X : DerivedCategory C) (n : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)) := by
  have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished n X
  have := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT n (n + 1) (by lia)).2
    (IsZero.eq_of_tgt (DerivedCategory.isZero_of_isLE _ (n - 1) (n + 1) (by lia)) _ _)
  exact this

/- English proof (translation)
The claim follows from `Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h`.
-/
lemma lift_LT {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : φ ≫ (DerivedCategory.TStructure.t.truncGEπ n).app Y = 0) :
    ∃ ψ : X ⟶ (DerivedCategory.TStructure.t.truncLT n).obj Y,
      φ = ψ ≫ (DerivedCategory.TStructure.t.truncLTι n).app Y :=
  Triangle.coyoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n Y) φ h

/- English proof (translation)
The claim follows from `Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h`.
-/
lemma desc_GE {X Y : DerivedCategory C} (n : ℤ) (φ : X ⟶ Y)
    (h : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ φ = 0) :
    ∃ ψ : (DerivedCategory.TStructure.t.truncGE n).obj X ⟶ Y,
      φ = (DerivedCategory.TStructure.t.truncGEπ n).app X ≫ ψ :=
  Triangle.yoneda_exact₂ _ (DerivedCategory.TStructure.t.triangleLTGE_distinguished n X) φ h

/- English proof (translation)
Take `⟨A, ⟨eX⟩⟩` from `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n`. Take `⟨B, ⟨eY⟩⟩` from `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n`. Take `⟨a, ha⟩` from `(DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)`. Establish `ha0 : a = 0`. Establish `eq` using `NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a`.

Simplify using `at eq`. Rewrite using `[← eq, ha]`. Simplify using `[hχ]`. Establish `: χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv` using `by simp`. Rewrite using `[this, ← ha, ha0, Functor.map_zero]`.

Simplify using the standard rewrite rules.
-/
lemma heart_zero {X Y : DerivedCategory C} (n : ℤ) [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (χ : X ⟶ Y) (hχ : (DerivedCategory.homologyFunctor C n).map χ = 0) : χ = 0 := by
  obtain ⟨A, ⟨eX⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  obtain ⟨B, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE Y n
  obtain ⟨a, ha⟩ := (DerivedCategory.singleFunctor C n).map_surjective (eX.inv ≫ χ ≫ eY.hom)
  have ha0 : a = 0 := by
    have eq := NatIso.naturality_1 (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) a
    dsimp at eq
    rw [← eq, ha]
    simp [hχ]
  have : χ = eX.hom ≫ (eX.inv ≫ χ ≫ eY.hom) ≫ eY.inv := by simp
  rw [this, ← ha, ha0, Functor.map_zero]
  simp

/- English proof (translation)
Establish `h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0` using `DerivedCategory.TStructure.t.zero _ n (n + 1)`. Take `⟨ψ, hψ⟩` from `lift_LT (n + 1) φ h1`. Establish `h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0` using `DerivedCategory.TStructure.t.zero _ (n - 1) n`. Take `⟨χ, hχ⟩` from `desc_GE n ψ h2`. Establish `hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0`.

Use `mono_H_ι Y n` as an intermediate fact. Use `epi_H_π X n` as an intermediate fact. Rewrite `hφ` using `[hψ, hχ, Functor.map_comp, Functor.map_comp]`. Rewrite using `[← cancel_epi ((DerivedCategory.homologyFunctor C n).map ((DerivedCategory.TStructure.t.truncGEπ n).app X)), ← cancel_mono ((DerivedCategory.homologyFunctor C n).map ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]`. Simplify using `using hφ`.

Establish `: χ = 0` using `heart_zero n χ hHχ`. Rewrite using `[hψ, hχ, this]`. Simplify using the standard rewrite rules.
-/
lemma zero_of_H {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (φ : X ⟶ Y)
    (hφ : (DerivedCategory.homologyFunctor C n).map φ = 0) : φ = 0 := by
  have h1 : φ ≫ (DerivedCategory.TStructure.t.truncGEπ (n + 1)).app Y = 0 :=
    DerivedCategory.TStructure.t.zero _ n (n + 1)
  obtain ⟨ψ, hψ⟩ := lift_LT (n + 1) φ h1
  have h2 : (DerivedCategory.TStructure.t.truncLTι n).app X ≫ ψ = 0 :=
    DerivedCategory.TStructure.t.zero _ (n - 1) n
  obtain ⟨χ, hχ⟩ := desc_GE n ψ h2
  have hHχ : (DerivedCategory.homologyFunctor C n).map χ = 0 := by
    have := mono_H_ι Y n
    have := epi_H_π X n
    rw [hψ, hχ, Functor.map_comp, Functor.map_comp] at hφ
    rw [← cancel_epi ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncGEπ n).app X)),
      ← cancel_mono ((DerivedCategory.homologyFunctor C n).map
      ((DerivedCategory.TStructure.t.truncLTι (n + 1)).app Y))]
    simpa using hφ
  have : χ = 0 := heart_zero n χ hHχ
  rw [hψ, hχ, this]
  simp

end LateralTheory.E.LeafTruncPf

open LateralTheory.E.LeafTruncPf in
/- English proof (translation)
Introduce `A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ`. Establish `: K0.IsLE 2` using `(DerivedCategory.isLE_iff K0 2).2 hK0`. Establish `: K2.IsGE 0` using `(DerivedCategory.isGE_iff K2 0).2 hK2`. Establish `: L.IsLE 0` using `(DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))`. Establish `: DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1` using `DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _`.

Establish `hP : DerivedCategory.TStructure.t.IsLE ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0` using `DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _`. Establish `e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0` using `zero_of_H 2 _ (by simp [Functor.map_comp, hf])`. Take `⟨f', hf'⟩` from `lift_LT 2 f e1`. Establish `e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0` using `zero_of_H 1 _ (by simp [Functor.map_comp, hg])`. Take `⟨w, hw⟩` from `lift_LT 1 _ e2`.

Establish `e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0` using `DerivedCategory.TStructure.t.zero _ 0 1`. Take `⟨ℓ', hℓ'⟩` from `lift_LT 1 ℓ e3`. Establish `hiso : IsIso ℓ'`. Rewrite using `[DerivedCategory.isIso_iff]`. Introduce `m`.

Break down `eq_or_ne m 0 with rfl | hm` into its components or cases. Establish `hm0` using `mono_H_ι K2 0`. Rewrite `hm0` using `[zero_add]`. Establish `hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫ (DerivedCategory.homologyFunctor A 0).map ((DerivedCategory.TStructure.t.truncLTι 1).app K2))`. Rewrite using `[← Functor.map_comp, ← hℓ']`.

Conclude with `hℓ`. Establish `: Epi ((DerivedCategory.homologyFunctor A 0).map ((DerivedCategory.TStructure.t.truncLTι 1).app K2))` using `epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _`. Establish `: IsIso ((DerivedCategory.homologyFunctor A 0).map ((DerivedCategory.TStructure.t.truncLTι 1).app K2))` using `isIso_of_mono_of_epi _`. Conclude with `IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map ((DerivedCategory.TStructure.t.truncLTι 1).app K2))`. Establish `hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj ((DerivedCategory.TStructure.t.truncLT 1).obj K2))`.

Break down `lt_or_gt_of_ne hm with h | h` into its components or cases. Conclude with `DerivedCategory.isZero_of_isGE _ 0 m h`. Conclude with `DerivedCategory.isZero_of_isLE _ 0 m h`. Conclude with `⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩`. Use `⟨f' ≫ w ≫ inv ℓ', ?_⟩` and prove the remaining obligations.

Rewrite using `[hf', hℓ']`. Simplify using `only [Category.assoc, IsIso.inv_hom_id_assoc, hw]`.
-/
theorem LateralTheory.E.LeafGhostRelCut.LeafTrunc_of : LateralTheory.E.LeafGhostRelCut.LeafTrunc := by
  intro A _ _ _ K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  have : K0.IsLE 2 := (DerivedCategory.isLE_iff K0 2).2 hK0
  have : K2.IsGE 0 := (DerivedCategory.isGE_iff K2 0).2 hK2
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 (fun i hi => hL i (by lia))
  have : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 2).obj K1) 1 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have hP : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLT 1).obj K2) 0 :=
    DerivedCategory.TStructure.t.isLE_truncLT_obj _ _ _
  have e1 : f ≫ (DerivedCategory.TStructure.t.truncGEπ 2).app K1 = 0 :=
    zero_of_H 2 _ (by simp [Functor.map_comp, hf])
  obtain ⟨f', hf'⟩ := lift_LT 2 f e1
  have e2 : ((DerivedCategory.TStructure.t.truncLTι 2).app K1 ≫ g) ≫
      (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    zero_of_H 1 _ (by simp [Functor.map_comp, hg])
  obtain ⟨w, hw⟩ := lift_LT 1 _ e2
  have e3 : ℓ ≫ (DerivedCategory.TStructure.t.truncGEπ 1).app K2 = 0 :=
    DerivedCategory.TStructure.t.zero _ 0 1
  obtain ⟨ℓ', hℓ'⟩ := lift_LT 1 ℓ e3
  have hiso : IsIso ℓ' := by
    rw [DerivedCategory.isIso_iff]
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · have hm0 := mono_H_ι K2 0
      rw [zero_add] at hm0
      have hc : IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ' ≫
          (DerivedCategory.homologyFunctor A 0).map
            ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := by
        rw [← Functor.map_comp, ← hℓ']; exact hℓ
      have : Epi ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) :=
        epi_of_epi ((DerivedCategory.homologyFunctor A 0).map ℓ') _
      have : IsIso ((DerivedCategory.homologyFunctor A 0).map
          ((DerivedCategory.TStructure.t.truncLTι 1).app K2)) := isIso_of_mono_of_epi _
      exact IsIso.of_isIso_comp_right _ ((DerivedCategory.homologyFunctor A 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app K2))
    · have hZ : IsZero ((DerivedCategory.homologyFunctor A m).obj
          ((DerivedCategory.TStructure.t.truncLT 1).obj K2)) := by
        rcases lt_or_gt_of_ne hm with h | h
        · exact DerivedCategory.isZero_of_isGE _ 0 m h
        · exact DerivedCategory.isZero_of_isLE _ 0 m h
      exact ⟨⟨0, (hL m hm).eq_of_src _ _, hZ.eq_of_src _ _⟩⟩
  refine ⟨f' ≫ w ≫ inv ℓ', ?_⟩
  rw [hf', hℓ']
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, hw]

end
