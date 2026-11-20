import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjSpace

namespace GlobalTheory.ProjBlowup

variable {X W : Scheme.{0}} {L : LB X} {m : ℕ}

/- English proof (translation)
Establish `hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom` using `fun B => by`. Rewrite using `[← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]`. Rewrite using `[hk, RingHom.mem_ker]`. Use `ext_germ fun z hz => ?_` and prove the remaining obligations. Take `⟨B, e, hzB, this⟩` from `h _ hz`.

Rewrite `this` using `[hk, RingHom.mem_ker, app_resG]`. Rewrite using `[← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]`.
-/
theorem mem_ideal_of_locally (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, app_resG] at this
  rw [← germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

/- English proof (translation)
The claim follows from `(comap_le_iff J g _).1 le_rfl V a ha A h`.
-/
theorem appLE_mem_ideal_comap (J : X.IdealSheafData) (g : W ⟶ X) (V : X.affineOpens) (A : W.affineOpens)
    (h : A.1 ≤ g ⁻¹ᵁ V.1) {a : Γ(X, V.1)} (ha : a ∈ J.ideal V) :
    (g.appLE V.1 A.1 h).hom a ∈ (J.comap g).ideal A :=
  (comap_le_iff J g _).1 le_rfl V a ha A h

/- English proof (translation)
Take `⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen`. Take `⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen`. Conclude with `⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩`.
-/
theorem exists_affine_pair (g : W ⟶ X) (U : X.Opens) (A : W.Opens) (y : W) (hy : y ∈ A) (hU : g y ∈ U) :
    ∃ (V : X.affineOpens) (B : W.affineOpens), V.1 ≤ U ∧ B.1 ≤ A ∧ B.1 ≤ g ⁻¹ᵁ V.1 ∧ y ∈ B.1 := by
  obtain ⟨_, ⟨V, hV', rfl⟩, hyV, hV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  obtain ⟨_, ⟨B, hB', rfl⟩, hyB, hB⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A ⊓ g ⁻¹ᵁ V from ⟨hy, hyV⟩) (A ⊓ g ⁻¹ᵁ V).isOpen
  exact ⟨⟨V, hV'⟩, ⟨B, hB'⟩, hV, fun x hx => (hB hx).1, fun x hx => (hB hx).2, hyB⟩

/- English proof (translation)
Use `set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK`. Establish `key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K`. Use `(comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨V, B, hV, hB, hBV, hyB⟩` from `exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩`. Use `⟨B, hB, hyB, ?_⟩` and prove the remaining obligations.

Establish `h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V` using `J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha`. Rewrite `h1` using `[hJ.2 k V (hV.trans inf_le_right)]`. Establish `h2 : resG W hB (resG W hA ((g.app U.1).hom a)) = (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a)`. Rewrite using `[appLE_resG, resG_resG]`. Both sides reduce to the same expression.

Rewrite using `[h2]`. Rewrite using `[← Ideal.mem_comap]`. Use `Ideal.span_le.2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]`.

Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)`. Use `(key _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem Generates.ideal_comap_top_le [IsAffine W] {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) (k : L.ι) (h : ⊤ ≤ g ⁻¹ᵁ L.U k) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤
      Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) := by
  set K : Ideal Γ(W, ⊤) := Ideal.span (Set.range fun j => (g.appLE (L.U k) ⊤ h).hom ((σ j).f k)) with hK
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop K := by
    refine (comap_le_iff _ _ _).2 fun U a ha A hA => mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (U.1 ⊓ L.U k) A.1 y hy ⟨hA hy, h trivial⟩
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X (hV.trans inf_le_left) a ∈ J.ideal V :=
      J.ideal_le_comap_ideal (U := V) (V := U) (hV.trans inf_le_left) ha
    rw [hJ.2 k V (hV.trans inf_le_right)] at h1
    have h2 : resG W hB (resG W hA ((g.app U.1).hom a)) =
        (g.appLE V.1 B.1 hBV).hom (resG X (hV.trans inf_le_left) a) := by
      rw [appLE_resG, resG_resG]
      rfl
    rw [h2]
    rw [← Ideal.mem_comap]
    refine Ideal.span_le.2 ?_ h1
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, appLE_resG, ← resG_appLE g h le_top]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩)
  refine (key _).trans ?_
  simp

/- English proof (translation)
Use `⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `: IsAffine A.1.toScheme` using `A.2`. Establish `hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1` using `A.1.ι_preimage_self.ge`. Establish `h1` using `appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs`.

Rewrite `h1` using `[← Scheme.IdealSheafData.comap_comp]`. Establish `h2` using `hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1`. Establish `hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom` using `ConcreteCategory.bijective_of_isIso _`. Rewrite using `[← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span, ← Set.range_comp]`. Use `h2 using 3` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j`. Conclude with `appLE_appLE _ _ h hA _`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `mem_ideal_of_locally _ _ _ fun y hy => ?_` and prove the remaining obligations.

Take `⟨V, B, hV, hB, hBV, hyB⟩` from `exists_affine_pair g (L.U k) A.1 y hy (h hy)`. Use `⟨B, hB, hyB, ?_⟩` and prove the remaining obligations. Establish `h1 : resG X hV ((σ j).f k) ∈ J.ideal V`. Rewrite using `[hJ.2 k V hV]`. Conclude with `Ideal.subset_span ⟨j, rfl⟩`.

Establish `h2` using `appLE_mem_ideal_comap J g V B hBV h1`. Rewrite `h2` using `[appLE_resG]`. Rewrite using `[resG_appLE]` and apply the resulting hypothesis.
-/
theorem Generates.generatesAlong_comap {J : X.IdealSheafData} {σ : Fin (m + 1) → L.Sec}
    (hJ : Generates J σ) (g : W ⟶ X) : GeneratesAlong (J.comap g) σ g := by
  refine ⟨by rw [← Scheme.Hom.preimage_iSup, hJ.1, Scheme.Hom.preimage_top], fun k A h => le_antisymm ?_ ?_⟩
  · intro s hs
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := appLE_mem_ideal_comap (J.comap g) A.1.ι A ⟨⊤, isAffineOpen_top _⟩ hA hs
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := hJ.ideal_comap_top_le (A.1.ι ≫ g) k (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.span _), Ideal.mem_comap, Ideal.map_span,
      ← Set.range_comp]
    convert h2 using 3
    funext j
    exact appLE_appLE _ _ h hA _
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine mem_ideal_of_locally _ _ _ fun y hy => ?_
    obtain ⟨V, B, hV, hB, hBV, hyB⟩ := exists_affine_pair g (L.U k) A.1 y hy (h hy)
    refine ⟨B, hB, hyB, ?_⟩
    have h1 : resG X hV ((σ j).f k) ∈ J.ideal V := by
      rw [hJ.2 k V hV]
      exact Ideal.subset_span ⟨j, rfl⟩
    have h2 := appLE_mem_ideal_comap J g V B hBV h1
    rw [appLE_resG] at h2
    rwa [resG_appLE]

/- English proof (translation)
The claim follows from `hJ.generatesAlong_comap g`.
-/
theorem generatesAlong_comap_of_generates (X W : Scheme.{0}) (J : X.IdealSheafData) (L : LB X) (m : ℕ)
    (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (hJ : Generates J σ) : GeneratesAlong (J.comap g) σ g :=
  hJ.generatesAlong_comap g

end GlobalTheory.ProjBlowup
