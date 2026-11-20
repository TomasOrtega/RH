import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartAlgebra
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothEtaleChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Rewrite using `[sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_comp_appLE]`.
-/
theorem sectionsAlgebraMap_comp_appLE (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) :
    (h.appLE W V e).hom.comp (sectionsAlgebraMap k p W) = sectionsAlgebraMap k (h ≫ p) V := by
  rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a`.
-/
theorem sectionsAlgebraMap_appLE_apply (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) (a : k) :
    (h.appLE W V e).hom (sectionsAlgebraMap k p W a) = sectionsAlgebraMap k (h ≫ p) V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a

/- English proof (translation)
Take `⟨⟨a, t⟩, hmul⟩` from `(IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers f) (S := S)).mp hx`. Establish `hmul' : algebraMap R S (x * (t : R)) = algebraMap R S (a : R)`. Rewrite using `[map_mul]`. Conclude with `hmul`. Take `⟨c, hceq⟩` from `(IsLocalization.eq_iff_exists (M := Submonoid.powers f) (S := S)).mp hmul'`.

Take `⟨i, hi⟩` from `t.2`. Take `⟨j, hj⟩` from `c.2`. Establish `hi' : f ^ i = (t : R)` using `hi`. Establish `hj' : f ^ j = (c : R)` using `hj`. Use `⟨i + j, ?_⟩` and prove the remaining obligations.

Establish `key : f ^ (i + j) * x = f ^ j * (x * f ^ i)` using `by ring`. Rewrite using `[key, hi', hj', hceq]`. Conclude with `N.mul_mem_left _ a.2`.
-/
private theorem exists_pow_mul_mem_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (N : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ N.map (algebraMap R S)) : ∃ n : ℕ, f ^ n * x ∈ N := by
  obtain ⟨⟨a, t⟩, hmul⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers f) (S := S)).mp hx
  have hmul' : algebraMap R S (x * (t : R)) = algebraMap R S (a : R) := by
    rw [map_mul]
    exact hmul
  obtain ⟨c, hceq⟩ :=
    (IsLocalization.eq_iff_exists (M := Submonoid.powers f) (S := S)).mp hmul'
  obtain ⟨i, hi⟩ := t.2
  obtain ⟨j, hj⟩ := c.2
  have hi' : f ^ i = (t : R) := hi
  have hj' : f ^ j = (c : R) := hj
  refine ⟨i + j, ?_⟩
  have key : f ^ (i + j) * x = f ^ j * (x * f ^ i) := by ring
  rw [key, hi', hj', hceq]
  exact N.mul_mem_left _ a.2

/- English proof (translation)
Substitute `hAB` using the available equality. Conclude with `h`.
-/
private theorem idealSheafData_ideal_le_congr {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    {A B : Y.affineOpens} (hAB : A = B) (h : J₁.ideal B ≤ J₂.ideal B) :
    J₁.ideal A ≤ J₂.ideal A := by
  subst hAB
  exact h

/- English proof (translation)
Introduce `x hx`. Use `set s : Set Γ(Y, U.1) := {f : Γ(Y, U.1) | ∃ n : ℕ, f ^ n * x ∈ J₂.ideal U} with hs`. Establish `hcover : U.1 ≤ ⨆ f : s, Y.basicOpen (f : Γ(Y, U.1))`. Introduce `z hz`. Take `⟨V, hV, hzV, hle⟩` from `H z`.

Take `⟨f, g, hfg, hzf⟩` from `exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩`. Establish `hres : Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₁.ideal U) ≤ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₂.ideal U)`. Rewrite using `[J₁.map_ideal_basicOpen U f, J₂.map_ideal_basicOpen U f]`. Establish `hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U` using `⟨V, hV⟩) g := Subtype.ext hfg`. Use `idealSheafData_ideal_le_congr J₁ J₂ hABO ?_` and prove the remaining obligations.

Rewrite using `[← J₁.map_ideal_basicOpen ⟨V, hV⟩ g, ← J₂.map_ideal_basicOpen ⟨V, hV⟩ g]`. Conclude with `Ideal.map_mono hle`. Establish `hfs : f ∈ s`. Use `U.2.isLocalization_basicOpen f` as an intermediate fact. Rewrite using `[hs]`.

Use `exists_pow_mul_mem_of_mem_map (S := Γ(Y, Y.basicOpen f)) f (J₂.ideal U) x ?_` and prove the remaining obligations. Establish `halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f)) = (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom` using `rfl`. Rewrite using `[halg]`. Conclude with `hres (Ideal.mem_map_of_mem _ hx)`. Conclude with `Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩`.

Establish `hspan : Ideal.span s = ⊤` using `(U.2.self_le_iSup_basicOpen_iff).mp hcover`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem (J₂.ideal U) s hspan x ?_` and prove the remaining obligations. Introduce and unpack `⟨f, hf⟩`. Rewrite `hf` using `[hs]`. Take `⟨n, hn⟩` from `hf`.

Conclude with `⟨n, by rw [smul_eq_mul]; exact hn⟩`.
-/
private theorem idealSheafData_ideal_le_of_locally_le {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ ≤ J₂.ideal ⟨V, hV⟩) (U : Y.affineOpens) :
    J₁.ideal U ≤ J₂.ideal U := by
  intro x hx
  set s : Set Γ(Y, U.1) := {f : Γ(Y, U.1) | ∃ n : ℕ, f ^ n * x ∈ J₂.ideal U} with hs
  have hcover : U.1 ≤ ⨆ f : s, Y.basicOpen (f : Γ(Y, U.1)) := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := H z
    obtain ⟨f, g, hfg, hzf⟩ := exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩
    have hres : Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₁.ideal U)
        ≤ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₂.ideal U) := by
      rw [J₁.map_ideal_basicOpen U f, J₂.map_ideal_basicOpen U f]
      have hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U := ⟨V, hV⟩) g := Subtype.ext hfg
      refine idealSheafData_ideal_le_congr J₁ J₂ hABO ?_
      rw [← J₁.map_ideal_basicOpen ⟨V, hV⟩ g, ← J₂.map_ideal_basicOpen ⟨V, hV⟩ g]
      exact Ideal.map_mono hle
    have hfs : f ∈ s := by
      have := U.2.isLocalization_basicOpen f
      rw [hs]
      refine exists_pow_mul_mem_of_mem_map (S := Γ(Y, Y.basicOpen f)) f (J₂.ideal U) x ?_
      have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f))
          = (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
      rw [halg]
      exact hres (Ideal.mem_map_of_mem _ hx)
    exact Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩
  have hspan : Ideal.span s = ⊤ := (U.2.self_le_iSup_basicOpen_iff).mp hcover
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J₂.ideal U) s hspan x ?_
  rintro ⟨f, hf⟩
  rw [hs] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩

/- English proof (translation)
Establish `key : ∀ U : Y.affineOpens, J₁.ideal U = J₂.ideal U`. Introduce `U`. Use `le_antisymm (idealSheafData_ideal_le_of_locally_le J₁ J₂ ?_ U) (idealSheafData_ideal_le_of_locally_le J₂ J₁ ?_ U)` and prove the remaining obligations. Introduce `y`. Take `⟨V, hV, h1, h2⟩` from `H y`.

Conclude with `⟨V, hV, h1, h2.le⟩`. Introduce `y`. Take `⟨V, hV, h1, h2⟩` from `H y`. Conclude with `⟨V, hV, h1, h2.ge⟩`. Conclude with `Scheme.IdealSheafData.ext (funext key)`.
-/
private theorem idealSheafData_eq_of_locally_eq {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ = J₂.ideal ⟨V, hV⟩) : J₁ = J₂ := by
  have key : ∀ U : Y.affineOpens, J₁.ideal U = J₂.ideal U := by
    intro U
    refine le_antisymm (idealSheafData_ideal_le_of_locally_le J₁ J₂ ?_ U)
      (idealSheafData_ideal_le_of_locally_le J₂ J₁ ?_ U)
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.le⟩
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.ge⟩
  exact Scheme.IdealSheafData.ext (funext key)

attribute [local instance] EtaleCoordinates.sumEvalAlgebra in
/- English proof (translation)
Take `⟨W₀, m, hxW₀, -, ⟨c₀⟩⟩` from `exists_etaleChart p (h.base y)`. Take `⟨W, V, d, e, hW, hV, hyV, hWW₀, -, g, hgE, hg⟩` from `SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W₀ hxW₀ ⊤ (by trivial)`. Use `⟨V, hV, hyV, ?_⟩` and prove the remaining obligations. Establish `: Etale g` using `hgE`. Set `c : EtaleChart p W m` to `c₀.restrict hWW₀`.

Set `instkS : Algebra k Γ(X, W)` to `sectionsAlgebra k p W`. Set `instkT : Algebra k Γ(Y, V)` to `sectionsAlgebra k (h ≫ p) V`. Set `instPS : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W)` to `c.algebra`. Set `instTow1 : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W)` to `c.isScalarTower`. Establish `instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W)` using `c.algebra_formallyEtale hW`.

Set `instChartAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)` to `chartAlgebra hW g`. Establish `instFE2 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)` using `chartAlgebra_formallyEtale hW hV g`. Set `instST : Algebra Γ(X, W) Γ(Y, V)` to `(h.appLE W V e).hom.toAlgebra`. Set `instTowkST : IsScalarTower k Γ(X, W) Γ(Y, V)` to `IsScalarTower.of_algebraMap_eq fun a => (sectionsAlgebraMap_appLE_apply k p h W V e a).symm`. Set `instScalarTowerChart : IsScalarTower Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)` to `chartAlgebra_isScalarTower hW h e g hg`.

Set `instSumT : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V)` to `((algebraMap (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)).comp (algebraMap (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)))).toAlgebra`. Set `instScalarTowerSum : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)` to `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `instTowkSum : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V)`. Establish `: IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W))` using `EtaleCoordinates.sumEvalAlgebra_isScalarTower k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W)`. Use `IsScalarTower.of_algebraMap_eq fun a => ?_` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) (algebraMap k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) a), ← IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin …`. Establish `instFE3 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V)` using `EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W) Γ(Y, V)`. Establish `hcoord : ∀ i : ULift.{u} (Fin m), algebraMap Γ(X, W) Γ(Y, V) (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W) i) = EtaleCoordinates.coord k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i)`. Introduce `i`. Rewrite using `[EtaleCoordinates.coord_def k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i), IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V), EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (F …`.

Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]`. Simplify using `only [derivIdealSheaf_ideal]`. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]`. Conclude with `(EtaleCoordinates.map_derivIdeal_sum k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W) Γ(Y, V) hcoord (I.ideal ⟨W, hW⟩)).symm`.
-/
private theorem exists_affineOpen_derivIdealSheaf_comap_ideal_eq (k : Type u) [Field k] [IsNoetherianRing k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      (derivIdealSheaf k (h ≫ p) (I.comap h)).ideal ⟨V, hV⟩
        = ((derivIdealSheaf k p I).comap h).ideal ⟨V, hV⟩ := by
  classical
  obtain ⟨W₀, m, hxW₀, -, ⟨c₀⟩⟩ := exists_etaleChart p (h.base y)
  obtain ⟨W, V, d, e, hW, hV, hyV, hWW₀, -, g, hgE, hg⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W₀ hxW₀ ⊤ (by trivial)
  refine ⟨V, hV, hyV, ?_⟩
  have : Etale g := hgE
  let c : EtaleChart p W m := c₀.restrict hWW₀
  let instkS : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instkT : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  let instPS : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.algebra
  let instTow1 : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.isScalarTower
  have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    c.algebra_formallyEtale hW
  let instChartAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have instFE2 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  let instST : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let instTowkST : IsScalarTower k Γ(X, W) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (sectionsAlgebraMap_appLE_apply k p h W V e a).symm
  let instScalarTowerChart : IsScalarTower Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_isScalarTower hW h e g hg
  let instSumT : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    ((algebraMap (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)).comp
      (algebraMap (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)))).toAlgebra
  let instScalarTowerSum : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTowkSum : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := by
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) :=
      EtaleCoordinates.sumEvalAlgebra_isScalarTower k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W)
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) a),
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      IsScalarTower.algebraMap_apply k Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      ← IsScalarTower.algebraMap_apply k Γ(X, W) Γ(Y, V)]
  have instFE3 : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W) Γ(Y, V)
  have hcoord : ∀ i : ULift.{u} (Fin m),
      algebraMap Γ(X, W) Γ(Y, V) (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W) i)
        = EtaleCoordinates.coord k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V)
            (Sum.inl i) := by
    intro i
    rw [EtaleCoordinates.coord_def k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i),
      IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W),
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]
  simp only [derivIdealSheaf_ideal]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]
  exact (EtaleCoordinates.map_derivIdeal_sum k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
    Γ(X, W) Γ(Y, V) hcoord (I.ideal ⟨W, hW⟩)).symm

/- English proof (translation)
The claim follows from `idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h I y`.
-/
theorem derivIdealSheaf_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) :
    derivIdealSheaf k (h ≫ p) (I.comap h) = (derivIdealSheaf k p I).comap h :=
  idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h I y

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => rfl`. Consider the case `succ r ih`. Rewrite using `[derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih, derivIdealSheaf_comap k p h (derivIdealSheafIterate k p r I)]`.
-/
theorem derivIdealSheafIterate_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k (h ≫ p) r (I.comap h) = (derivIdealSheafIterate k p r I).comap h := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih,
      derivIdealSheaf_comap k p h (derivIdealSheafIterate k p r I)]

end FunctorialResolution.EmbeddedResolution
