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

/- English proof (authored)
Sending a scalar first to W via p and then to V via h pulls the same base global section back along the composite morphism. Functoriality of pullback and restriction identifies this with the structure map for the composite on V.
-/
theorem sectionsAlgebraMap_comp_appLE (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) :
    (h.appLE W V e).hom.comp (sectionsAlgebraMap k p W) = sectionsAlgebraMap k (h ≫ p) V := by
  rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
    Scheme.Hom.appLE_comp_appLE]

/- English proof (authored)
Evaluate the compatibility of scalar maps with pullback at a.
-/
theorem sectionsAlgebraMap_appLE_apply (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (h : Y ⟶ X) (W : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ W) (a : k) :
    (h.appLE W V e).hom (sectionsAlgebraMap k p W a) = sectionsAlgebraMap k (h ≫ p) V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_appLE k p h W V e) a

/- English proof (authored)
Represent the image of x as a fraction with numerator in N and denominator a power of f. Equality in the localization implies equality after multiplying the cross-multiplied expressions by a further power of f. The resulting product of powers times x belongs to N.
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

/- English proof (authored)
Identify the affine opens by the given equality. The two section rings and their ideal values then coincide, and the stated inclusion transfers.
-/
private theorem idealSheafData_ideal_le_congr {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    {A B : Y.affineOpens} (hAB : A = B) (h : J₁.ideal B ≤ J₂.ideal B) :
    J₁.ideal A ≤ J₂.ideal A := by
  subst hAB
  exact h

/- English proof (authored)
Fix an element x of the ideal of the first sheaf on U. At every point of U choose an affine neighborhood where the local containment holds, then shrink to a common neighborhood principal in both affines. Ideal extension along the restriction preserves that local containment. Thus on the principal open in U the image of x lies in the localized ideal of the second sheaf. Clearing a power of the defining section puts a multiple of x in the second ideal on U. The defining sections of these principal opens generate the unit ideal because the opens cover U. The powers that kill the class of x modulo the second ideal also generate the unit ideal, so that class is zero.
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

/- English proof (authored)
The local equalities give local containments in both directions. Apply the result that local affine containments imply containment on each affine open. The two ideals thus agree on every affine open, which gives equality of the ideal sheaves.
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
/- English proof (authored)
Choose an étale chart around the image of y in X. Smoothness of h gives affine neighborhoods W of that image and V of y where h admits an étale chart over relative affine space over W. Shrink W inside the original chart and restrict it. The section ring of W is formally étale over the polynomial ring in its original coordinates. The section ring of V is formally étale over the polynomial ring over the sections of W in the relative coordinates. Composing gives formal étaleness over the polynomial ring over k in both sets of coordinates, where the original coordinates map to the corresponding first set. On V, pullback of each ideal sheaf extends its ideal on W along the section map. The ring-level equality for compatible old and new coordinates identifies the derivative ideal of the extended ideal with the extension of its original derivative ideal. This is the required equality on V.
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

/- English proof (authored)
At every point of Y the local smooth charts give an affine neighborhood where the two section ideals agree. Equality of ideal sheaves is local, so these affine equalities give the claimed equality.
-/
theorem derivIdealSheaf_comap (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) :
    derivIdealSheaf k (h ≫ p) (I.comap h) = (derivIdealSheaf k p I).comap h :=
  idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h I y

/- English proof (authored)
At zero both sides are the pullback of I. At each successor, apply the induction equality for the preceding iterate and then use the one-step result that the derivative ideal sheaf commutes with smooth pullback.
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
