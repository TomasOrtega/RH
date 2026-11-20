import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

/- English proof (translation)
Establish `hx : below y = x`. Rewrite using `[← hy]`. Conclude with `Scheme.fromSpecResidueField_apply x _`. Substitute `hx` using the available equality. Establish `hσ : σ = Z.descResidueField (Scheme.stalkClosedPointTo y)`.

Rewrite using `[← Spec.map_inj, ← cancel_mono (Z.fromSpecResidueField _), hy]`. Conclude with `(Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z y).symm`. Establish `h : RegAt (below y) (algebraMap _ Z.functionField a)` using `⟨a, rfl⟩`. Establish `e : h.choose = a` using `IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec`. Rewrite using `[valAt, dif_pos h, e, hσ]`.

Both sides reduce to the same expression.
-/
theorem valAt_eq_of_residueField_hom {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (x : Z)
    (σ : Z.residueField x ⟶ CommRingCat.of K) (hy : Spec.map σ ≫ Z.fromSpecResidueField x = y)
    (a : Z.presheaf.stalk x) :
    valAt y (algebraMap _ Z.functionField a) = σ.hom ((Z.residue x).hom a) := by
  have hx : below y = x := by
    rw [← hy]
    exact Scheme.fromSpecResidueField_apply x _
  subst hx
  have hσ : σ = Z.descResidueField (Scheme.stalkClosedPointTo y) := by
    rw [← Spec.map_inj, ← cancel_mono (Z.fromSpecResidueField _), hy]
    exact (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z y).symm
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  have e : h.choose = a := IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec
  rw [valAt, dif_pos h, e, hσ]
  rfl

/- English proof (translation)
Take `⟨a, ha, rfl⟩` from `hf`. Use `isClosed_singleton_iff_isClosedImmersion.mp hx` as an intermediate fact. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)`. Establish `hfin : IsFinite (Spec.map ψ)`. Rewrite using `[hψ]`.

Conclude with `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance`. Use `letI : Algebra F (Y.X.residueField x) := ψ.hom.toAlgebra`. Use `haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff ψ).1 hfin`. Establish `hα : (Y.X.residue x).hom a ≠ 0` using `(ha.map _).ne_zero`. Use `⟨Algebra.norm F ((Y.X.residue x).hom a), Algebra.norm_ne_zero_iff.2 hα, fun K _ _ φ => ?_⟩` and prove the remaining obligations.

Use `letI : Algebra F K := φ.toAlgebra`. Set `g : (Y.X.residueField x →ₐ[F] K) → {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ}` to `fun σ => ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Y.X.fromSpecResidueField x, by`. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `c`.

Conclude with `σ.commutes c⟩`. Establish `hinj : Function.Injective g` using `fun σ τ h => by`. Establish `h1` using `congrArg Subtype.val h`. Simplify using `only [g, cancel_mono, Spec.map_inj] at h1`. Conclude with `AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)`.

Establish `hr : {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x} = Set.range g`. Use extensionality with `⟨y, hy⟩`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Express the relevant statement in the definitionally equal form `below y = x at h`.

Establish `h2 : Spec.map ((Y.X.residueFieldCongr h.symm).hom ≫ Y.X.descResidueField (Scheme.stalkClosedPointTo y)) ≫ Y.X.fromSpecResidueField x = y`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]`. Conclude with `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y.X y`. Generalize the expression as in `(Y.X.residueFieldCongr h.symm).hom ≫ Y.X.descResidueField (Scheme.stalkClosedPointTo y) = s at h2`. Establish `h3 : ψ ≫ s = CommRingCat.ofHom φ`.

Rewrite using `[← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, h2, hy]`. Conclude with `⟨⟨s.hom, fun c => congrArg (fun t => t.hom c) h3⟩, Subtype.ext h2⟩`. Introduce and unpack `⟨σ, hσ⟩`. Rewrite using `[← hσ]`. Conclude with `Scheme.fromSpecResidueField_apply x _`.

Use `⟨hr ▸ Set.finite_range g, ?_⟩` and prove the remaining obligations. Establish `key` using `finprod_mem_range (f := fun y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} => valAt y.1 (algebraMap _ Y.X.functionField a)) hinj`. Rewrite `key` using `[← hr]`. Use `Eq.trans key ?_` and prove the remaining obligations. Rewrite using `[finprod_eq_prod_of_fintype]`.

Use `Eq.trans ?_ (Algebra.norm_eq_prod_embeddings F K ((Y.X.residue x).hom a)).symm` and prove the remaining obligations. Conclude with `Finset.prod_congr rfl fun σ _ => valAt_eq_of_residueField_hom _ x _ rfl a`.
-/
theorem exists_finprod_valAt_eq (F : Type) [Field F] [NumberField F] (Y : Var F) (x : Y.X)
    (hx : IsClosed ({x} : Set Y.X)) (f : Y.Fn) (hf : UnitAt x f) :
    ∃ N : F, N ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : F →+* K),
      {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x}.Finite ∧
      ∏ᶠ (y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ}) (_ : below y.1 = x), valAt y.1 f = φ N := by
  obtain ⟨a, ha, rfl⟩ := hf
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.X.fromSpecResidueField x ≫ Y.str)
  have hfin : IsFinite (Spec.map ψ) := by
    rw [hψ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (Y.X.residueField x) := ψ.hom.toAlgebra
  haveI : Module.Finite F (Y.X.residueField x) := (IsFinite.SpecMap_iff ψ).1 hfin
  have hα : (Y.X.residue x).hom a ≠ 0 := (ha.map _).ne_zero
  refine ⟨Algebra.norm F ((Y.X.residue x).hom a), Algebra.norm_ne_zero_iff.2 hα, fun K _ _ φ => ?_⟩
  letI : Algebra F K := φ.toAlgebra
  let g : (Y.X.residueField x →ₐ[F] K) → {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} := fun σ =>
    ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Y.X.fromSpecResidueField x, by
      rw [Category.assoc, ← hψ, ← Spec.map_comp]
      congr 1
      ext c
      exact σ.commutes c⟩
  have hinj : Function.Injective g := fun σ τ h => by
    have h1 := congrArg Subtype.val h
    simp only [g, cancel_mono, Spec.map_inj] at h1
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1)
  have hr : {y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} | below y.1 = x} = Set.range g := by
    ext ⟨y, hy⟩
    constructor
    · intro h
      change below y = x at h
      have h2 : Spec.map ((Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y)) ≫ Y.X.fromSpecResidueField x = y := by
        rw [Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
        exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y.X y
      generalize (Y.X.residueFieldCongr h.symm).hom ≫
          Y.X.descResidueField (Scheme.stalkClosedPointTo y) = s at h2
      have h3 : ψ ≫ s = CommRingCat.ofHom φ := by
        rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, h2, hy]
      exact ⟨⟨s.hom, fun c => congrArg (fun t => t.hom c) h3⟩, Subtype.ext h2⟩
    · rintro ⟨σ, hσ⟩
      rw [← hσ]
      exact Scheme.fromSpecResidueField_apply x _
  refine ⟨hr ▸ Set.finite_range g, ?_⟩
  have key := finprod_mem_range (f := fun y : {y : Sp K ⟶ Y.X // y ≫ Y.str = spMap φ} =>
    valAt y.1 (algebraMap _ Y.X.functionField a)) hinj
  rw [← hr] at key
  refine Eq.trans key ?_
  rw [finprod_eq_prod_of_fintype]
  refine Eq.trans ?_ (Algebra.norm_eq_prod_embeddings F K ((Y.X.residue x).hom a)).symm
  exact Finset.prod_congr rfl fun σ _ => valAt_eq_of_residueField_hom _ x _ rfl a

end GlobalTheory.TrueGeo
