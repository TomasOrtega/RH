import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyExt
import ReciprocityTheory.GaloisValuations.Global

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ExtConj
variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]`. Break down `eq_or_ne y 0 with rfl | hy` into its components or cases. Simplify using the standard rewrite rules. Establish `h0 : 0 < e.w y` using `e.w.pos hy`. Simplify using `only [hy, false_or, not_le, one_lt_inv₀ h0]`.

Conclude with `⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩`.
-/
theorem valuation_lt_one_iff {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgebraicClosure F) :
    e.O.valuation y < 1 ↔ e.w y < 1 := by
  rw [ReciprocityTheory.Gal.valuation_lt_one_iff', e.mem_O, e.mem_O, map_inv₀]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < e.w y := e.w.pos hy
    simp only [hy, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]`. Conclude with `FinitePlace.norm_lt_one_iff_mem F v x`.
-/
theorem lies_over {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (x : 𝓞 F) :
    e.O.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
  rw [valuation_lt_one_iff, e.w_alg, ← FinitePlace.norm_embedding]
  exact FinitePlace.norm_lt_one_iff_mem F v x

/- English proof (translation)
Take `⟨g, hg⟩` from `ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')`. Use `⟨g⁻¹, ?_⟩` and prove the remaining obligations. Set `u : AbsoluteValue (AlgebraicClosure F) ℝ` to `e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective`. Establish `hu (x) : u x = e.w (g⁻¹ x)` using `rfl`. Establish `he : u.IsEquiv e'.w` using `AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by`.

Rewrite using `[hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]`. Take `⟨c, hc, hce⟩` from `AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot`. Establish `h1 : e'.w (algebraMap F _ (a : F)) < 1` using `(valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)`. Establish `h0 : 0 < e'.w (algebraMap F _ (a : F))` using `e'.w.pos (by simpa using ha0)`.

Establish `h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F))`. Rewrite using `[hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]`. Establish `h3` using `congrFun hce (algebraMap F _ (a : F))`. Simplify using `only [h2] at h3`. Establish `hc1 : c = 1`.

Establish `h4` using `congrArg Real.log h3`. Rewrite `h4` using `[Real.log_rpow h0]`. Use `(Real.log_neg h0 h1).ne` as an intermediate fact. Conclude with `mul_right_cancel₀ this (by rw [h4, one_mul])`. Introduce `x`.

Rewrite using `[← hu, ← hce, hc1]`. Simplify using the standard rewrite rules.
-/
theorem conj (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v) :
    ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) := by
  obtain ⟨g, hg⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over (lies_over e) (lies_over e')
  refine ⟨g⁻¹, ?_⟩
  let u : AbsoluteValue (AlgebraicClosure F) ℝ :=
    e.w.comp (f := (g⁻¹ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).toRingEquiv.toRingHom) (g⁻¹).injective
  have hu (x) : u x = e.w (g⁻¹ x) := rfl
  have he : u.IsEquiv e'.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rw [hu, ← valuation_lt_one_iff, ← valuation_lt_one_iff, ← hg, ReciprocityTheory.Gal.smul_valuation_lt_one_iff]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have h1 : e'.w (algebraMap F _ (a : F)) < 1 := (valuation_lt_one_iff e' _).1 ((lies_over e' a).2 ha)
  have h0 : 0 < e'.w (algebraMap F _ (a : F)) := e'.w.pos (by simpa using ha0)
  have h2 : u (algebraMap F _ (a : F)) = e'.w (algebraMap F _ (a : F)) := by
    rw [hu, AlgEquiv.commutes, e.w_alg, e'.w_alg]
  have h3 := congrFun hce (algebraMap F _ (a : F))
  simp only [h2] at h3
  have hc1 : c = 1 := by
    have h4 := congrArg Real.log h3
    rw [Real.log_rpow h0] at h4
    have := (Real.log_neg h0 h1).ne
    exact mul_right_cancel₀ this (by rw [h4, one_mul])
  intro x
  rw [← hu, ← hce, hc1]
  simp

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩`.
-/
theorem factor {K : Type} [Field K] {X : Scheme.{0}} (y : Sp K ⟶ X) (x : X) (h : below y = x) :
    ∃ ψ : X.residueField x ⟶ CommRingCat.of K, Spec.map ψ ≫ X.fromSpecResidueField x = y := by
  subst h
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X y⟩

/- English proof (translation)
The claim follows from `(Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)`.
-/
theorem below_comp {K : Type} [Field K] {X : Scheme.{0}} (x : X) (ψ : X.residueField x ⟶ CommRingCat.of K) :
    below (K := K) (Spec.map ψ ≫ X.fromSpecResidueField x) = x :=
  (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply x _)

/- English proof (translation)
Use `isClosed_singleton_iff_isClosedImmersion.1 hx` as an intermediate fact. Take `⟨φ, hφ⟩` from `Spec.map_surjective (X.fromSpecResidueField x ≫ s)`. Establish `hfin : IsFinite (Spec.map φ)`. Rewrite using `[hφ]`. Conclude with `isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance`.

Use `letI : Algebra k (X.residueField x) := φ.hom.toAlgebra`. Use `haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin`. Establish `hP (ψ : X.residueField x →ₐ[k] K) : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K)`. Establish `h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K)` using `CommRingCat.hom_ext ψ.comp_algebraMap`. Rewrite using `[Category.assoc, ← hφ, ← Spec.map_comp]`.

Conclude with `congrArg Spec.map h`. Set `P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x}` to `fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩, below_comp x _⟩`. Use `⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨y, hy⟩, hyx⟩`. Take `⟨ψ, h⟩` from `factor y x hyx`.

Establish `h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K))`. Rewrite using `[Spec.map_comp, hφ, ← Category.assoc, h]`. Conclude with `hy`. Establish `h3` using `Spec.map_injective h2`. Conclude with `⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩`.
-/
theorem closed_point_geometric_fibres_finite {k K : Type} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nonempty {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} ∧
      Finite {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[k] K) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s = spMap (algebraMap k K) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap k K) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[k] K) → {y : {y : Sp K ⟶ X // y ≫ s = spMap (algebraMap k K)} // below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      below_comp x _⟩
  refine ⟨⟨P IsAlgClosed.lift⟩, Finite.of_surjective P ?_⟩
  rintro ⟨⟨y, hy⟩, hyx⟩
  obtain ⟨ψ, h⟩ := factor y x hyx
  have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [Spec.map_comp, hφ, ← Category.assoc, h]
    exact hy
  have h3 := Spec.map_injective h2
  exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩

/- English proof (translation)
The claim follows from `closed_point_geometric_fibres_finite Y.str x hx`.
-/
theorem pts (Y : Var F) (x : Y.X) (hx : IsClosed ({x} : Set Y.X)) :
    Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x} :=
  closed_point_geometric_fibres_finite Y.str x hx

/- English proof (translation)
Introduce `_ _ _` and use `⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] , (∀ v : HeightOneSpectrum (𝓞 F), Nonempty (Ext v)) ∧ (∀ Y : Var F, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → Nonempty {y : AlgPt Y // below y.1 = x} ∧ Finite {y : AlgPt Y // below y.1 = x}) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)) (e e' : Ext v), ∃ g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, ∀ x, e'.w x = e.w (g x) :=
  fun _ _ _ => ⟨GlobalTheory.TrueGeoModel.nonempty_ext, pts, conj⟩

end GlobalTheory.TrueGeo.ExtConj
