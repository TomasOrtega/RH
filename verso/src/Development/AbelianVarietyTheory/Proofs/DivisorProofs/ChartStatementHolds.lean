import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineTangentBasisLocally
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LineNorm

namespace GlobalTheory.FlatModel

/- English proof (translation)
Establish `hC : IsOpen (irreducibleComponent z)` using `GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)`. Take `⟨U, hU, hzU, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := X) (x := z) (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩`. Establish `hpre : IsPreirreducible (U : Set X)` using `(isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2 fun q hq => (hle hq).2`. Establish `hirr : IsIrreducible (U : Set X)` using `⟨⟨z, hzU⟩, hpre⟩`. Establish `: IrreducibleSpace U.toScheme` using `Subtype.irreducibleSpace hirr`.

Establish `: Nonempty U` using `⟨⟨z, hzU⟩⟩`. Establish `: IsIntegral U.toScheme` using `GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _`. Establish `: Nonempty (Spec Γ(X, U))` using `⟨hU.isoSpec.hom ⟨z, hzU⟩⟩`. Establish `: IsIntegral (Spec Γ(X, U))` using `isIntegral_of_isOpenImmersion hU.isoSpec.inv`. Establish `hd : IsDomain Γ(X, U)` using `(affine_isIntegral_iff _).1 this`.

Conclude with `⟨U, hU, hd, hzU, fun q hq => (hle hq).1, (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩`.
-/
theorem exists_affine_normal_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l' Xo' c' W Y p hp hW x`. Establish `hN : GlobalTheory.IsNormalScheme Y.X` using `(GlobalTheory.isNormalScheme_iff _).2 Y.normal`. Use `GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff c' hp.ne_zero hW` as an intermediate fact. Establish `: IsProper Y.s` using `projProper _ _ _ Y.proj`. Establish `: IsLocallyNoetherian Y.X` using `LocallyOfFiniteType.isLocallyNoetherian Y.s`.

Take `⟨V, g, e, hxV, he⟩` from `exists_affine_isTanBasis E H Y.X Y.t Y.X (𝟙 _) x`. Take `⟨U, hU, hd, hxU, hle, hic⟩` from `exists_affine_normal_domain V.1 hxV`. Take `⟨ρ, eρ⟩ : ∃ ρ : Γ(Y.X, V.1) →+* Γ(Y.X, U), spMap ρ ≫ V.2.fromSpec = hU.fromSpec` from `⟨(Y.X.presheaf.map (homOfLE hle).op).hom, V.2.map_fromSpec hU _⟩`. Establish `hb` using `isTanBasis_bc he ρ`. Rewrite `hb` using `[Category.comp_id, eρ]`.

Use `⟨Γ(Y.X, U), inferInstance, hd, hic, hU.fromSpec, g, _, inferInstance, ?_, hb⟩` and prove the remaining obligations. Rewrite using `[hU.range_fromSpec]`. Conclude with `hxU`.
-/
theorem chartSt : ChartSt := by
  intro E _ _ _ H Dw l' Xo' c' W Y p hp hW x
  have hN : GlobalTheory.IsNormalScheme Y.X := (GlobalTheory.isNormalScheme_iff _).2 Y.normal
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff c' hp.ne_zero hW
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  obtain ⟨V, g, e, hxV, he⟩ := exists_affine_isTanBasis E H Y.X Y.t Y.X (𝟙 _) x
  obtain ⟨U, hU, hd, hxU, hle, hic⟩ := exists_affine_normal_domain V.1 hxV
  obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Y.X, V.1) →+* Γ(Y.X, U), spMap ρ ≫ V.2.fromSpec = hU.fromSpec :=
    ⟨(Y.X.presheaf.map (homOfLE hle).op).hom, V.2.map_fromSpec hU _⟩
  have hb := isTanBasis_bc he ρ
  rw [Category.comp_id, eρ] at hb
  refine ⟨Γ(Y.X, U), inferInstance, hd, hic, hU.fromSpec, g, _, inferInstance, ?_, hb⟩
  rw [hU.range_fromSpec]
  exact hxU

end GlobalTheory.FlatModel

end
