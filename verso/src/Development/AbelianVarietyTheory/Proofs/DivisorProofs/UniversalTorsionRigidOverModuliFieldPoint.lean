import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TorsRigid

/- English proof (translation)
Use `letI := σ.toAlgebra`. Use `haveI : Flat (spMap σ) := by`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Use `haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩`.

Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c φ K L _ _ y x hx κ₁ κ₂ hκ`. Take `⟨⟨p, ψ⟩, hyp⟩` from `(Scheme.SpecToEquivOfField K (Xo.XF c)).symm.surjective y`. Set `k : Type` to `(Xo.XF c).residueField p`. Set `y₀ : Sp k ⟶ Xo.XF c` to `(Xo.XF c).fromSpecResidueField p`. Set `φ' : k →+* K` to `ψ.hom`.

Establish `hy : y = spMap φ' ≫ y₀` using `hyp.symm`. Set `K'` to `AlgebraicClosure K`. Set `ιK : K →+* K'` to `algebraMap K K'`. Use `haveI := epi_spMap_field ιK`. Set `j : Over.mk (spMap (ιK.comp φ') ≫ y₀ ≫ pullback.fst _ _) ⟶ Over.mk (y ≫ pullback.fst _ _)` to `Over.homMk (spMap ιK) (by`.

Simplify using `only [Over.mk_hom, hy, Category.assoc]`. Rewrite using `[← Category.assoc (spMap ιK), ← spMap_comp])`. Establish `hx' : (j ≫ x) ^ l.M' = 1` using `by rw [← MonObj.comp_pow, hx, MonObj.comp_one]`. Take `⟨x₀, -, hx₀⟩` from `GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint Xo c φ k K' (ιK.comp φ') y₀ (j ≫ x) hx'`. Establish `hxl : x.left = spMap φ' ≫ x₀.left`.

Rewrite using `[← cancel_epi (spMap ιK)]`. Establish `: spMap ιK ≫ x.left = spMap (ιK.comp φ') ≫ x₀.left` using `hx₀`. Rewrite using `[this, ← Category.assoc, ← spMap_comp]`. Establish `hκ' : κ₁ ≫ spMap φ' = κ₂ ≫ spMap φ'`. Rewrite using `[← cancel_mono y₀]`.

Simplify `hκ` using `only [hy, Category.assoc]`. Rewrite using `[hxl, ← Category.assoc, hκ', Category.assoc]`.
-/
theorem torsion_rigid : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K L : Type) [Field K] [Field L] (y : Sp K ⟶ Xo.XF c) (x : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∀ κ₁ κ₂ : Sp L ⟶ Sp K, κ₁ ≫ y = κ₂ ≫ y → κ₁ ≫ x.left = κ₂ ≫ x.left := by
  intro E _ _ _ H Dw l Xo c φ K L _ _ y x hx κ₁ κ₂ hκ
  obtain ⟨⟨p, ψ⟩, hyp⟩ := (Scheme.SpecToEquivOfField K (Xo.XF c)).symm.surjective y
  let k : Type := (Xo.XF c).residueField p
  let y₀ : Sp k ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField p
  let φ' : k →+* K := ψ.hom
  have hy : y = spMap φ' ≫ y₀ := hyp.symm
  let K' := AlgebraicClosure K
  let ιK : K →+* K' := algebraMap K K'
  haveI := epi_spMap_field ιK
  let j : Over.mk (spMap (ιK.comp φ') ≫ y₀ ≫ pullback.fst _ _) ⟶
      Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap ιK) (by
      simp only [Over.mk_hom, hy, Category.assoc]
      rw [← Category.assoc (spMap ιK), ← spMap_comp])
  have hx' : (j ≫ x) ^ l.M' = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨x₀, -, hx₀⟩ := GlobalTheory.T.universalAbelianScheme_torsion_rational_fieldPoint Xo c φ k K' (ιK.comp φ') y₀ (j ≫ x) hx'
  have hxl : x.left = spMap φ' ≫ x₀.left := by
    rw [← cancel_epi (spMap ιK)]
    have : spMap ιK ≫ x.left = spMap (ιK.comp φ') ≫ x₀.left := hx₀
    rw [this, ← Category.assoc, ← spMap_comp]
  have hκ' : κ₁ ≫ spMap φ' = κ₂ ≫ spMap φ' := by
    rw [← cancel_mono y₀]
    simpa only [hy, Category.assoc] using hκ
  rw [hxl, ← Category.assoc, hκ', Category.assoc]

end GlobalTheory.TorsRigid
