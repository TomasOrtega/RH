import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisIntegerActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectorEigenDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisActionOnModelStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

/- English proof (translation)
Introduce `F _ _ K _ _ χ`. Establish `hinj : Function.Injective χ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `h0`.

Establish `ha0 : (a : F) ≠ 0` using `fun h => h0 (RingOfIntegers.coe_eq_zero_iff.1 h)`. Take `⟨y, hy0, hyi⟩` from `exists_integral_multiples ℤ ℚ ({((a : F))⁻¹} : Finset F)`. Set `b : 𝓞 F` to `⟨y • (a : F)⁻¹, hyi _ (Finset.mem_singleton_self _)⟩`. Establish `hb : ((y : ℤ) : 𝓞 F) = a * b`. Apply `RingOfIntegers.ext` to reduce the goal to its premises.

Use `show ((y : 𝓞 F) : F) = (a : F) * (y • (a : F)⁻¹)`. Rewrite using `[zsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ ha0, mul_one]`. Use `push_cast`. Both sides reduce to the same expression. Establish `h2` using `congrArg χ hb`.

Rewrite `h2` using `[map_intCast, map_mul, ha, zero_mul]`. Conclude with `hy0 (Int.cast_eq_zero.1 h2)`. Conclude with `⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩`.
-/
theorem exists_ext_of_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (K : Type) [Field K] [CharZero K]
    (χ : 𝓞 F →+* K), ∃ φ : F →+* K, φ.comp (algebraMap (𝓞 F) F) = χ := by
  intro F _ _ K _ _ χ
  have hinj : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have ha0 : (a : F) ≠ 0 := fun h => h0 (RingOfIntegers.coe_eq_zero_iff.1 h)
    obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ ({((a : F))⁻¹} : Finset F)
    let b : 𝓞 F := ⟨y • (a : F)⁻¹, hyi _ (Finset.mem_singleton_self _)⟩
    have hb : ((y : ℤ) : 𝓞 F) = a * b := by
      apply RingOfIntegers.ext
      show ((y : 𝓞 F) : F) = (a : F) * (y • (a : F)⁻¹)
      rw [zsmul_eq_mul, mul_left_comm, mul_inv_cancel₀ ha0, mul_one]
      push_cast
      rfl
    have h2 := congrArg χ hb
    rw [map_intCast, map_mul, ha, zero_mul] at h2
    exact hy0 (Int.cast_eq_zero.1 h2)
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

end GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase

open GlobalTheory.ShFam.Pad.Guard in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Z R _ x τ g e he`. Take `⟨ρ, hρ⟩` from `GlobalTheory.T.tangent_basis_integer_action E H Z.X Z.t R x g e he`. Set `κ : 𝓞 c.F →+* R` to `(Spec.preimage (x ≫ Z.s)).hom`. Establish `hκ : spMap κ = x ≫ Z.s` using `Spec.map_preimage _`. Take `⟨D, P, hD, hPP, hP⟩` from `GlobalTheory.T.exists_projector_eigen_decomposition E H l c R κ g ρ τ`.

Establish `hb` using `fun {K : Type} [CommRing K] (ψ : R →+* K) => GlobalTheory.HTPres.isTanBasis_map Z.t he ψ`. Establish `hcomp : ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F)`. Introduce `K _ ψ φ h`. Apply `GlobalTheory.ShFam.EigLoc.spMap_inj` to reduce the goal to its premises. Rewrite using `[← h, ← hκ]`.

Conclude with `Spec.map_comp _ _`. Establish `heig : ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K), spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∀ (cf : Fin g → K) w, IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ (P.map ψ).mulVec cf = (D : K …`. Introduce `K _ ψ φ hφ cf w hw`. Rewrite using `[← hP K ψ φ (hcomp K ψ φ hφ) cf]`. Establish `hu` using `(hb ψ).1`.

Establish `ht` using `comb_tan hu hw`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hE⟩ a`. Establish `h1` using `hρ K ψ a cf w hw`. Establish `h2` using `comb_smul hu hw (φ (embK c τ a))`.

Rewrite `h2` using `[← hE a]`. Conclude with `(he.2 K ψ _ (comb_tan hu h1)).unique h1 h2`. Introduce `h`. Use `⟨ht, fun a => ?_⟩` and prove the remaining obligations. Establish `h1` using `hρ K ψ a cf w hw`.

Rewrite `h1` using `[h a]`. Conclude with `comb_unique hu h1 (comb_smul hu hw _)`. Use `⟨D, P, hD, ⟨hPP, heig⟩, ?_⟩` and prove the remaining obligations. Introduce `K _ _ ψ`. Take `⟨φ, hφ⟩` from `exists_ext_of_ringOfIntegers c.F K (ψ.comp κ)`.

Establish `hφ' : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F))`. Rewrite using `[hφ, ← hκ]`. Conclude with `(Spec.map_comp _ _).symm`. Take `⟨V, hV, hVm⟩` from `GlobalTheory.T.tangent_basis_action_on_model E H Dw l Xo c Z R x τ g e he K ψ φ hφ'`. Establish `hDK : (D : K) ≠ 0` using `Nat.cast_ne_zero.2 hD`.

Establish `hPK : P.map ψ * P.map ψ = (D : K) • P.map ψ`. Rewrite using `[← Matrix.map_mul, hPP]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hV' : V = LinearMap.range (P.map ψ).mulVecLin`.

Use extensionality with `cf`. Take `⟨w, -, hw⟩` from `exists_comb (hb ψ).1 cf`. Rewrite using `[← hVm cf w hw, heig K ψ φ hφ' cf w hw]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `⟨(D : K)⁻¹ • cf, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mulVec_smul, h, smul_smul, hDK]`. Introduce and unpack `⟨y, rfl⟩ show (P.map ψ).mulVec ((P.map ψ).mulVec y) = (D : K) • (P.map ψ).mulVec y`. Rewrite using `[Matrix.mulVec_mulVec, hPK]`. Apply the tactic sequence `first | exact Matrix.smul_mulVec _ _ _ | exact Matrix.smul_mulVec_assoc _ _ _ | simp [Matrix.smul_mulVec]`.

Rewrite using `[Matrix.rank, ← hV', hV]`.
-/
theorem exists_isEigProj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (R : Type) [CommRing R] (x : Sp R ⟶ Z.X) (τ : E →+* ℂ) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Z.t.G.left)), GlobalTheory.LineNorm.IsTanBasis Z.t x e → ∃ (D : ℕ) (P : Matrix (Fin g) (Fin g) R), D ≠ 0 ∧ IsEigProj Z x τ e D P ∧ ∀ (K : Type) [Field K] [CharZero K] (ψ : R →+* K), (P.map ψ).rank = Dw.mult τ := by
  intro E _ _ _ H Dw l Xo c Z R _ x τ g e he
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.tangent_basis_integer_action E H Z.X Z.t R x g e he
  let κ : 𝓞 c.F →+* R := (Spec.preimage (x ≫ Z.s)).hom
  have hκ : spMap κ = x ≫ Z.s := Spec.map_preimage _
  obtain ⟨D, P, hD, hPP, hP⟩ := GlobalTheory.T.exists_projector_eigen_decomposition E H l c R κ g ρ τ
  have hb := fun {K : Type} [CommRing K] (ψ : R →+* K) => GlobalTheory.HTPres.isTanBasis_map Z.t he ψ
  have hcomp : ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K),
      spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) →
      ψ.comp κ = φ.comp (algebraMap (𝓞 c.F) c.F) := by
    intro K _ ψ φ h
    apply GlobalTheory.ShFam.EigLoc.spMap_inj
    rw [← h, ← hκ]
    exact Spec.map_comp _ _
  have heig : ∀ (K : Type) [CommRing K] (ψ : R →+* K) (φ : c.F →+* K),
      spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) → ∀ (cf : Fin g → K) w,
      IsCombAtG Z.t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w →
      (IsEigTan Z φ (spMap ψ ≫ x) τ w ↔ (P.map ψ).mulVec cf = (D : K) • cf) := by
    intro K _ ψ φ hφ cf w hw
    rw [← hP K ψ φ (hcomp K ψ φ hφ) cf]
    have hu := (hb ψ).1
    have ht := comb_tan hu hw
    constructor
    · rintro ⟨-, hE⟩ a
      have h1 := hρ K ψ a cf w hw
      have h2 := comb_smul hu hw (φ (embK c τ a))
      rw [← hE a] at h2
      exact (he.2 K ψ _ (comb_tan hu h1)).unique h1 h2
    · intro h
      refine ⟨ht, fun a => ?_⟩
      have h1 := hρ K ψ a cf w hw
      rw [h a] at h1
      exact comb_unique hu h1 (comb_smul hu hw _)
  refine ⟨D, P, hD, ⟨hPP, heig⟩, ?_⟩
  intro K _ _ ψ
  obtain ⟨φ, hφ⟩ := exists_ext_of_ringOfIntegers c.F K (ψ.comp κ)
  have hφ' : spMap ψ ≫ x ≫ Z.s = spMap (φ.comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [hφ, ← hκ]
    exact (Spec.map_comp _ _).symm
  obtain ⟨V, hV, hVm⟩ := GlobalTheory.T.tangent_basis_action_on_model E H Dw l Xo c Z R x τ g e he K ψ φ hφ'
  have hDK : (D : K) ≠ 0 := Nat.cast_ne_zero.2 hD
  have hPK : P.map ψ * P.map ψ = (D : K) • P.map ψ := by
    rw [← Matrix.map_mul, hPP]
    ext i j
    simp
  have hV' : V = LinearMap.range (P.map ψ).mulVecLin := by
    ext cf
    obtain ⟨w, -, hw⟩ := exists_comb (hb ψ).1 cf
    rw [← hVm cf w hw, heig K ψ φ hφ' cf w hw]
    constructor
    · intro h
      refine ⟨(D : K)⁻¹ • cf, ?_⟩
      simp [Matrix.mulVec_smul, h, smul_smul, hDK]
    · rintro ⟨y, rfl⟩
      show (P.map ψ).mulVec ((P.map ψ).mulVec y) = (D : K) • (P.map ψ).mulVec y
      rw [Matrix.mulVec_mulVec, hPK]
      first | exact Matrix.smul_mulVec _ _ _ | exact Matrix.smul_mulVec_assoc _ _ _ | simp [Matrix.smul_mulVec]
  rw [Matrix.rank, ← hV', hV]

end GlobalTheory.ArLieBase

end
