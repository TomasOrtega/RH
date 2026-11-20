import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.MixHt

/- English proof (translation)
Introduce `k _ X p h ℓ U C hℓ hU hC hCc hfib hCU`. Take `⟨η, hη⟩` from `QuasiSober.sober hC hCc`. Use `set Y := GlobalTheory.MixHt.clo η`. Use `set i := GlobalTheory.MixHt.cloι η`. Establish `hgen : i (genericPoint Y) = η` using `GlobalTheory.MixHt.cloι_genericPoint η`.

Establish `hrange : i '' Set.univ = C`. Rewrite using `[← (genericPoint_spec Y).def, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, hgen, hη.def]`. Establish `htop : i ⁻¹ᵁ U = ⊤`. Use `top_unique fun y _ => ?_` and prove the remaining obligations. Conclude with `hCU (hrange ▸ Set.mem_image_of_mem i (Set.mem_univ y))`.

Establish `hV : IsAffineOpen (⊤ : Y.Opens)` using `htop ▸ hU.preimage i`. Establish `hA` using `h.sub i`. Use `hA.finite` as an intermediate fact. Establish `: IsProper (i ≫ p)`. Take `⟨N, j, _, hj⟩` from `hA.isProjOver`.

Use `isProper_str k N` as an intermediate fact. Conclude with `hj ▸ inferInstance`. Establish `hφ` using `isIntegral_appTop_of_universallyClosed (i ≫ p)`. Set `A` to `Γ(Sp k, ⊤)`. Set `R` to `Γ(Y, ⊤)`.

Set `e : A ≃+* k` to `(Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv`. Establish `hAint : Algebra.IsIntegral ℤ A` using `Algebra.IsIntegral.of_surjective e.symm.toRingHom.toIntAlgHom e.symm.surjective`. Use `letI : Algebra A R := (i ≫ p).appTop.hom.toAlgebra`. Establish `hRA : Algebra.IsIntegral A R` using `⟨hφ⟩`. Establish `hRint : Algebra.IsIntegral ℤ R` using `Algebra.IsIntegral.trans A`.

Establish `hchar : ((ℓ : ℕ) : R) = 0`. Establish `hcX : CharP (X.residueField η) ℓ` using `ringChar.eq_iff.mp (hfib hη.mem)`. Establish `h1 : ((ℓ : ℕ) : X.residueField (i (genericPoint Y))) = 0`. Rewrite using `[hgen]`. Conclude with `CharP.cast_eq_zero _ ℓ`.

Establish `h2 : ((ℓ : ℕ) : Y.residueField (genericPoint Y)) = 0`. Use `congrArg (i.residueFieldMap (genericPoint Y)).hom h1` as an intermediate fact. Simplify using `using this`. Establish `hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom)` using `(RingHom.injective (Y.residue (genericPoint Y)).hom).comp (germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial)`. Apply `hinj` to reduce the goal to its premises.

Simplify using `using h2`. Establish `: Fact ℓ.Prime` using `⟨hℓ⟩`. Establish `: CharP R ℓ` using `(CharP.charP_iff_prime_eq_zero hℓ).2 hchar`. Use `letI : Algebra (ZMod ℓ) R := ZMod.algebra R ℓ`. Establish `: Algebra.IsIntegral (ZMod ℓ) R` using `Algebra.IsIntegral.tower_top ℤ`.

Establish `hR : IsField R` using `isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))`. Establish `hdimY : topologicalKrullDim ((⊤ : Y.Opens) : Set Y) = 0`. Rewrite using `[topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]`. Conclude with `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans (ringKrullDim_eq_zero_of_isField hR)`. Rewrite using `[← hrange, GlobalTheory.MixHt.DimBasic.dim_image i.isClosedEmbedding.isEmbedding]`.

Rewrite `hdimY` using `[TopologicalSpace.Opens.coe_top]`. Conclude with `hdimY.le`.
-/
theorem dim_le_zero_of_fib_of_subset_affine : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), GlobalTheory.MixHt.IsAmb p → ∀ (ℓ : ℕ) (U : X.Opens) (C : Set X), ℓ.Prime → IsAffineOpen U → IsIrreducible C → IsClosed C → C ⊆ GlobalTheory.HSAmp.fib X ℓ → C ⊆ (U : Set X) → topologicalKrullDim C ≤ 0 := by
  intro k _ X p h ℓ U C hℓ hU hC hCc hfib hCU
  obtain ⟨η, hη⟩ := QuasiSober.sober hC hCc
  set Y := GlobalTheory.MixHt.clo η
  set i := GlobalTheory.MixHt.cloι η
  have hgen : i (genericPoint Y) = η := GlobalTheory.MixHt.cloι_genericPoint η
  have hrange : i '' Set.univ = C := by
    rw [← (genericPoint_spec Y).def, ← i.isClosedEmbedding.closure_image_eq, Set.image_singleton, hgen, hη.def]
  have htop : i ⁻¹ᵁ U = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hCU (hrange ▸ Set.mem_image_of_mem i (Set.mem_univ y))
  have hV : IsAffineOpen (⊤ : Y.Opens) := htop ▸ hU.preimage i
  have hA := h.sub i
  have := hA.finite
  have : IsProper (i ≫ p) := by
    obtain ⟨N, j, _, hj⟩ := hA.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance

  have hφ := isIntegral_appTop_of_universallyClosed (i ≫ p)
  let A := Γ(Sp k, ⊤)
  let R := Γ(Y, ⊤)
  let e : A ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have hAint : Algebra.IsIntegral ℤ A :=
    Algebra.IsIntegral.of_surjective e.symm.toRingHom.toIntAlgHom e.symm.surjective
  letI : Algebra A R := (i ≫ p).appTop.hom.toAlgebra
  have hRA : Algebra.IsIntegral A R := ⟨hφ⟩
  have hRint : Algebra.IsIntegral ℤ R := Algebra.IsIntegral.trans A

  have hchar : ((ℓ : ℕ) : R) = 0 := by
    have hcX : CharP (X.residueField η) ℓ := ringChar.eq_iff.mp (hfib hη.mem)
    have h1 : ((ℓ : ℕ) : X.residueField (i (genericPoint Y))) = 0 := by
      rw [hgen]; exact CharP.cast_eq_zero _ ℓ
    have h2 : ((ℓ : ℕ) : Y.residueField (genericPoint Y)) = 0 := by
      have := congrArg (i.residueFieldMap (genericPoint Y)).hom h1
      simpa using this
    have hinj : Function.Injective ((Y.residue (genericPoint Y)).hom.comp
        (Y.presheaf.germ ⊤ (genericPoint Y) trivial).hom) :=
      (RingHom.injective (Y.residue (genericPoint Y)).hom).comp
        (germ_injective_of_isIntegral Y (U := ⊤) (genericPoint Y) trivial)
    apply hinj
    simpa using h2

  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP R ℓ := (CharP.charP_iff_prime_eq_zero hℓ).2 hchar
  letI : Algebra (ZMod ℓ) R := ZMod.algebra R ℓ
  have : Algebra.IsIntegral (ZMod ℓ) R := Algebra.IsIntegral.tower_top ℤ
  have hR : IsField R := isField_of_isIntegral_of_isField' (Field.toIsField (ZMod ℓ))

  have hdimY : topologicalKrullDim ((⊤ : Y.Opens) : Set Y) = 0 := by
    rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding hV.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := R)).trans (ringKrullDim_eq_zero_of_isField hR)
  rw [← hrange, GlobalTheory.MixHt.DimBasic.dim_image i.isClosedEmbedding.isEmbedding]
  rw [TopologicalSpace.Opens.coe_top] at hdimY
  exact hdimY.le

end GlobalTheory.MixHt
