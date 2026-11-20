import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmulStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic

/- English proof (translation)
Use `set z : Fin N → Ω := c • fun j => algebraMap K Ω (y j) with hz`. Set `L : IntermediateField K Ω` to `IntermediateField.adjoin K {c}`. Establish `hcK : IsIntegral K c` using `((Algebra.IsAlgebraic.isAlgebraic (R := F) c).tower_top K).isIntegral`. Use `haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hcK`. Use `haveI : NumberField L := NumberField.of_module_finite K L`.

Establish `hcL : c ∈ L` using `IntermediateField.mem_adjoin_simple_self K c`. Establish `hle : coordField F z ≤ L.restrictScalars F`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `mul_mem hcL (L.algebraMap_mem (y j))`.

Set `ι : coordField F z →ₐ[F] L` to `IntermediateField.inclusion hle`. Use `letI : Algebra (coordField F z) L := ι.toRingHom.toAlgebra`. Use `haveI : IsScalarTower F (coordField F z) L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm`. Set `z' : Fin N → coordField F z` to `fun j => ⟨z j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩`. Set `c' : L` to `⟨c, hcL⟩`.

Establish `hc' : c' ≠ 0` using `fun h => hc (congrArg Subtype.val h)`. Establish `hyL : (fun j => algebraMap K L (y j)) ≠ 0` using `fun h => hy (funext fun j => (algebraMap K L).injective ((congrFun h j).trans (map_zero _).symm))`. Establish `he : (fun j => algebraMap (coordField F z) L (z' j)) = c' • fun j => algebraMap K L (y j)`. Use function extensionality and compare the values at `fun j => Subtype.ext rfl`. Establish `hz' : z' ≠ 0` using `fun h => smul_ne_zero hc' hyL (by`.

Rewrite using `[← he, h]`. Conclude with `funext fun j => map_zero _)`. Establish `h1` using `GlobalTheory.T.normalizedPointHeightLattice_algebraMap F (coordField F z) N n w A hw hA L z' hz'`. Establish `h2` using `GlobalTheory.T.normalizedPointHeightLattice_smul F L N n w A hw hA _ c' hyL hc'`. Establish `h3` using `GlobalTheory.T.normalizedPointHeightLattice_algebraMap F K N n w A hw hA L y hy`.

Rewrite `h1` using `[he, h2, h3]`. Conclude with `h1.symm`.
-/
theorem vecHeight_smul_algebraMap (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hw : Submodule.span F (Set.range w.col) = ⊤) (hA : ∀ σ, (A σ).det ≠ 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    (y : Fin N → K) (c : Ω) (hy : y ≠ 0) (hc : c ≠ 0) :
    vecHeight w A (c • fun j => algebraMap K Ω (y j)) = pointHeight w A y := by
  set z : Fin N → Ω := c • fun j => algebraMap K Ω (y j) with hz
  let L : IntermediateField K Ω := IntermediateField.adjoin K {c}
  have hcK : IsIntegral K c := ((Algebra.IsAlgebraic.isAlgebraic (R := F) c).tower_top K).isIntegral
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hcK
  haveI : NumberField L := NumberField.of_module_finite K L
  have hcL : c ∈ L := IntermediateField.mem_adjoin_simple_self K c
  have hle : coordField F z ≤ L.restrictScalars F := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨j, rfl⟩
    exact mul_mem hcL (L.algebraMap_mem (y j))
  let ι : coordField F z →ₐ[F] L := IntermediateField.inclusion hle
  letI : Algebra (coordField F z) L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (coordField F z) L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let z' : Fin N → coordField F z := fun j => ⟨z j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  let c' : L := ⟨c, hcL⟩
  have hc' : c' ≠ 0 := fun h => hc (congrArg Subtype.val h)
  have hyL : (fun j => algebraMap K L (y j)) ≠ 0 := fun h => hy (funext fun j =>
    (algebraMap K L).injective ((congrFun h j).trans (map_zero _).symm))
  have he : (fun j => algebraMap (coordField F z) L (z' j)) = c' • fun j => algebraMap K L (y j) :=
    funext fun j => Subtype.ext rfl
  have hz' : z' ≠ 0 := fun h => smul_ne_zero hc' hyL (by
    rw [← he, h]; exact funext fun j => map_zero _)
  have h1 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F (coordField F z) N n w A hw hA L z' hz'
  have h2 := GlobalTheory.T.normalizedPointHeightLattice_smul F L N n w A hw hA _ c' hyL hc'
  have h3 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F K N n w A hw hA L y hy
  rw [he, h2, h3] at h1
  exact h1.symm

end GlobalTheory.Adelic
