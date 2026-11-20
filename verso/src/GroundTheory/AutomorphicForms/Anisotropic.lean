import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
import GroundTheory.AutomorphicForms.AnisotropicDivisionCompact
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Unitary

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

/- English proof (translation)
Unfold `hermValue`. Express the relevant statement in the definitionally equal form `((Algebra.TensorProduct.lid K E : K ⊗[K] E ≃ₐ[K] E) : K ⊗[K] E →+* E) (_ ⬝ᵥ _) = _`. Rewrite using `[RingHom.map_dotProduct]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, RingHom.coe_coe]`. Conclude with `lid_conjBase (ξ i)`. Use function extensionality and compare the values at `i`. Rewrite using `[Function.comp_apply, RingHom.map_mulVec]`. Use `congr 1`.

Use extensionality with `a c`. Simplify using `[baseMatrix]`.
-/
theorem lid_hermValue (ξ : ι → K ⊗[K] E) :
    Algebra.TensorProduct.lid K E (hermValue K H K ξ) =
      (fun i => conj K E (Algebra.TensorProduct.lid K E (ξ i))) ⬝ᵥ
        (H *ᵥ fun i => Algebra.TensorProduct.lid K E (ξ i)) := by
  unfold hermValue
  change ((Algebra.TensorProduct.lid K E : K ⊗[K] E ≃ₐ[K] E) : K ⊗[K] E →+* E) (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  congr 1
  · funext i
    simp only [Function.comp_apply, RingHom.coe_coe]
    exact lid_conjBase (ξ i)
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a c
    simp [baseMatrix]

/- English proof (translation)
Introduce `ξ hξ`. Establish `h1` using `haniso (fun i => Algebra.TensorProduct.lid K E (ξ i)) (by rw [← lid_hermValue, hξ, map_zero])`. Use function extensionality and compare the values at `i`. Conclude with `(Algebra.TensorProduct.lid K E).injective (by simpa using congrFun h1 i)`.
-/
theorem anisotropic_tensor (haniso : ∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0) :
    ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0 := by
  intro ξ hξ
  have h1 := haniso (fun i => Algebra.TensorProduct.lid K E (ξ i))
    (by rw [← lid_hermValue, hξ, map_zero])
  funext i
  exact (Algebra.TensorProduct.lid K E).injective (by simpa using congrFun h1 i)

variable [NumberField K]

/- English proof (translation)
The claim follows from `compactSpace_unitaryQuotient_of_anisotropic' H hH (anisotropic_tensor H haniso)`.
-/
theorem compactSpace_unitaryQuotient_of_anisotropic (hH : IsUnit H.det)
    (haniso : ∀ x : ι → E, (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ x) = 0 → x = 0) :
    CompactSpace (RightCosetSpace (unitaryDiagonal K H).range) :=
  compactSpace_unitaryQuotient_of_anisotropic' H hH (anisotropic_tensor H haniso)

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

end Unitary

section Division

variable (K : Type*) [Field K] [NumberField K] (D : Type*) [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D]

attribute [local instance] adeleTensorTopology isModuleTopology_adeleTensor
  isTopologicalRing_adeleTensor t2Space_adeleTensor

variable {K D} {d : ℕ} (b : Basis (Fin d) K D)

/- English proof (translation)
Use `set t : ℝ := (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K d (rmatUnits b 𝔸[K] x)) : ℝ) with ht`. Establish `htpos : 0 < t` using `(GroundTheory.Global.IdeleGroup.ideleModule K _).2`. Establish `hn : 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `hd` using `pos_of_basis b`. Use `set ρ : ℝ := t⁻¹ ^ ((1 : ℝ) / ((Module.finrank ℚ K * d : ℕ) : ℝ)) with hρdef`.

Establish `hρ : 0 < ρ` using `Real.rpow_pos_of_pos (inv_pos.2 htpos) _`. Establish `hρpow : ρ ^ (Module.finrank ℚ K * d) = t⁻¹`. Rewrite using `[hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 htpos.le), one_div_mul_cancel (by positivity), Real.rpow_one]`. Use `⟨Reduction.posIdele ρ hρ, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_normOneUnits, Reduction.mem_normOneGL]`.

Establish `hdet : AdelicGLn.det K d (rmatUnits b 𝔸[K] (scalarUnits K D (Reduction.posIdele ρ hρ) * x)) = Reduction.posIdele ρ hρ ^ d * AdelicGLn.det K d (rmatUnits b 𝔸[K] x)`. Use `ext`. Simplify using `only [map_mul, Units.val_mul, Units.val_pow_eq_pow_val, AdelicGLn.coe_det, rmatUnits_val]`. Use `congr 1`. Establish `hs : rmat b 𝔸[K] (scalarUnits K D (Reduction.posIdele ρ hρ) : 𝔸[K] ⊗[K] D) = algebraMap 𝔸[K] (Matrix (Fin d) (Fin d) 𝔸[K]) ((Reduction.posIdele (K` using `K) ρ hρ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) := (rmatHom b 𝔸[K]).commutes (Reduction.posIdele (K := K) ρ hρ : 𝔸[K])`.

Rewrite using `[hs, Matrix.algebraMap_eq_diagonal, det_diagonal]`. Simplify using the standard rewrite rules. Rewrite using `[hdet, map_mul, map_pow]`. Simplify using `only [Positive.val_mul, Positive.val_pow, Reduction.ideleModule_posIdele]`. Rewrite using `[← ht, ← pow_mul, hρpow, inv_mul_cancel₀ htpos.ne']`.
-/
theorem exists_scalar_mem_normOneUnits (x : (𝔸[K] ⊗[K] D)ˣ) :
    ∃ a : (𝔸[K])ˣ, scalarUnits K D a * x ∈ normOneUnits b := by
  set t : ℝ := (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K d (rmatUnits b 𝔸[K] x)) : ℝ)
    with ht
  have htpos : 0 < t := (GroundTheory.Global.IdeleGroup.ideleModule K _).2
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hd := pos_of_basis b
  set ρ : ℝ := t⁻¹ ^ ((1 : ℝ) / ((Module.finrank ℚ K * d : ℕ) : ℝ)) with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos (inv_pos.2 htpos) _
  have hρpow : ρ ^ (Module.finrank ℚ K * d) = t⁻¹ := by
    rw [hρdef, ← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.2 htpos.le),
      one_div_mul_cancel (by positivity), Real.rpow_one]
  refine ⟨Reduction.posIdele ρ hρ, ?_⟩
  rw [mem_normOneUnits, Reduction.mem_normOneGL]
  have hdet : AdelicGLn.det K d (rmatUnits b 𝔸[K] (scalarUnits K D (Reduction.posIdele ρ hρ) * x)) =
      Reduction.posIdele ρ hρ ^ d * AdelicGLn.det K d (rmatUnits b 𝔸[K] x) := by
    ext
    simp only [map_mul, Units.val_mul, Units.val_pow_eq_pow_val, AdelicGLn.coe_det, rmatUnits_val]
    congr 1
    have hs : rmat b 𝔸[K] (scalarUnits K D (Reduction.posIdele ρ hρ) : 𝔸[K] ⊗[K] D) =
        algebraMap 𝔸[K] (Matrix (Fin d) (Fin d) 𝔸[K])
          ((Reduction.posIdele (K := K) ρ hρ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) :=
      (rmatHom b 𝔸[K]).commutes (Reduction.posIdele (K := K) ρ hρ : 𝔸[K])
    rw [hs, Matrix.algebraMap_eq_diagonal, det_diagonal]
    simp
  rw [hdet, map_mul, map_pow]
  simp only [Positive.val_mul, Positive.val_pow, Reduction.ideleModule_posIdele]
  rw [← ht, ← pow_mul, hρpow, inv_mul_cancel₀ htpos.ne']

end Division

end Anisotropic

end

end GroundTheory.Automorphic
