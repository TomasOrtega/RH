import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J L hL hdual hdet`. Take `⟨y, hy, hyJ⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hdet`. Establish `hmem : ∀ c : E, c • y ∈ L`. Introduce `c`. Rewrite using `[hdual]`.

Introduce `x _ o`. Establish `h0 : form σ J (c • y) x = 0`. Unfold `form`. Rewrite using `[Matrix.dotProduct_mulVec, Matrix.smul_vecMul, hyJ, smul_zero, zero_dotProduct]`. Rewrite using `[h0, mul_zero, map_zero]`.

Conclude with `isIntegral_zero`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hy`. Establish `hi' : y i ≠ 0` using `hi`. Establish `htop : L.map (LinearMap.proj (R` using `𝓞 E) (φ := fun _ : Fin n => E) i) = ⊤ := by`. Rewrite using `[eq_top_iff]`.

Introduce `e _`. Use `⟨(e / y i) • y, hmem _, ?_⟩` and prove the remaining obligations. Simplify using `[hi']`. Establish `hfin : Module.Finite (𝓞 E) E` using `⟨htop ▸ hL.fg.map _⟩`. Conclude with `RingOfIntegers.not_isField E (isField_of_isIntegral_of_isField (R := 𝓞 E) (S := E) (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField E))`.
-/
theorem det_ne_zero_of_lattice_trace_selfDual :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.IsLattice E →
    (∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) → J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ n J L hL hdual hdet
  obtain ⟨y, hy, hyJ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hmem : ∀ c : E, c • y ∈ L := by
    intro c
    rw [hdual]
    intro x _ o
    have h0 : form σ J (c • y) x = 0 := by
      unfold form
      rw [Matrix.dotProduct_mulVec, Matrix.smul_vecMul, hyJ, smul_zero, zero_dotProduct]
    rw [h0, mul_zero, map_zero]
    exact isIntegral_zero
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hy
  have hi' : y i ≠ 0 := hi
  have htop : L.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) i) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    refine ⟨(e / y i) • y, hmem _, ?_⟩
    simp [hi']
  have hfin : Module.Finite (𝓞 E) E := ⟨htop ▸ hL.fg.map _⟩
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (R := 𝓞 E) (S := E)
      (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField E))

end GlobalTheory
