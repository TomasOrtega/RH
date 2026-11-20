import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormLocSplit

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h v τ z hz`. Establish `hN : algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z) = z * cA σ z` using `GlobalTheory.Doubling.algebraMap_norm_eq h z`. Establish `hinj : Function.Injective (algebraMap (AF F) (AE F E))` using `Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective`. Use `⟨fun u hu => hinj ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : u • (z - 1) = 0` using `hz u hu`.

Establish `h2 : u • (cA σ z - 1) = 0`. Use `congrArg (cA σ) h1` as an intermediate fact. Rewrite `this` using `[map_smul, map_sub, map_one, map_zero]`. Then use the resulting hypothesis. Rewrite using `[smul_eq_mul, map_mul, map_sub, map_one, hN, map_zero, ← Algebra.smul_def, show z * cA σ z - 1 = (z - 1) * cA σ z + (cA σ z - 1) by ring, smul_add, ← smul_mul_assoc, h1, h2, zero_mul, add_zero]`. Establish `h3` using `congrArg (piW τ) hN`.

Establish `hc : piW τ (cA σ z) = piW (τ.comp σ) z`. Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v (sigR (AF F) σ z)) = splitProj (τ.comp σ) (compFin F E v z)`. Establish `hs : ∀ y : AE F E, compFin F E v (sigR (AF F) σ y) = sigR (Fv F v) σ (compFin F E v y)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Rewrite using `[hs, splitProj_comp]`. Establish `ha : piW τ (algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z)) = evFin F v (Algebra.norm (AF F) z)`.

Express the relevant statement in the definitionally equal form `splitProj τ (compFin F E v (Algebra.norm (AF F) z ⊗ₜ[F] 1)) = _`. Simplify using `[compFin]`. Rewrite `h3` using `[map_mul, hc, ha]`. Conclude with `h3`.
-/
theorem norm_at_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl F) (τ : E →ₐ[F] Fv F v) (z : AE F E), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  intro F E _ _ _ _ _ σ h v τ z hz
  have hN : algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z) = z * cA σ z :=
    GlobalTheory.Doubling.algebraMap_norm_eq h z
  have hinj : Function.Injective (algebraMap (AF F) (AE F E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := AF F) (algebraMap F E).injective
  refine ⟨fun u hu => hinj ?_, ?_⟩
  · have h1 : u • (z - 1) = 0 := hz u hu
    have h2 : u • (cA σ z - 1) = 0 := by
      have := congrArg (cA σ) h1
      rwa [map_smul, map_sub, map_one, map_zero] at this
    rw [smul_eq_mul, map_mul, map_sub, map_one, hN, map_zero, ← Algebra.smul_def,
      show z * cA σ z - 1 = (z - 1) * cA σ z + (cA σ z - 1) by ring, smul_add, ← smul_mul_assoc, h1, h2,
      zero_mul, add_zero]
  · have h3 := congrArg (piW τ) hN
    have hc : piW τ (cA σ z) = piW (τ.comp σ) z := by
      change splitProj τ (compFin F E v (sigR (AF F) σ z)) = splitProj (τ.comp σ) (compFin F E v z)
      have hs : ∀ y : AE F E, compFin F E v (sigR (AF F) σ y) = sigR (Fv F v) σ (compFin F E v y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => rfl
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [hs, splitProj_comp]
    have ha : piW τ (algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z)) = evFin F v (Algebra.norm (AF F) z) := by
      change splitProj τ (compFin F E v (Algebra.norm (AF F) z ⊗ₜ[F] 1)) = _
      simp [compFin]
    rw [map_mul, hc, ha] at h3
    exact h3

end GlobalTheory.NormLocSplit
