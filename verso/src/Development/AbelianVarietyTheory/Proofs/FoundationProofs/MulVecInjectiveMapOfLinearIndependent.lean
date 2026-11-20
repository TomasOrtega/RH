import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

/- English proof (translation)
Use `letI : Algebra K L := σ.toAlgebra`. Rewrite using `[Matrix.mulVec_injective_iff]`. Establish `h` using `(linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he`. Conclude with `h`.
-/
theorem mulVec_injective_map_of_linearIndependent {K L : Type} [Field K] [Field L] (σ : K →+* L) {d j : ℕ}
    (e : Fin j → Fin d → K) (he : LinearIndependent K e) :
    Function.Injective (((Matrix.of e)ᵀ).map σ).mulVec := by
  letI : Algebra K L := σ.toAlgebra
  rw [Matrix.mulVec_injective_iff]
  have h := (linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he
  exact h

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]`. Rewrite using `[Matrix.mul_apply]`. Both sides reduce to the same expression.
-/
theorem gram_eq_conjTranspose_mul {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding)ᴴ * ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
  rw [Matrix.mul_apply]
  rfl

/- English proof (translation)
Introduce `K _ _ _ _ v0 hv0 d j H X hX e he`. Establish `hpos : ∀ v, (gram X v e).PosDef`. Introduce `v`. Rewrite using `[gram_eq_conjTranspose_mul]`. Use `Matrix.PosDef.conjTranspose_mul_self _ ?_` and prove the remaining obligations.

Establish `h1 : Function.Injective ((X v)⁻¹).mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))`. Establish `h2` using `mulVec_injective_map_of_linearIndependent v.embedding e he`. Introduce `x y hxy`. Rewrite `hxy` using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Conclude with `h2 (h1 hxy)`.

Use `⟨?_, hpos⟩` and prove the remaining obligations. Establish `key : v0.embedding (gramR H e) = (gram X v0 e).det`. Unfold `gramR`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 1`.

Use `set σ := v0.embedding`. Establish `hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹` using `(hX v0).2.symm`. Use extensionality with `a b`. Rewrite using `[Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]`. Establish `hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b)`.

Use function extensionality and compare the values at `fun i => RingHom.map_mulVec σ _ _ i`. Establish `hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a)`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, Pi.star_apply]`. Rewrite using `[← starRingEnd_apply]`.

Conclude with `hv0 (e a i)`. Rewrite using `[hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Simplify using `only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]`. Both sides reduce to the same expression. Introduce `h0`.

Rewrite `key` using `[h0, map_zero]`. Conclude with `(hpos v0).det_pos.ne key`.
-/
theorem gramR_ne_zero_and_gram_posDef : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsMetric H X → ∀ e : Fin j → Fin d → K, LinearIndependent K e → gramR H e ≠ 0 ∧ ∀ v, (gram X v e).PosDef := by
  intro K _ _ _ _ v0 hv0 d j H X hX e he
  have hpos : ∀ v, (gram X v e).PosDef := by
    intro v
    rw [gram_eq_conjTranspose_mul]
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    have h1 : Function.Injective ((X v)⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))
    have h2 := mulVec_injective_map_of_linearIndependent v.embedding e he
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact h2 (h1 hxy)
  refine ⟨?_, hpos⟩
  have key : v0.embedding (gramR H e) = (gram X v0 e).det := by
    unfold gramR
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    set σ := v0.embedding
    have hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ := (hX v0).2.symm
    ext a b
    rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]
    have hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b) :=
      funext fun i => RingHom.map_mulVec σ _ _ i
    have hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a) := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply]
      rw [← starRingEnd_apply]
      exact hv0 (e a i)
    rw [hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
    rfl
  intro h0
  rw [h0, map_zero] at key
  exact (hpos v0).det_pos.ne key

end GlobalTheory.TestLat
