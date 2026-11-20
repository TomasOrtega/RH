import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefExistsFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EmbGramDetConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecInjectiveMapOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LcvSub

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, Complex.ofReal_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.cnorm`. Use `congr 1`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem cnorm_mulVec_eq {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m k ℂ) (B : Matrix n k ℂ) (h : Aᴴ * A = Bᴴ * B) (u : k → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ u) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  apply Complex.ofReal_injective
  rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.fcoord`. Use `congr 1`.
-/
theorem fcoord_std {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  congr 1

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply]`.
-/
theorem gram_eq {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))ᴴ *
      ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply]

/- English proof (translation)
Establish `h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1`. Use extensionality with `a b`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hab, Matrix.one_apply]`. Rewrite using `[gram_eq, h, Matrix.mul_one]`.
-/
theorem gram_single {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  have h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Matrix.one_apply]
  rw [gram_eq, h, Matrix.mul_one]

end GlobalTheory.LcvSub

open GlobalTheory.LcvSub in

/- English proof (translation)
Introduce `K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint`. Use `set j := Formalism.HN.rkK L with hj`. Set `W : Submodule K (Fin d → K)` to `Submodule.span K (L : Set (Fin d → K))`. Set `b : Module.Basis (Fin j) K W` to `Module.finBasis K W`. Set `e : Fin j → Fin d → K` to `fun a => (b a : Fin d → K)`.

Establish `he : LinearIndependent K e` using `b.linearIndependent.map' W.subtype W.ker_subtype`. Set `ψ : (Fin j → K) →ₗ[K] (Fin d → K)` to `W.subtype ∘ₗ b.equivFun.symm.toLinearMap`. Establish `hψ : Function.Injective ψ` using `W.injective_subtype.comp b.equivFun.symm.injective`. Establish `hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x`. Introduce `x`.

Use extensionality with `i`. Simplify using `[ψ, e, Matrix.mulVec, dotProduct, mul_comm]`. Establish `hrange : LinearMap.range ψ = W`. Simplify using `[ψ, LinearMap.range_comp]`. Take `⟨hne, hpos⟩` from `GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he`.

Use `choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)`. Set `L' : Submodule (𝓞 K) (Fin j → K)` to `L.comap (ψ.restrictScalars (𝓞 K))`. Establish `hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L`. Apply `Submodule.map_comap_eq_self` to reduce the goal to its premises. Introduce `x hx`.

Establish `: x ∈ LinearMap.range ψ`. Rewrite using `[hrange]`. Conclude with `Submodule.subset_span hx`. Conclude with `this`. Establish `hfg : L'.FG` using `Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)`.

Establish `hlat : Submodule.IsLattice K L'`. Use `⟨hfg, ?_⟩` and prove the remaining obligations. Apply `Submodule.map_injective_of_injective hψ` to reduce the goal to its premises. Rewrite using `[← Submodule.span_image, Submodule.map_top, hrange]`. Establish `: ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K))`.

Rewrite using `[← hmap]`. Both sides reduce to the same expression. Rewrite using `[this]`. Establish `hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x`. Introduce `v x`.

Unfold `Formalism.HermitianLatticesTheory.normAt`. Rewrite using `[fcoord_std, fcoord_std, cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]`. Use `congr 2`. Use extensionality with `i`. Rewrite using `[hψE]`.

Simplify using `[Matrix.mulVec, dotProduct]`. Establish `hht` using `(Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X' (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1`. Rewrite `hht` using `[hmap]`. Establish `hlcv : lcv X L = lcv X' L'`. Unfold `lcv`.

Rewrite using `[hht]`. Rewrite using `[hlcv]`. Use `GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' hlat ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e`. Simplify using `only [gram_single, hX'g]`.

Conclude with `h`. Introduce `x hx y hy`. Establish `h` using `hint (ψ x) hx (ψ y) hy`. Establish `hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) = ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ)`. Use extensionality with `a c`.

Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite `h` using `[hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[hG]`. Conclude with `h`.
-/
theorem GlobalTheory.neg_rank_mul_log_le_lcv : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint
  classical
  set j := Formalism.HN.rkK L with hj
  let W : Submodule K (Fin d → K) := Submodule.span K (L : Set (Fin d → K))
  let b : Module.Basis (Fin j) K W := Module.finBasis K W
  let e : Fin j → Fin d → K := fun a => (b a : Fin d → K)
  have he : LinearIndependent K e := b.linearIndependent.map' W.subtype W.ker_subtype
  let ψ : (Fin j → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Injective ψ := W.injective_subtype.comp b.equivFun.symm.injective
  have hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x := by
    intro x
    ext i
    simp [ψ, e, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : LinearMap.range ψ = W := by
    simp [ψ, LinearMap.range_comp]
  obtain ⟨hne, hpos⟩ := GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he
  choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)
  let L' : Submodule (𝓞 K) (Fin j → K) := L.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have : x ∈ LinearMap.range ψ := by
      rw [hrange]; exact Submodule.subset_span hx
    exact this
  have hfg : L'.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)
  have hlat : Submodule.IsLattice K L' := by
    refine ⟨hfg, ?_⟩
    apply Submodule.map_injective_of_injective hψ
    rw [← Submodule.span_image, Submodule.map_top, hrange]
    have : ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K)) := by
      rw [← hmap]; rfl
    rw [this]
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x := by
    intro v x
    unfold Formalism.HermitianLatticesTheory.normAt
    rw [fcoord_std, fcoord_std,
      cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))
        (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]
    congr 2
    ext i
    rw [hψE]
    simp [Matrix.mulVec, dotProduct]
  have hht := (Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X'
    (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1
  rw [hmap] at hht
  have hlcv : lcv X L = lcv X' L' := by
    unfold lcv; rw [hht]
  rw [hlcv]
  refine GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' hlat ?_
  · have h := GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e
    simp only [gram_single, hX'g]
    exact h
  · intro x hx y hy
    have h := hint (ψ x) hx (ψ y) hy
    have hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) =
        ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ) := by
      ext a c
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] at h
    rw [hG]
    exact h
