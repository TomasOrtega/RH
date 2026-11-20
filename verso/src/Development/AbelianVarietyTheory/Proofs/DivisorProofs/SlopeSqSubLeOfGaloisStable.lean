import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan

open NumberField GlobalTheory.AllWt Module TensorProduct Matrix GlobalTheory.SlopeExt
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.SlopeGalois

/- English proof (translation)
Use `set d := (Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b with hd`. Set `A : Matrix ι (K' →ₐ[ℚ] ℂ) ℂ` to `fun r ρ => ρ (d r)`. Set `B : Matrix (K' →ₐ[ℚ] ℂ) ι ℂ` to `fun ρ r => ρ (b r)`. Establish `hAB : A * B = 1`. Use extensionality with `r t`.

Rewrite using `[Matrix.mul_apply]`. Establish `e : ∑ ρ : K' →ₐ[ℚ] ℂ, A r ρ * B ρ t = algebraMap ℚ ℂ (Algebra.trace ℚ K' (d r * b t))`. Rewrite using `[trace_eq_sum_embeddings]`. Conclude with `Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm`. Rewrite using `[e, ← Algebra.traceForm_apply, hd, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]`.

Distinguish the cases in `h : r = t`. Rewrite using `[if_pos h, if_pos h.symm, map_one]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero]`. Establish `e : ι ≃ (K' →ₐ[ℚ] ℂ)` using `Fintype.equivOfCardEq (by`. Rewrite using `[← Module.finrank_eq_card_basis b, AlgHom.card])`.

Establish `hBA : B * A = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 hAB`. Set `φ : K' →ₐ[ℚ] ℂ` to `IsAlgClosed.lift`. Set `ψ : K' →ₐ[ℚ] ℂ` to `φ.comp ((s : K' →+* K').toRatAlgHom)`. Establish `key : φ (∑ r, s (d r) * b r) = (1 : Matrix (K' →ₐ[ℚ] ℂ) (K' →ₐ[ℚ] ℂ) ℂ) φ ψ`. Rewrite using `[← hBA, Matrix.mul_apply, map_sum]`.

Conclude with `Finset.sum_congr rfl fun r _ => by rw [map_mul, mul_comm]; rfl`. Apply `φ.injective` to reduce the goal to its premises. Use `show φ _ = φ _`. Rewrite using `[key]`. Use `split_ifs with h`.

Establish `: φ = ψ` using `by subst h; ext x; rfl`. Rewrite using `[← this, Matrix.one_apply_eq, map_one]`. Rewrite using `[map_zero, Matrix.one_apply_ne]`. Introduce `h'`. Conclude with `h (AlgEquiv.ext fun x => (φ.injective (AlgHom.congr_fun h' x)).symm)`.
-/
theorem sum_dual_mul {K K' ι : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [Fintype ι] [DecidableEq ι] [DecidableEq (K' ≃ₐ[K] K')] (b : Basis ι ℚ K') (s : K' ≃ₐ[K] K') :
    ∑ r, s ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r) * b r =
      if s = 1 then 1 else 0 := by
  classical
  set d := (Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b with hd
  let A : Matrix ι (K' →ₐ[ℚ] ℂ) ℂ := fun r ρ => ρ (d r)
  let B : Matrix (K' →ₐ[ℚ] ℂ) ι ℂ := fun ρ r => ρ (b r)
  have hAB : A * B = 1 := by
    ext r t
    rw [Matrix.mul_apply]
    have e : ∑ ρ : K' →ₐ[ℚ] ℂ, A r ρ * B ρ t = algebraMap ℚ ℂ (Algebra.trace ℚ K' (d r * b t)) := by
      rw [trace_eq_sum_embeddings]
      exact Finset.sum_congr rfl fun ρ _ => (map_mul ρ _ _).symm
    rw [e, ← Algebra.traceForm_apply, hd, LinearMap.BilinForm.apply_dualBasis_left, Matrix.one_apply]
    by_cases h : r = t
    · rw [if_pos h, if_pos h.symm, map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have e : ι ≃ (K' →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq (by
    rw [← Module.finrank_eq_card_basis b, AlgHom.card])
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 hAB
  let φ : K' →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ψ : K' →ₐ[ℚ] ℂ := φ.comp ((s : K' →+* K').toRatAlgHom)
  have key : φ (∑ r, s (d r) * b r) = (1 : Matrix (K' →ₐ[ℚ] ℂ) (K' →ₐ[ℚ] ℂ) ℂ) φ ψ := by
    rw [← hBA, Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, mul_comm]; rfl
  apply φ.injective
  show φ _ = φ _
  rw [key]
  split_ifs with h
  · have : φ = ψ := by subst h; ext x; rfl
    rw [← this, Matrix.one_apply_eq, map_one]
  · rw [map_zero, Matrix.one_apply_ne]
    intro h'
    exact h (AlgEquiv.ext fun x => (φ.injective (AlgHom.congr_fun h' x)).symm)

/- English proof (translation)
Use `haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'`. Simplify using `only [trace_eq_sum_automorphisms, Finset.sum_mul, map_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `: ∀ s : K' ≃ₐ[K] K', ∑ r, s ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r) * s y * b r = if s = 1 then y else 0` using `fun s => by`. Establish `h` using `sum_dual_mul b s`.

Simplify using `only [mul_right_comm _ (s y), ← Finset.sum_mul, h]`. Use `split_ifs with h1`. Simplify using `[h1]`. Simplify using the standard rewrite rules. Simplify using `[this]`.
-/
theorem eq_sum_trace {K K' ι : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    [IsGalois K K'] [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ K') (y : K') :
    ∑ r, algebraMap K K' (Algebra.trace K K'
      ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r * y)) * b r = y := by
  classical
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  simp only [trace_eq_sum_automorphisms, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  have : ∀ s : K' ≃ₐ[K] K', ∑ r, s ((Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') b r) * s y * b r
      = if s = 1 then y else 0 := fun s => by
    have h := sum_dual_mul b s
    simp only [mul_right_comm _ (s y), ← Finset.sum_mul, h]
    split_ifs with h1
    · simp [h1]
    · simp
  simp [this]

/- English proof (translation)
Establish `hdual : (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K) r ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)`. Rewrite using `[FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]`. Introduce `a ha`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff _).mp ha`. Rewrite using `[← (RingOfIntegers.basis K).sum_repr c, map_sum, map_sum]`.

Use `Subring.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, ← integralBasis_apply, LinearMap.BilinForm.apply_dualBasis_left]`. Use `zsmul_mem ?_ _` and prove the remaining obligations. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`. Establish `hprod` using `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hδ) hdual`. Rewrite `hprod` using `[coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))]`. Conclude with `(FractionalIdeal.mem_one_iff _).mp hprod`.
-/
theorem different_mul_dual {K : Type} [Field K] [NumberField K] [DecidableEq (Free.ChooseBasisIndex ℤ (𝓞 K))]
    {δ : 𝓞 K} (hδ : δ ∈ differentIdeal ℤ (𝓞 K)) (r : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    ∃ α : 𝓞 K, (α : K) =
      δ * (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K) r := by
  have hdual : (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K) r ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K))]
    intro a ha
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    rw [← (RingOfIntegers.basis K).sum_repr c, map_sum, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_zsmul, map_zsmul, ← integralBasis_apply, LinearMap.BilinForm.apply_dualBasis_left]
    refine zsmul_mem ?_ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hprod := FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hδ) hdual
  rw [coeIdeal_differentIdeal ℤ ℚ,
    inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 K)⁰ K)))] at hprod
  exact (FractionalIdeal.mem_one_iff _).mp hprod

/- English proof (translation)
Use `set σ := w.embedding.comp (algebraMap K K') with hσ`. Establish `hv : w.comap (algebraMap K K') = InfinitePlace.mk σ`. Rewrite using `[← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]`. Establish `hd : DenseRange σ` using `denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)`. Establish `h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) = 1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k))` using `fun x => by`.

Establish `h` using `ht w.embedding (∑ k, x k • e k)`. Rewrite `h` using `[← (hG' w).2, map_sum]`. Simplify using `only [map_smulₛₗ] at h`. Rewrite `h` using `[normAt_sum]`. Rewrite using `[one_mul]`.

Conclude with `h.symm`. Rewrite using `[hv, gramPl_eq, gramPl_eq]`. Use `le_of_le_of_eq ?_ (by rw [one_pow, one_mul] : (1 : ℝ) ^ (2 * j) * _ = _)` and prove the remaining obligations. Break down `InfinitePlace.embedding_mk_eq σ with h | h` into its components or cases. Use `det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le` and prove the remaining obligations.

Use `normAt_sum b X (InfinitePlace.mk σ) e x` as an intermediate fact. Rewrite `this` using `[(hG _).2, h]`. Rewrite using `[this]`. Use `set B := cols b X (InfinitePlace.mk σ) e with hB`. Establish `h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re`.

Establish `: (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B)`. Use extensionality with `a c`. Simplify using `[Matrix.mul_apply]`. Rewrite using `[this, ← RingHom.map_det, Complex.conj_re]`. Rewrite using `[← h2]`.

Use `det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le` and prove the remaining obligations. Use `normAt_sum b X (InfinitePlace.mk σ) e x` as an intermediate fact. Rewrite `this` using `[(hG _).2, h]`. Rewrite using `[← hc]`. Use `(this.trans ?_).symm` and prove the remaining obligations.

Unfold `Formalism.HermitianLatticesTheory.cnorm`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.norm_conj]`. Simplify using `[Matrix.mulVec, dotProduct, hB]`.
-/
theorem gram_ge {K K' V V' ι κ : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [Field K']
    [NumberField K'] [StarRing K'] [Algebra K K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {b : Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {b' : Basis κ K' V'} {X' : InfinitePlace K' → Matrix κ κ ℂ} {N : (K →+* ℂ) → V → ℝ} {N' : (K' →+* ℂ) → V' → ℝ}
    (hG : IsGram b X N) (hG' : IsGram b' X' N') (hc : ∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x)
    (φ : V →ₛₗ[algebraMap K K'] V') (ht : ∀ σ' x, N' σ' (φ x) = N (σ'.comp (algebraMap K K')) x)
    {j : ℕ} (e : Fin j → V) (w : InfinitePlace K') :
    (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      (Formalism.HN.gramPl b' X' w fun k => φ (e k)).det.re := by
  set σ := w.embedding.comp (algebraMap K K') with hσ
  have hv : w.comap (algebraMap K K') = InfinitePlace.mk σ := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  have hd : DenseRange σ := denseRange_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)
  have h1 : ∀ x : Fin j → K, N σ (∑ k, x k • e k) =
      1 * Formalism.HermitianLatticesTheory.cnorm (cols b' X' w (fun k => φ (e k)) *ᵥ fun k => σ (x k)) := fun x => by
    have h := ht w.embedding (∑ k, x k • e k)
    rw [← (hG' w).2, map_sum] at h
    simp only [map_smulₛₗ] at h
    rw [normAt_sum] at h
    rw [one_mul]
    exact h.symm
  rw [hv, gramPl_eq, gramPl_eq]
  refine le_of_le_of_eq ?_ (by rw [one_pow, one_mul] : (1 : ℝ) ^ (2 * j) * _ = _)
  rcases InfinitePlace.embedding_mk_eq σ with h | h
  · refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [this]
  · set B := cols b X (InfinitePlace.mk σ) e with hB
    have h2 : ((B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ)).det.re = (Bᴴ * B).det.re := by
      have : (B.map (starRingEnd ℂ))ᴴ * B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (Bᴴ * B) := by
        ext a c
        simp [Matrix.mul_apply]
      rw [this, ← RingHom.map_det, Complex.conj_re]
    rw [← h2]
    refine det_le_of_dense σ hd _ _ 1 fun x => (le_of_eq ?_).trans (h1 x).le
    have := normAt_sum b X (InfinitePlace.mk σ) e x
    rw [(hG _).2, h] at this
    rw [← hc]
    refine (this.trans ?_).symm
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.norm_conj]
    simp [Matrix.mulVec, dotProduct, hB]

/- English proof (translation)
Introduce `K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L M ⟨⟨n, ⟨b, X⟩, hG⟩⟩ ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ hc hli hM h0 hN hsM hLM hst`. Use `letI : StarRing K := starRingOfComm`. Use `letI : StarRing K' := starRingOfComm`. Use `haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'`. Use `haveI : Module.Finite K V := Module.Finite.of_basis b`.

Use `haveI : Module.Finite K' V' := Module.Finite.of_basis b'`. Use `haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'`. Use `letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))`. Use `haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩`. Set `l : L →ₗ[𝓞 K] V'` to `{ toFun := fun x => ι x map_add' := fun x y => by simp map_smul' := fun a x => by show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x`.

Rewrite using `[← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]`. Use `rfl }`. Establish `hr : Set.range l = ι '' (L : Set V)`. Use extensionality with `y`. Simplify using `[l]`.

Establish `hιM : ∀ x ∈ L, ι x ∈ M` using `fun x hx => (hLM x (Submodule.subset_span hx)).1 hx`. Establish `hL : L.FG` using `by haveI : Module.Finite (𝓞 K') M := Module.Finite.iff_fg.2 hM haveI : Module.Finite (𝓞 K) M := Module.Finite.trans (𝓞 K') M`. Set `l' : L →ₗ[𝓞 K] M` to `{ toFun := fun x => ⟨l x, hιM x x.2⟩ map_add' := fun x y => Subtype.ext (l.map_add x y) map_smul' := fun a x => Subtype.ext (l.map_smul a x) }`. Use `Module.Finite.iff_fg.1 (Module.Finite.of_injective l' ((injective_iff_map_eq_zero _).2 fun x hx => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Establish `h1 : LinearIndependent K (fun _ : Fin 1 => (x : V))` using `linearIndependent_unique_iff.2 fun h => hne (Subtype.ext h)`. Conclude with `(hli 1 _ h1).ne_zero 0 (congrArg Subtype.val hx)`. Use `set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'`. Establish `hL'M : L' ≤ M` using `Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hιM x hx)`. Take `⟨e, heL, hsp, he⟩` from `Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)`.

Establish `hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V))` using `rfl`. Generalize the expression as in `finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj`. Establish `he'` using `hli j e he`. Establish `hspM : Submodule.span K' (M : Set V') = Submodule.span K' (Set.range fun k => ι (e k))`. Use `le_antisymm (Submodule.span_le.2 (hsM.trans (Submodule.span_le.2 ?_))) (Submodule.span_mono ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ hx)`. Rewrite using `[map_sum]`. Conclude with `Submodule.sum_mem _ fun k _ => by`. Rewrite using `[map_smulₛₗ]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `hιM _ (heL k)`. Establish `hj' : Formalism.HN.rkK M = j`. Rewrite using `[Formalism.HN.rkK, hspM, finrank_span_eq_card he', Fintype.card_fin]`.

Establish `hj0` using `Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b' M h0`. Rewrite `hj0` using `[hj']`. Establish `hD : differentIdeal ℤ (𝓞 K') • M ≤ L'`. Use `Submodule.smul_le.2 fun δ hδ x hx => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K').1 (hspM ▸ Submodule.subset_span hx)`.

Use `set d := (Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') (integralBasis K') with hd`. Set `y : Free.ChooseBasisIndex ℤ (𝓞 K') → V` to `fun r => ∑ k, Algebra.trace K K' (d r * (δ * a k)) • e k`. Establish `hy : ∀ r, y r ∈ L` using `fun r => by`. Use `(hLM _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (heL k)))).2 ?_` and prove the remaining obligations. Take `⟨α, hα⟩` from `different_mul_dual hδ r`.

Establish `h1 : ∑ k, (d r * (δ * a k)) • ι (e k) ∈ M`. Establish `h2` using `M.smul_mem α hx`. Rewrite `h2` using `[← algebraMap_smul K' α, Finset.smul_sum]`. Use `h2 using 2 with k` and compare the differences between its conclusion and the goal. Rewrite using `[smul_smul]`.

Use `congr 1`. Use `show _ = (α : K') * _`. Rewrite using `[hα, ← hd]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [map_sum, map_smulₛₗ, trace_eq_sum_automorphisms, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Submodule.sum_mem _ fun s _ => hst s j _ e h1`. Establish `h3 : δ • ∑ k, a k • ι (e k) = ∑ r, RingOfIntegers.basis K' r • ι (y r)`. Simplify using `only [y, map_sum, map_smulₛₗ, ← algebraMap_smul K' (RingOfIntegers.basis K' _), ← algebraMap_smul K' δ, Finset.smul_sum, smul_smul, ← integralBasis_apply]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`. Use `(eq_sum_trace (K := K) (integralBasis K') _).symm.trans ?_` and prove the remaining obligations. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`.

Rewrite using `[h3]`. Conclude with `Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy r, rfl⟩)`. Establish `hdisc : (discr K').natAbs ≠ 0` using `Int.natAbs_ne_zero.2 (discr_ne_zero K')`. Establish `hDi` using `Formalism.HN.DualPolygon.twist_index M hM (differentIdeal ℤ (𝓞 K')) fun h => hdisc (by`. Rewrite using `[← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])`.

Rewrite `hDi` using `[absNorm_differentIdeal K' (𝓞 K'), show finrank K' (Submodule.span K' (M : Set V')) = j from hj']`. Establish `hMi : L'.toAddSubgroup.relIndex M.toAddSubgroup ≤ (discr K').natAbs ^ j`. Rewrite using `[← hDi]`. Conclude with `AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).2 hD) (by rw [hDi]; exact pow_ne_zero _ hdisc)`. Take `⟨i1, g1, m1⟩` from `rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj`.

Establish `hFL' : Submodule.span (𝓞 K') (Set.range fun k => ι (e k)) ≤ L'` using `Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)`. Take `⟨i2, g2, m2⟩` from `rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' M hM (hFL'.trans hL'M) hj'`. Set `eL : Fin j → L` to `fun k => ⟨e k, heL k⟩`. Establish `hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup = (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup`. Establish `: Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype`.

Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Both sides reduce to the same expression. Use extensionality with `x`. Rewrite using `[this]`. Conclude with `⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩`.

Establish `hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup = Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))`. Rewrite using `[AddSubgroup.relIndex, hsub]`. Both sides reduce to the same expression. Rewrite `i1`, `m1` using `[hidx]`. Use `haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1`.

Establish `hidx'` using `relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K')) (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K) (fun x hx => by`. Establish `h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0`. Use `congrArg Subtype.val hx` as an intermediate fact. Rewrite `this`, the goal using `[Nat.cast_smul_eq_nsmul]`. Conclude with `this`.

Conclude with `Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))`. Use the proof step `(fun x => by`. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `(Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)`. Rewrite `hidx'` using `[card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr]`.

Establish `hmul` using `AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hFL') ((Submodule.toAddSubgroup_le _ _).2 hL'M)`. Rewrite `hmul` using `[show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _ from hidx']`. Establish `hlog : Real.log ((Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≤ finrank K K' * Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))) + j * Real.log |(discr K' : ℝ)|`. Rewrite using `[← Real.log_pow, ← Real.log_pow, ← Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 i1)) (pow_ne_zero _ (abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero K')))), ← Int.cast_abs, ← Nat.cast_natAbs]`. Use `Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero i2) ?_` and prove the remaining obligations.

Rewrite using `[← hmul]`. Conclude with `Nat.mul_le_mul_left _ hMi` after adjusting the coercions. Establish `hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤ ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re` using `Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)`. Rewrite `hs` using `[sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re]`. Establish `hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K`.

Simplify `sum_comap K K' fun _ => 1` using `[Formalism.HN.nPl]`. Establish `hf' : (0 : ℝ) < Formalism.HN.nPl K'` using `lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm`. Establish `hn : (finrank ℚ K' : ℝ) = 2 * Formalism.HN.nPl K'`. Simplify `sum_mk K' fun _ => 1` using `[Formalism.HN.nPl, Embeddings.card]`. Establish `hjp : (0 : ℝ) < j` using `by exact_mod_cast Nat.pos_of_ne_zero hj0`.

Rewrite using `[slope_sq_eq hG hL, slope_sq_eq hG' hM]`. Use `le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp` and prove the remaining obligations. Establish `m4` using `congrArg ((finrank K K' : ℝ) * ·) m1`. Establish `h5 : (Formalism.HN.nPl K' : ℝ) * (j * (2 * (Real.log |(discr K' : ℝ)| / finrank ℚ K'))) = j * Real.log |(discr K' : ℝ)|`. Rewrite using `[hn]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_sub, mul_sub, h5, m2, hf]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slope_sq_sub_le_of_galois_stable : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [IsGalois K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (M : Submodule (𝓞 K') V'), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → M.FG → M ≠ ⊥ → (∀ σ' x, N' σ' (ι x) = N (σ'.comp (algebraMap K K')) x) → (M : Set V') ⊆ Submodule.span K' (ι '' (Submodule.span K (L : Set V) : Set V)) → (∀ x ∈ Submodule.span K (L : Set V), x ∈ L ↔ ι x ∈ M) → (∀ (s : K' ≃ₐ[K] K') (n : ℕ) (a : Fin n → K') (x : Fin n → V), ∑ k, a k • ι (x k) ∈ M → ∑ k, s (a k) • ι (x k) ∈ M) → slope_sq N' M - 2 * (Real.log |(discr K' : ℝ)| / Module.finrank ℚ K') ≤ slope_sq N L := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L M ⟨⟨n, ⟨b, X⟩, hG⟩⟩ ⟨⟨n', ⟨b', X'⟩, hG'⟩⟩ hc hli hM h0 hN
    hsM hLM hst
  classical
  letI : StarRing K := starRingOfComm
  letI : StarRing K' := starRingOfComm
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K V := Module.Finite.of_basis b
  haveI : Module.Finite K' V' := Module.Finite.of_basis b'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  letI : Module (𝓞 K) V' := Module.compHom V' (algebraMap (𝓞 K) (𝓞 K'))
  haveI : IsScalarTower (𝓞 K) (𝓞 K') V' := ⟨fun a s x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  let l : L →ₗ[𝓞 K] V' :=
    { toFun := fun x => ι x
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        show ι (a • (x : V)) = algebraMap (𝓞 K) (𝓞 K') a • ι x
        rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
        rfl }
  have hr : Set.range l = ι '' (L : Set V) := by
    ext y; simp [l]
  have hιM : ∀ x ∈ L, ι x ∈ M := fun x hx => (hLM x (Submodule.subset_span hx)).1 hx
  have hL : L.FG := by
    haveI : Module.Finite (𝓞 K') M := Module.Finite.iff_fg.2 hM
    haveI : Module.Finite (𝓞 K) M := Module.Finite.trans (𝓞 K') M
    let l' : L →ₗ[𝓞 K] M :=
      { toFun := fun x => ⟨l x, hιM x x.2⟩
        map_add' := fun x y => Subtype.ext (l.map_add x y)
        map_smul' := fun a x => Subtype.ext (l.map_smul a x) }
    refine Module.Finite.iff_fg.1 (Module.Finite.of_injective l' ((injective_iff_map_eq_zero _).2 fun x hx => ?_))
    by_contra hne
    have h1 : LinearIndependent K (fun _ : Fin 1 => (x : V)) :=
      linearIndependent_unique_iff.2 fun h => hne (Subtype.ext h)
    exact (hli 1 _ h1).ne_zero 0 (congrArg Subtype.val hx)
  set L' := Submodule.span (𝓞 K') (ι '' (L : Set V)) with hL'
  have hL'M : L' ≤ M := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hιM x hx)
  obtain ⟨e, heL, hsp, he⟩ := Submodule.exists_fun_fin_finrank_span_eq K (L : Set V)
  have hj : Formalism.HN.rkK L = finrank K (Submodule.span K (L : Set V)) := rfl
  generalize finrank K (Submodule.span K (L : Set V)) = j at e heL hsp he hj
  have he' := hli j e he
  have hspM : Submodule.span K' (M : Set V') = Submodule.span K' (Set.range fun k => ι (e k)) := by
    refine le_antisymm (Submodule.span_le.2 (hsM.trans (Submodule.span_le.2 ?_))) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsp ▸ hx)
      rw [map_sum]
      exact Submodule.sum_mem _ fun k _ => by
        rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rintro _ ⟨k, rfl⟩; exact hιM _ (heL k)
  have hj' : Formalism.HN.rkK M = j := by
    rw [Formalism.HN.rkK, hspM, finrank_span_eq_card he', Fintype.card_fin]
  have hj0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b' M h0
  rw [hj'] at hj0

  have hD : differentIdeal ℤ (𝓞 K') • M ≤ L' := by
    refine Submodule.smul_le.2 fun δ hδ x hx => ?_
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K').1 (hspM ▸ Submodule.subset_span hx)
    set d := (Algebra.traceForm ℚ K').dualBasis (traceForm_nondegenerate ℚ K') (integralBasis K') with hd
    let y : Free.ChooseBasisIndex ℤ (𝓞 K') → V := fun r => ∑ k, Algebra.trace K K' (d r * (δ * a k)) • e k
    have hy : ∀ r, y r ∈ L := fun r => by
      refine (hLM _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (heL k)))).2 ?_
      obtain ⟨α, hα⟩ := different_mul_dual hδ r
      have h1 : ∑ k, (d r * (δ * a k)) • ι (e k) ∈ M := by
        have h2 := M.smul_mem α hx
        rw [← algebraMap_smul K' α, Finset.smul_sum] at h2
        convert h2 using 2 with k
        rw [smul_smul]
        congr 1
        show _ = (α : K') * _
        rw [hα, ← hd]; ring
      simp only [map_sum, map_smulₛₗ, trace_eq_sum_automorphisms, Finset.sum_smul]
      rw [Finset.sum_comm]
      exact Submodule.sum_mem _ fun s _ => hst s j _ e h1
    have h3 : δ • ∑ k, a k • ι (e k) = ∑ r, RingOfIntegers.basis K' r • ι (y r) := by
      simp only [y, map_sum, map_smulₛₗ, ← algebraMap_smul K' (RingOfIntegers.basis K' _), ← algebraMap_smul K' δ,
        Finset.smul_sum, smul_smul, ← integralBasis_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      refine (eq_sum_trace (K := K) (integralBasis K') _).symm.trans ?_
      exact Finset.sum_congr rfl fun r _ => mul_comm _ _
    rw [h3]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy r, rfl⟩)
  have hdisc : (discr K').natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero K')
  have hDi := Formalism.HN.DualPolygon.twist_index M hM (differentIdeal ℤ (𝓞 K')) fun h => hdisc (by
    rw [← absNorm_differentIdeal K' (𝓞 K'), h, Ideal.absNorm_bot])
  rw [absNorm_differentIdeal K' (𝓞 K'), show finrank K' (Submodule.span K' (M : Set V')) = j from hj'] at hDi
  have hMi : L'.toAddSubgroup.relIndex M.toAddSubgroup ≤ (discr K').natAbs ^ j := by
    rw [← hDi]
    exact AddSubgroup.relIndex_le_of_le_left ((Submodule.toAddSubgroup_le _ _).2 hD)
      (by rw [hDi]; exact pow_ne_zero _ hdisc)
  obtain ⟨i1, g1, m1⟩ := rk_mul_mu_eq b X (fun v => (hG v).1) e he L hL
    (Submodule.span_le.2 (Set.range_subset_iff.2 heL)) hj
  have hFL' : Submodule.span (𝓞 K') (Set.range fun k => ι (e k)) ≤ L' :=
    Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨e k, heL k, rfl⟩)
  obtain ⟨i2, g2, m2⟩ := rk_mul_mu_eq b' X' (fun v => (hG' v).1) _ he' M hM (hFL'.trans hL'M) hj'
  let eL : Fin j → L := fun k => ⟨e k, heL k⟩
  have hsub : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.addSubgroupOf L.toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup := by
    have : Submodule.span (𝓞 K) (Set.range e) = (Submodule.span (𝓞 K) (Set.range eL)).map L.subtype := by
      rw [Submodule.map_span, ← Set.range_comp]; rfl
    ext x
    rw [this]
    exact ⟨fun ⟨y, hy, h⟩ => (Subtype.ext h : y = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have hidx : (Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup =
      Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := by
    rw [AddSubgroup.relIndex, hsub]; rfl
  rw [hidx] at i1 m1
  haveI : Finite (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) := Nat.finite_of_card_ne_zero i1
  have hidx' := relIndex_span (S := 𝓞 K') l eL (he'.restrict_scalars' (𝓞 K'))
    (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : 𝓞 K)
    (fun x hx => by
      have h1 : ((Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL)) : ℕ) : K) • (x : V) = 0 := by
        have := congrArg Subtype.val hx
        rw [Nat.cast_smul_eq_nsmul] at this ⊢
        exact this
      exact Subtype.ext ((smul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 i1)))
    (fun x => by
      rw [Nat.cast_smul_eq_nsmul]
      exact (Submodule.span (𝓞 K) (Set.range eL)).toAddSubgroup.nsmul_index_mem x)
  rw [card_tensor K K' (isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩), hr] at hidx'
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 hFL')
    ((Submodule.toAddSubgroup_le _ _).2 hL'M)
  rw [show (Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex L'.toAddSubgroup = _
    from hidx'] at hmul
  have hlog : Real.log ((Submodule.span (𝓞 K') (Set.range fun k => ι (e k))).toAddSubgroup.relIndex
      M.toAddSubgroup : ℝ) ≤ finrank K K' * Real.log (Nat.card (L ⧸ Submodule.span (𝓞 K) (Set.range eL))) +
        j * Real.log |(discr K' : ℝ)| := by
    rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 i1))
      (pow_ne_zero _ (abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero K')))), ← Int.cast_abs, ← Nat.cast_natAbs]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero i2) ?_
    rw [← hmul]
    exact_mod_cast Nat.mul_le_mul_left _ hMi
  have hs : ∑ w : InfinitePlace K', Real.log (Formalism.HN.gramPl b X (w.comap (algebraMap K K')) e).det.re ≤
      ∑ w, Real.log (Formalism.HN.gramPl b' X' w fun k => ι (e k)).det.re :=
    Finset.sum_le_sum fun w _ => Real.log_le_log (g1 _) (gram_ge hG hG' hc ι hN e w)
  rw [sum_comap K K' fun v => Real.log (Formalism.HN.gramPl b X v e).det.re] at hs
  have hf : (Formalism.HN.nPl K' : ℝ) = finrank K K' * Formalism.HN.nPl K := by
    simpa [Formalism.HN.nPl] using sum_comap K K' fun _ => 1
  have hf' : (0 : ℝ) < Formalism.HN.nPl K' := lt_of_le_of_ne (Nat.cast_nonneg _) Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.nPl_ne_zero.symm
  have hn : (finrank ℚ K' : ℝ) = 2 * Formalism.HN.nPl K' := by
    simpa [Formalism.HN.nPl, Embeddings.card] using sum_mk K' fun _ => 1
  have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
  rw [slope_sq_eq hG hL, slope_sq_eq hG' hM]
  refine le_of_mul_le_mul_left (le_of_mul_le_mul_left ?_ hf') hjp
  have m4 := congrArg ((finrank K K' : ℝ) * ·) m1
  have h5 : (Formalism.HN.nPl K' : ℝ) * (j * (2 * (Real.log |(discr K' : ℝ)| / finrank ℚ K'))) =
      j * Real.log |(discr K' : ℝ)| := by
    rw [hn]; field_simp
  rw [mul_sub, mul_sub, h5, m2, hf]
  linarith

end GlobalTheory.SlopeGalois
