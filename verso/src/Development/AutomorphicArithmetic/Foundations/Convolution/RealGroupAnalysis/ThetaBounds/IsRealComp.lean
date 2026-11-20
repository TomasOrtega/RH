import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

open UpperTheory.ConvolutionTheory.R2.Fo (pl cw)

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsTotallyReal F] [IsTotallyComplex E]

private def Dm (s : ℂ) (d : Fin 4 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![d 1, (2 : ℂ)⁻¹ * (d 2 + s⁻¹ * d 3); (2 : ℂ)⁻¹ * (d 2 - s⁻¹ * d 3), d 0]

/- English proof (translation)
Simplify using `only [Fin.sum_univ_two, Fin.sum_univ_four]`. Simplify using `[Hm, Dm]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pair (s : ℂ) (hs : s ≠ 0) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) (d : Fin 4 → ℂ) :
    ∑ a, ∑ b, Hm s w x a b * Dm s d a b = ∑ i, ((x i w : ℝ) : ℂ) * d i := by
  simp only [Fin.sum_univ_two, Fin.sum_univ_four]
  simp [Hm, Dm]
  field_simp
  ring

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Hm] <;> ring`.
-/
private theorem Hm_neg (s : ℂ) (w : InfinitePlace F) (x : Fin 4 → TR.Rinf F) :
    Hm (-s) w x = (Hm s w x)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Hm] <;> ring

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Dm] <;> ring`.
-/
private theorem Dm_neg (s : ℂ) (d : Fin 4 → ℂ) : Dm (-s) d = (Dm s d)ᵀ := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Dm] <;> ring

/- English proof (translation)
Simplify using `[Fin.sum_univ_two, Matrix.mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem swap (Y H D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (Y.map (starRingEnd ℂ) * Hᵀ) a b * Dᵀ a b = ∑ a, ∑ b, (H * Yᴴ) a b * D a b := by
  simp [Fin.sum_univ_two, Matrix.mul_apply]
  ring

/- English proof (translation)
Simplify using `[Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem pair_neg (A B D : Matrix (Fin 2) (Fin 2) ℂ) :
    ∑ a, ∑ b, (-(A + B)) a b * D a b = -(∑ a, ∑ b, A a b * D a b) - ∑ a, ∑ b, B a b * D a b := by
  simp [Fin.sum_univ_two]
  ring

/- English proof (translation)
Establish `hre : s.re * s.re - s.im * s.im = r`. Use `congrArg Complex.re h` as an intermediate fact. Simplify `this` using `[pow_two, Complex.mul_re]`. Establish `him : s.re * s.im + s.im * s.re = 0`. Use `congrArg Complex.im h` as an intermediate fact.

Simplify `this` using `[pow_two, Complex.mul_im]`. Establish `h0 : s.re = 0`. Establish `: s.re * s.im = 0` using `by linarith`. Break down `mul_eq_zero.1 this with h1 | h1` into its components or cases. Conclude with `h1`.

Rewrite `hre` using `[h1]`. Use polynomial arithmetic with `[mul_self_nonneg s.re]`. Use `⟨Complex.ext (by simp [h0]) (by simp), fun hs => ?_⟩` and prove the remaining obligations. Rewrite `hre` using `[hs]`. Simplify using `at hre`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem im_of_sq {s : ℂ} {r : ℝ} (h : s ^ 2 = (r : ℂ)) (hr : r < 0) :
    starRingEnd ℂ s = -s ∧ s ≠ 0 := by
  have hre : s.re * s.re - s.im * s.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two, Complex.mul_re] using this
  have him : s.re * s.im + s.im * s.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two, Complex.mul_im] using this
  have h0 : s.re = 0 := by
    have : s.re * s.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg s.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun hs => ?_⟩
  rw [hs] at hre
  simp at hre
  linarith

/- English proof (translation)
The claim follows from `InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)`.
-/
private theorem isReal_comp (τ : E →+* ℂ) : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
  InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)

/- English proof (translation)
Rewrite using `[← map_pow, D.sq]`. Both sides reduce to the same expression.
-/
private theorem θ_sq (D : Dat F E) (τ : E →+* ℂ) : (τ D.θ) ^ 2 = (τ.comp (algebraMap F E)) D.δ := by
  rw [← map_pow, D.sq]
  rfl

/- English proof (translation)
Establish `hr` using `isReal_comp (F := F) τ`. Use `im_of_sq (r := hr.embedding D.δ) ?_ (D.neg hr.embedding)` and prove the remaining obligations. Rewrite using `[θ_sq, hr.coe_embedding_apply]`.
-/
private theorem θ_im (D : Dat F E) (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0 := by
  have hr := isReal_comp (F := F) τ
  refine im_of_sq (r := hr.embedding D.δ) ?_ (D.neg hr.embedding)
  rw [θ_sq, hr.coe_embedding_apply]

/- English proof (translation)
Establish `hc : ∀ c : F, τ (algebraMap F E c) = τ' (algebraMap F E c)` using `fun c => RingHom.congr_fun h c`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[← D.b.sum_repr x, Fin.sum_univ_two, D.b0, D.b1]`. Simplify using `only [Algebra.smul_def, map_add, map_mul, map_one, hc, hθ]`.
-/
private theorem emb_ext (D : Dat F E) {τ τ' : E →+* ℂ} (h : τ.comp (algebraMap F E) = τ'.comp (algebraMap F E))
    (hθ : τ D.θ = τ' D.θ) : τ = τ' := by
  have hc : ∀ c : F, τ (algebraMap F E c) = τ' (algebraMap F E c) := fun c => RingHom.congr_fun h c
  refine RingHom.ext fun x => ?_
  rw [← D.b.sum_repr x, Fin.sum_univ_two, D.b0, D.b1]
  simp only [Algebra.smul_def, map_add, map_mul, map_one, hc, hθ]

/- English proof (translation)
Establish `hr` using `ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ)`. Use extensionality with `x`. Use `RingHom.congr_fun hr x` as an intermediate fact. Simplify `congrArg id this` using `[ComplexEmbedding.conjugate_coe_eq]`.
-/
private theorem conj_comp (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap F E) = τ.comp (algebraMap F E) := by
  have hr := ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ)
  ext x
  have := RingHom.congr_fun hr x
  simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg id this

/- English proof (translation)
Unfold `pl`. Rewrite using `[conj_comp]`.
-/
private theorem pl_conj (τ : E →+* ℂ) : pl F (ComplexEmbedding.conjugate τ) = pl F τ := by
  unfold pl
  rw [conj_comp]

/- English proof (translation)
Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Conclude with `(θ_im D τ).1`.
-/
private theorem conj_θ (D : Dat F E) (τ : E →+* ℂ) : (ComplexEmbedding.conjugate τ) D.θ = -τ D.θ := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact (θ_im D τ).1

/- English proof (translation)
Introduce `h` and use `by have h1 := conj_θ D τ rw [← h] at h1 have h2 := (θ_im D τ).2 exact h2 (self_eq_neg.1 h1)`.
-/
private theorem conj_ne (D : Dat F E) (τ : E →+* ℂ) : τ ≠ ComplexEmbedding.conjugate τ := fun h => by
  have h1 := conj_θ D τ
  rw [← h] at h1
  have h2 := (θ_im D τ).2
  exact h2 (self_eq_neg.1 h1)

/- English proof (translation)
Establish `h1 : τ'.comp (algebraMap F E) = τ.comp (algebraMap F E)`. Break down `InfinitePlace.mk_eq_iff.1 h with h | h` into its components or cases. Conclude with `h`. Rewrite using `[← h]`. Conclude with `(ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ')).symm`.

Establish `h2 : (τ' D.θ) ^ 2 = (τ D.θ) ^ 2` using `by rw [θ_sq, θ_sq, h1]`. Break down `eq_or_eq_neg_of_sq_eq_sq _ _ h2 with h3 | h3` into its components or cases. Conclude with `Or.inl (emb_ext D h1 h3)`. Conclude with `Or.inr (emb_ext D (h1.trans (conj_comp τ).symm) (h3.trans (conj_θ D τ).symm))`.
-/
private theorem pl_fiber (D : Dat F E) {τ τ' : E →+* ℂ} (h : pl F τ' = pl F τ) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by
  have h1 : τ'.comp (algebraMap F E) = τ.comp (algebraMap F E) := by
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact h
    · rw [← h]
      exact (ComplexEmbedding.isReal_iff.1 (isReal_comp (F := F) τ')).symm
  have h2 : (τ' D.θ) ^ 2 = (τ D.θ) ^ 2 := by rw [θ_sq, θ_sq, h1]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ h2 with h3 | h3
  · exact Or.inl (emb_ext D h1 h3)
  · exact Or.inr (emb_ext D (h1.trans (conj_comp τ).symm) (h3.trans (conj_θ D τ).symm))

/- English proof (translation)
Use `haveI : Module.Finite F E := Module.Finite.of_basis D.b`. Take `⟨w', hw'⟩` from `InfinitePlace.comap_surjective (k := F) (K := E) w`. Use `⟨w'.embedding, ?_⟩` and prove the remaining obligations. Unfold `pl`. Rewrite using `[← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]`.

Conclude with `hw'`.
-/
private theorem pl_surj (D : Dat F E) (w : InfinitePlace F) : ∃ τ : E →+* ℂ, pl F τ = w := by
  haveI : Module.Finite F E := Module.Finite.of_basis D.b
  obtain ⟨w', hw'⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
  refine ⟨w'.embedding, ?_⟩
  unfold pl
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw'

/- English proof (translation)
Rewrite using `[← Finset.sum_fiberwise Finset.univ (pl F) f]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Take `⟨τ, rfl⟩` from `pl_surj D w`. Establish `hf : (Finset.univ.filter fun τ' : E →+* ℂ => pl F τ' = pl F τ) = {τ, ComplexEmbedding.conjugate τ}`. Use extensionality with `τ'`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`. Use `⟨pl_fiber D, ?_⟩` and prove the remaining obligations. Introduce and unpack `(rfl | rfl)`. Both sides reduce to the same expression. Conclude with `pl_conj τ`.

Rewrite using `[← h τ, ← Finset.sum_pair (conj_ne D τ), ← hf]`.
-/
private theorem sum_pl (D : Dat F E) (f : (E →+* ℂ) → ℂ) (g : InfinitePlace F → ℂ)
    (h : ∀ τ, f τ + f (ComplexEmbedding.conjugate τ) = g (pl F τ)) : ∑ τ, f τ = ∑ w, g w := by
  rw [← Finset.sum_fiberwise Finset.univ (pl F) f]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨τ, rfl⟩ := pl_surj D w
  have hf : (Finset.univ.filter fun τ' : E →+* ℂ => pl F τ' = pl F τ) = {τ, ComplexEmbedding.conjugate τ} := by
    ext τ'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨pl_fiber D, ?_⟩
    rintro (rfl | rfl)
    · rfl
    · exact pl_conj τ
  rw [← h τ, ← Finset.sum_pair (conj_ne D τ), ← hf]

variable (D : Dat F E) (O : Fo.Ops F) (v : V4 F)

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Fo.Ops.X, Hm, O.x_apply, Fo.cw] <;> ring`.
-/
private theorem X_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.X D τ a b ψ').1 v = Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) a b * ψ'.1 v := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.X, Hm, O.x_apply, Fo.cw] <;> ring

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Fo.Ops.DX, Dm] <;> ring`.
-/
private theorem DX_apply (τ : E →+* ℂ) (a b : Fin 2) (ψ' : S4 F) :
    (O.DX D τ a b ψ').1 v = Dm (τ D.θ) (fun i => (O.d (pl F τ) i ψ').1 v) a b := by
  fin_cases a <;> fin_cases b <;> simp [Fo.Ops.DX, Dm] <;> ring

/- English proof (translation)
Unfold `Fo.Ops.dE`. Rewrite using `[Fin.sum_univ_two, Fin.sum_univ_two]`. Distinguish the cases in `h : i = j`. Simplify using `[h, Module.End.mul_apply, X_apply, DX_apply]`. Simplify using `[h, Module.End.mul_apply, X_apply, DX_apply]`.
-/
private theorem dE_apply (τ : E →+* ℂ) (i j : Fin 2) (ψ' : S4 F) :
    (O.dE D τ i j ψ').1 v = -(if i = j then ψ'.1 v else 0) -
      ∑ b, Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) j b *
        Dm (τ D.θ) (fun i => (O.d (pl F τ) i ψ').1 v) i b := by
  unfold Fo.Ops.dE
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  by_cases h : i = j
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]
  · simp [h, Module.End.mul_apply, X_apply, DX_apply]

/- English proof (translation)
Simplify using `[Fo.Ops.dL, LinearMap.sum_apply, Finset.sum_apply]`.
-/
private theorem dL_apply (Y : Lie E 2) (ψ' : S4 F) :
    (O.dL D Y ψ').1 v = ∑ τ : E →+* ℂ, ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v := by
  simp [Fo.Ops.dL, LinearMap.sum_apply, Finset.sum_apply]

private def T (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) : ℂ :=
  ∑ a, ∑ b, ((Matrix.of Y).map (coord τ) * Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i))) a b *
    Dm (τ D.θ) (fun i => (O.d (pl F τ) i ψ').1 v) a b

/- English proof (translation)
Establish `hy : (Matrix.of Y).map (coord (ComplexEmbedding.conjugate τ)) = ((Matrix.of Y).map (coord τ)).map (starRingEnd ℂ)`. Use extensionality with `a b`. Simplify using `[GlobalTheory.IsoPull.coord_conj]`. Unfold `T`. Rewrite using `[pl_conj, conj_θ, Hm_neg, Dm_neg, hy]`.

Conclude with `swap _ _ _`.
-/
private theorem T_conj (Y : Lie E 2) (ψ' : S4 F) (τ : E →+* ℂ) :
    T D O v Y ψ' (ComplexEmbedding.conjugate τ) =
      ∑ a, ∑ b, (Hm (τ D.θ) (pl F τ) (fun i => TR.pInf F (v i)) * ((Matrix.of Y).map (coord τ))ᴴ) a b *
        Dm (τ D.θ) (fun i => (O.d (pl F τ) i ψ').1 v) a b := by
  have hy : (Matrix.of Y).map (coord (ComplexEmbedding.conjugate τ)) =
      ((Matrix.of Y).map (coord τ)).map (starRingEnd ℂ) := by
    ext a b
    simp [GlobalTheory.IsoPull.coord_conj]
  unfold T
  rw [pl_conj, conj_θ, Hm_neg, Dm_neg, hy]
  exact swap _ _ _

/- English proof (translation)
Establish `tr : coord τ (Y 0 0) + coord τ (Y 1 1) = 0`. Rewrite `hY` using `[Matrix.trace_fin_two]`. Rewrite using `[← map_add]`. Establish `: Y 0 0 + Y 1 1 = 0` using `hY`. Rewrite using `[this, map_zero]`.

Simplify using `only [dE_apply, T, Fin.sum_univ_two, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]`. Simplify using `only [Fin.isValue, zero_ne_one, one_ne_zero, if_true, if_false]`. Take the linear combination `(-(ψ'.1 v)) * tr`.
-/
private theorem term (Y : Lie E 2) (hY : (Matrix.of Y).trace = 0) (ψ' : S4 F) (τ : E →+* ℂ) :
    ∑ i, ∑ j, coord τ (Y i j) * (O.dE D τ i j ψ').1 v = -T D O v Y ψ' τ := by
  have tr : coord τ (Y 0 0) + coord τ (Y 1 1) = 0 := by
    rw [Matrix.trace_fin_two] at hY
    rw [← map_add]
    have : Y 0 0 + Y 1 1 = 0 := hY
    rw [this, map_zero]
  simp only [dE_apply, T, Fin.sum_univ_two, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_true, if_false]
  linear_combination (-(ψ'.1 v)) * tr

end UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators

end

open UpperTheory.ConvolutionTheory.R2.Ff.VectorFieldOperators in
/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D O Y hY v x' hx φ`. Rewrite using `[Finset.sum_comm, dL_apply]`. Repeatedly rewrite using `[term D O v Y hY φ]`. Use `symm`. Use `sum_pl D (fun τ => -T D O v Y φ τ) _ fun τ => ?_` and prove the remaining obligations.

Establish `h1` using `pair (τ D.θ) (θ_im D τ).2 (pl F τ) x' (fun i => (O.d (pl F τ) i φ).1 v)`. Rewrite `h1` using `[hx τ, pair_neg]`. Rewrite using `[← h1, T_conj]`. Unfold `T`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.vfOps :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), VfOps D O := by
  intro F E _ _ _ _ _ _ _ D O Y hY v x' hx φ
  rw [Finset.sum_comm, dL_apply]
  simp_rw [term D O v Y hY φ]
  symm
  refine sum_pl D (fun τ => -T D O v Y φ τ) _ fun τ => ?_
  have h1 := pair (τ D.θ) (θ_im D τ).2 (pl F τ) x' (fun i => (O.d (pl F τ) i φ).1 v)
  rw [hx τ, pair_neg] at h1
  rw [← h1, T_conj]
  unfold T
  ring
