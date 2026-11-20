import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

variable {n : ℕ}

/- English proof (translation)
Set `L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ` to `(LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)`. Establish `hL : Continuous L` using `L.continuous_of_finiteDimensional`. Conclude with `hL.comp (E.cont.mul continuous_const)`.
-/
private theorem cont_tr (E : PositivityTheory.RgBcC.KMod n) (T : E.V →L[ℂ] E.V) :
    Continuous fun κ : Un n =>
      LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  let L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (E.cont.mul continuous_const)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
The claim follows from `(hf.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
private theorem integrable_coef [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v w : V) :
    Integrable (fun κ => f κ * ⟪w, σ κ v⟫_ℂ) ν :=
  (hf.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Take `⟨S, hfd, hv, hS⟩` from `hσ.fin v`. Establish `hmem : ∀ κ, σ κ v ∈ S` using `fun κ => hS κ v hv`. Set `b` to `stdOrthonormalBasis ℂ S`. Establish `hexp : ∀ κ, σ κ v = ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • ((b i : S) : V)`. Introduce `κ`.

Establish `h` using `b.sum_repr' (⟨σ κ v, hmem κ⟩ : S)`. Establish `h'` using `congrArg (Subtype.val) h`. Simplify `h'.symm` using `[Submodule.coe_sum, Submodule.coe_inner]`. Use `⟨∑ i, (∫ κ, f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ ∂ν) • ((b i : S) : V), fun w => ?_⟩` and prove the remaining obligations. Establish `hint : ∀ κ, f κ * ⟪w, σ κ v⟫_ℂ = ∑ i, (f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ) * ⟪w, ((b i : S) : V)⟫_ℂ`.

Introduce `κ`. Use `conv_lhs => rw [hexp κ]`. Rewrite using `[inner_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right]`.

Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hint]`. Rewrite using `[integral_finset_sum _ fun i _ => (integrable_coef ν σ hσ hf v _).mul_const _, inner_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_right, integral_mul_const]`.
-/
private theorem exists_avg [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v : V) :
    ∃ p : V, ∀ w : V, ⟪w, p⟫_ℂ = ∫ κ, f κ * ⟪w, σ κ v⟫_ℂ ∂ν := by
  obtain ⟨S, hfd, hv, hS⟩ := hσ.fin v
  have hmem : ∀ κ, σ κ v ∈ S := fun κ => hS κ v hv
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ κ, σ κ v = ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • ((b i : S) : V) := by
    intro κ
    have h := b.sum_repr' (⟨σ κ v, hmem κ⟩ : S)
    have h' := congrArg (Subtype.val) h
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h'.symm
  refine ⟨∑ i, (∫ κ, f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ ∂ν) • ((b i : S) : V), fun w => ?_⟩
  have hint : ∀ κ, f κ * ⟪w, σ κ v⟫_ℂ =
      ∑ i, (f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ) * ⟪w, ((b i : S) : V)⟫_ℂ := by
    intro κ
    conv_lhs => rw [hexp κ]
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  simp_rw [hint]
  rw [integral_finset_sum _ fun i _ => (integrable_coef ν σ hσ hf v _).mul_const _, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, integral_mul_const]

/- English proof (translation)
Introduce `n _ _ ν _ V _ _ σ hσ E T`. Use `haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ`. Establish `hf` using `cont_tr E T`. Use `choose p hp using fun v : V => exists_avg ν σ hσ hf v`. Establish `hI` using `fun v w : V => integrable_coef ν σ hσ hf v w`.

Use `⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, fun v w => hp v w⟩` and prove the remaining obligations. Introduce `x y`. Use `ext_inner_left ℂ fun w => ?_` and prove the remaining obligations. Rewrite using `[inner_add_right, hp, hp, hp, ← integral_add (hI x w) (hI y w)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)` and prove the remaining obligations.

Simplify using `only [map_add, inner_add_right, mul_add]`. Introduce `c x`. Use `ext_inner_left ℂ fun w => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)` and prove the remaining obligations.

Simplify using `only [map_smul, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem avgEx : AvgEx := by
  intro n _ _ ν _ V _ _ σ hσ E T
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  have hf := cont_tr E T
  choose p hp using fun v : V => exists_avg ν σ hσ hf v
  have hI := fun v w : V => integrable_coef ν σ hσ hf v w
  refine ⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, fun v w => hp v w⟩
  · intro x y
    refine ext_inner_left ℂ fun w => ?_
    rw [inner_add_right, hp, hp, hp, ← integral_add (hI x w) (hI y w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_add, inner_add_right, mul_add]
  · intro c x
    refine ext_inner_left ℂ fun w => ?_
    rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_smul, inner_smul_right]
    ring

end UpperTheory.V.Z.GSp4Splitting
