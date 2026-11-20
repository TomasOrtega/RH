import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLevelSetLocalInj
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

def polyDiff {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) : (J → ℂ) →L[ℂ] ℂ :=
  ∑ j, eval w₀ (pderiv j p) • ContinuousLinearMap.proj j

/- English proof (translation)
Simplify using `[polyDiff]`.
-/
theorem polyDiff_apply {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ v : J → ℂ) :
    polyDiff p w₀ v = ∑ j, eval w₀ (pderiv j p) * v j := by
  simp [polyDiff]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h0 : polyDiff (C a) w₀ = 0`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[polyDiff_apply]`.

Rewrite using `[h0]`. Simplify using `only [eval_C]`. Conclude with `hasStrictFDerivAt_const a w₀`. Consider the case `add p q hp hq`. Establish `h0 : polyDiff (p + q) w₀ = polyDiff p w₀ + polyDiff q w₀`.

Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Simplify using `[polyDiff_apply, add_mul, Finset.sum_add_distrib]`. Rewrite using `[h0]`. Simplify using `only [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p n hp`. Establish `hX : HasStrictFDerivAt (fun w : J → ℂ => w n) (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) w₀` using `hasStrictFDerivAt_apply n w₀`. Establish `h` using `hp.mul hX`. Establish `h0 : polyDiff (p * X n) w₀ = eval w₀ p • (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) + w₀ n • polyDiff p w₀`. Establish `key : ∀ j, eval w₀ (pderiv j (X n : MvPolynomial J ℂ)) = if j = n then 1 else 0`.

Introduce `j`. Distinguish the cases in `hj : j = n`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[pderiv_X_of_ne (Ne.symm hj), hj]`.

Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `s1 : ∑ j, eval w₀ p * (if j = n then (1 : ℂ) else 0) * v j = eval w₀ p * v n`. Simplify using the standard rewrite rules. Establish `s2 : ∑ j, eval w₀ (pderiv j p) * w₀ n * v j = w₀ n * ∑ j, eval w₀ (pderiv j p) * v j`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Simplify using `only [polyDiff_apply, pderiv_mul, map_add, map_mul, key, eval_X, add_mul, Finset.sum_add_distrib, s1, s2, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h0]`. Simplify using `only [map_mul, eval_X]`.

Conclude with `h`.
-/
theorem hasStrictFDerivAt_eval_poly {J : Type} [Fintype J] (p : MvPolynomial J ℂ) (w₀ : J → ℂ) :
    HasStrictFDerivAt (fun w => eval w p) (polyDiff p w₀) w₀ := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h0 : polyDiff (C a) w₀ = 0 := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply]
    rw [h0]
    simp only [eval_C]
    exact hasStrictFDerivAt_const a w₀
  | add p q hp hq =>
    have h0 : polyDiff (p + q) w₀ = polyDiff p w₀ + polyDiff q w₀ := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp [polyDiff_apply, add_mul, Finset.sum_add_distrib]
    rw [h0]
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasStrictFDerivAt (fun w : J → ℂ => w n)
        (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) w₀ :=
      hasStrictFDerivAt_apply n w₀
    have h := hp.mul hX
    have h0 : polyDiff (p * X n) w₀ =
        eval w₀ p • (ContinuousLinearMap.proj n : (J → ℂ) →L[ℂ] ℂ) + w₀ n • polyDiff p w₀ := by
      have key : ∀ j, eval w₀ (pderiv j (X n : MvPolynomial J ℂ)) = if j = n then 1 else 0 := by
        intro j
        by_cases hj : j = n
        · subst hj
          simp
        · simp [pderiv_X_of_ne (Ne.symm hj), hj]
      refine ContinuousLinearMap.ext fun v => ?_
      have s1 : ∑ j, eval w₀ p * (if j = n then (1 : ℂ) else 0) * v j = eval w₀ p * v n := by
        simp
      have s2 : ∑ j, eval w₀ (pderiv j p) * w₀ n * v j = w₀ n * ∑ j, eval w₀ (pderiv j p) * v j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      simp only [polyDiff_apply, pderiv_mul, map_add, map_mul, key, eval_X, add_mul,
        Finset.sum_add_distrib, s1, s2, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      ring
    rw [h0]
    simp only [map_mul, eval_X]
    exact h

/- English proof (translation)
Set `M : Matrix R J ℂ` to `Matrix.of fun i j => eval w₀ (pderiv j (f i))`. Establish `hrank : M.rank = Fintype.card R` using `LinearIndependent.rank_matrix (M := M) hli`. Establish `hLM : ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) : (J → ℂ) →ₗ[ℂ] (R → ℂ)) = M.mulVecLin`. Use `LinearMap.ext fun v => funext fun i => ?_` and prove the remaining obligations. Simplify using `[polyDiff_apply, M, Matrix.mulVec, dotProduct]`.

Rewrite using `[hLM]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[Module.finrank_fintype_fun_eq_card, ← hrank, Matrix.rank]`.
-/
theorem polyDiff_pi_range_eq_top {J R : Type} [Fintype J] [Fintype R] (f : R → MvPolynomial J ℂ)
    (w₀ : J → ℂ) (hli : LinearIndependent ℂ (fun i => fun j => eval w₀ (pderiv j (f i)))) :
    LinearMap.range ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = ⊤ := by
  classical
  let M : Matrix R J ℂ := Matrix.of fun i j => eval w₀ (pderiv j (f i))
  have hrank : M.rank = Fintype.card R := LinearIndependent.rank_matrix (M := M) hli
  have hLM : ((ContinuousLinearMap.pi fun i => polyDiff (f i) w₀ : (J → ℂ) →L[ℂ] (R → ℂ)) :
      (J → ℂ) →ₗ[ℂ] (R → ℂ)) = M.mulVecLin := by
    refine LinearMap.ext fun v => funext fun i => ?_
    simp [polyDiff_apply, M, Matrix.mulVec, dotProduct]
  rw [hLM]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← hrank, Matrix.rank]

/- English proof (translation)
Establish `hK : Module.finrank ℂ (LinearMap.ker L) = m`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker L`. Rewrite `h` using `[hL, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers. Take `⟨C, hC⟩` from `(LinearMap.ker L).exists_isCompl`.

Establish `hKm : Module.finrank ℂ (LinearMap.ker L) = Module.finrank ℂ (Fin m → ℂ)`. Rewrite using `[hK, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Set `e : LinearMap.ker L ≃ₗ[ℂ] (Fin m → ℂ)` to `LinearEquiv.ofFinrankEq _ _ hKm`. Set `π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ)` to `e.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto C hC`. Establish `hker : LinearMap.ker (L.prod π) = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`. Establish `h1 : L x = 0` using `congrArg Prod.fst hx`. Establish `h2 : π x = 0` using `congrArg Prod.snd hx`. Establish `hxK : x ∈ LinearMap.ker L` using `h1`.

Establish `h3 : (LinearMap.ker L).projectionOnto C hC x = ⟨x, hxK⟩` using `Submodule.projectionOnto_apply_of_mem_left hC hxK`. Establish `h4 : e ⟨x, hxK⟩ = 0`. Establish `: π x = e ((LinearMap.ker L).projectionOnto C hC x)` using `rfl`. Rewrite `h2` using `[this, h3]`. Conclude with `h2`.

Establish `h5 : (⟨x, hxK⟩ : LinearMap.ker L) = 0` using `(LinearEquiv.map_eq_zero_iff e).1 h4`. Conclude with `congrArg Subtype.val h5`. Use `⟨π, hker, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]`. Conclude with `LinearMap.ker_eq_bot.1 hker`.

Rewrite using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prod_bijective {J R : Type} [Fintype J] [Fintype R] (L : (J → ℂ) →ₗ[ℂ] (R → ℂ))
    (hL : LinearMap.range L = ⊤) (m : ℕ) (hm : m + Fintype.card R = Fintype.card J) :
    ∃ π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ),
      LinearMap.ker (L.prod π) = ⊥ ∧ LinearMap.range (L.prod π) = ⊤ := by
  have hK : Module.finrank ℂ (LinearMap.ker L) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hL, finrank_top, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card] at h
    omega
  obtain ⟨C, hC⟩ := (LinearMap.ker L).exists_isCompl
  have hKm : Module.finrank ℂ (LinearMap.ker L) = Module.finrank ℂ (Fin m → ℂ) := by
    rw [hK, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e : LinearMap.ker L ≃ₗ[ℂ] (Fin m → ℂ) := LinearEquiv.ofFinrankEq _ _ hKm
  let π : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ) := e.toLinearMap ∘ₗ (LinearMap.ker L).projectionOnto C hC
  have hker : LinearMap.ker (L.prod π) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : L x = 0 := congrArg Prod.fst hx
    have h2 : π x = 0 := congrArg Prod.snd hx
    have hxK : x ∈ LinearMap.ker L := h1
    have h3 : (LinearMap.ker L).projectionOnto C hC x = ⟨x, hxK⟩ :=
      Submodule.projectionOnto_apply_of_mem_left hC hxK
    have h4 : e ⟨x, hxK⟩ = 0 := by
      have : π x = e ((LinearMap.ker L).projectionOnto C hC x) := rfl
      rw [this, h3] at h2
      exact h2
    have h5 : (⟨x, hxK⟩ : LinearMap.ker L) = 0 := (LinearEquiv.map_eq_zero_iff e).1 h4
    exact congrArg Subtype.val h5
  refine ⟨π, hker, ?_⟩
  rw [LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  · exact LinearMap.ker_eq_bot.1 hker
  · rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega

/- English proof (translation)
Introduce `J _ R _ f w₀ hli m hm`. Set `F : (J → ℂ) → (R → ℂ)` to `fun w i => eval w (f i)`. Set `L : (J → ℂ) →L[ℂ] (R → ℂ)` to `ContinuousLinearMap.pi fun i => polyDiff (f i) w₀`. Establish `hF : HasStrictFDerivAt F L w₀` using `hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_eval_poly (f i) w₀`. Take `⟨πl, hker, hran⟩` from `exists_prod_bijective (L : (J → ℂ) →ₗ[ℂ] (R → ℂ)) (polyDiff_pi_range_eq_top f w₀ hli) m hm`.

Set `π : (J → ℂ) →L[ℂ] (Fin m → ℂ)` to `LinearMap.toContinuousLinearMap πl`. Set `Φ : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ)` to `L.prod π`. Set `E` to `ContinuousLinearEquiv.ofBijective Φ hker hran`. Set `G : (J → ℂ) → (R → ℂ) × (Fin m → ℂ)` to `fun w => (F w, π w)`. Establish `hG : HasStrictFDerivAt G (E : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ)) w₀` using `(hF.prodMk π.hasStrictFDerivAt).congr_fderiv (ContinuousLinearEquiv.coe_ofBijective Φ hker hran).symm`.

Use `⟨(hG.toOpenPartialHomeomorph G).source, (hG.toOpenPartialHomeomorph G).open_source, hG.mem_toOpenPartialHomeomorph_source, π, ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxU, hx⟩ y ⟨hyU, hy⟩ hxy`. Apply `(hG.toOpenPartialHomeomorph G).injOn hxU hyU` to reduce the goal to its premises. Rewrite using `[hG.toOpenPartialHomeomorph_coe]`. Conclude with `Prod.ext (funext fun i => (hx i).trans (hy i).symm) hxy`.
-/
theorem LevelSetLocalInj.proof : LevelSetLocalInj.Statement := by
  intro J _ R _ f w₀ hli m hm
  let F : (J → ℂ) → (R → ℂ) := fun w i => eval w (f i)
  let L : (J → ℂ) →L[ℂ] (R → ℂ) := ContinuousLinearMap.pi fun i => polyDiff (f i) w₀
  have hF : HasStrictFDerivAt F L w₀ :=
    hasStrictFDerivAt_pi.2 fun i => hasStrictFDerivAt_eval_poly (f i) w₀
  obtain ⟨πl, hker, hran⟩ :=
    exists_prod_bijective (L : (J → ℂ) →ₗ[ℂ] (R → ℂ)) (polyDiff_pi_range_eq_top f w₀ hli) m hm
  let π : (J → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap πl
  let Φ : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ) := L.prod π
  let E := ContinuousLinearEquiv.ofBijective Φ hker hran
  let G : (J → ℂ) → (R → ℂ) × (Fin m → ℂ) := fun w => (F w, π w)
  have hG : HasStrictFDerivAt G (E : (J → ℂ) →L[ℂ] (R → ℂ) × (Fin m → ℂ)) w₀ :=
    (hF.prodMk π.hasStrictFDerivAt).congr_fderiv (ContinuousLinearEquiv.coe_ofBijective Φ hker hran).symm
  refine ⟨(hG.toOpenPartialHomeomorph G).source, (hG.toOpenPartialHomeomorph G).open_source,
    hG.mem_toOpenPartialHomeomorph_source, π, ?_⟩
  rintro x ⟨hxU, hx⟩ y ⟨hyU, hy⟩ hxy
  apply (hG.toOpenPartialHomeomorph G).injOn hxU hyU
  rw [hG.toOpenPartialHomeomorph_coe]
  exact Prod.ext (funext fun i => (hx i).trans (hy i).symm) hxy

end GroundTheory.Heights₂.Heights.LowerBoundFree
