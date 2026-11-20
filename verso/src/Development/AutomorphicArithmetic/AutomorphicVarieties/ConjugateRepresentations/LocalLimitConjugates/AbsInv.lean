import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Establish `hre : (inner ℂ x v).im = 0`. Establish `e` using `congrArg Complex.im h`. Rewrite `e` using `[← inner_conj_symm v x, Complex.conj_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : ‖x + (Complex.I * s) • v‖ ^ 2 = ‖x‖ ^ 2 + (|s| * ‖v‖) ^ 2`.

Rewrite using `[@norm_add_sq ℂ, inner_smul_right, norm_smul]`. Establish `hn : ‖Complex.I * (s : ℂ)‖ = |s|`. Rewrite using `[norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[hn]`. Simplify using `[Complex.mul_re, hre]`.

Establish `h0 : 0 ≤ |s| * ‖v‖` using `mul_nonneg (abs_nonneg s) (norm_nonneg v)`. Use polynomial arithmetic with `[norm_nonneg (x + (Complex.I * s) • v), sq_nonneg ‖x‖]`.
-/
private theorem UpperTheory.V.Cj.H.absInv_low {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x v : H) (s : ℝ)
    (h : inner ℂ x v = inner ℂ v x) : |s| * ‖v‖ ≤ ‖x + (Complex.I * s) • v‖ := by
  have hre : (inner ℂ x v).im = 0 := by
    have e := congrArg Complex.im h
    rw [← inner_conj_symm v x, Complex.conj_im] at e
    linarith
  have hsq : ‖x + (Complex.I * s) • v‖ ^ 2 = ‖x‖ ^ 2 + (|s| * ‖v‖) ^ 2 := by
    rw [@norm_add_sq ℂ, inner_smul_right, norm_smul]
    have hn : ‖Complex.I * (s : ℂ)‖ = |s| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn]
    simp [Complex.mul_re, hre]
  have h0 : 0 ≤ |s| * ‖v‖ := mul_nonneg (abs_nonneg s) (norm_nonneg v)
  nlinarith [norm_nonneg (x + (Complex.I * s) • v), sq_nonneg ‖x‖]

/- English proof (translation)
Introduce `H _ _ _ D A hA s hs hd`. Set `L : D →ₗ[ℂ] H` to `D.subtype.comp A + (Complex.I * s) • D.subtype`. Establish `hL : ∀ v, L v = ↑(A v) + (Complex.I * s) • (v : H)` using `fun v => rfl`. Establish `hs' : 0 < |s|` using `abs_pos.mpr hs`. Establish `hlow : ∀ v : D, |s| * ‖(v : H)‖ ≤ ‖L v‖`.

Introduce `v`. Rewrite using `[hL]`. Conclude with `UpperTheory.V.Cj.H.absInv_low _ _ s (hA v v)`. Establish `hinj : Function.Injective L`. Introduce `a b hab`.

Establish `h1` using `hlow (a - b)`. Rewrite `h1` using `[map_sub, hab, sub_self, norm_zero]`. Establish `h2 : ‖((a - b : D) : H)‖ = 0` using `le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hs') (norm_nonneg _)`. Rewrite `h2` using `[norm_eq_zero, Submodule.coe_sub, sub_eq_zero]`. Conclude with `Subtype.ext h2`.

Set `R` to `LinearMap.range L`. Set `e` to `LinearEquiv.ofInjective L hinj`. Establish `he : ∀ x : D, ((e x : R) : H) = L x` using `fun x => LinearEquiv.ofInjective_apply L (h := hinj) x`. Set `g : R →ₗ[ℂ] H` to `D.subtype.comp e.symm.toLinearMap`. Establish `hg : ∀ y : R, |s| * ‖g y‖ ≤ ‖(y : H)‖`.

Introduce `y`. Establish `h1 : L (e.symm y) = y`. Establish `h2` using `he (e.symm y)`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply]`. Conclude with `h2.symm`.

Establish `h3` using `hlow (e.symm y)`. Rewrite `h3` using `[h1]`. Conclude with `h3`. Set `gc : R →L[ℂ] H` to `g.mkContinuous (|s|⁻¹) (fun y => by`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ hs']`.

Use `hg y` as an intermediate fact. Express the relevant statement in the definitionally equal form `‖g y‖ * |s| ≤ ‖(y : H)‖`. Use the proof step `linarith)`. Establish `hdense : Dense (R : Set H)`. Rewrite using `[Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure]`.

Establish `hb : Rᗮ = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `w hw`. Apply `hd w` to reduce the goal to its premises. Introduce `v`.

Conclude with `(Submodule.mem_orthogonal' R w).1 hw _ (LinearMap.mem_range_self L v)`. Rewrite using `[hb, Submodule.bot_orthogonal_eq_top]`. Establish `hdr : DenseRange (R.subtypeL : R → H)` using `hdense.denseRange_val`. Establish `hui : IsUniformInducing (R.subtypeL : R → H)` using `isUniformEmbedding_subtype_val.isUniformInducing`. Use `⟨gc.extend R.subtypeL, ?_, ?_⟩` and prove the remaining obligations.

Introduce `v`. Establish `h1` using `ContinuousLinearMap.extend_eq gc hdr hui ⟨L v, LinearMap.mem_range_self L v⟩`. Establish `h2 : e.symm ⟨L v, LinearMap.mem_range_self L v⟩ = v`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `Subtype.ext (he v).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Introduce `w`. Use `hdense.induction (P := fun w => |s| * ‖gc.extend R.subtypeL w‖ ≤ ‖w‖) ?_ ?_ w` and prove the remaining obligations. Introduce `y hy`.

Establish `h1 : gc.extend R.subtypeL y = gc ⟨y, hy⟩` using `ContinuousLinearMap.extend_eq gc hdr hui ⟨y, hy⟩`. Use `show |s| * ‖gc.extend R.subtypeL y‖ ≤ ‖y‖`. Rewrite using `[h1]`. Conclude with `hg ⟨y, hy⟩`. Conclude with `isClosed_le (continuous_const.mul (continuous_norm.comp (gc.extend R.subtypeL).continuous)) continuous_norm`.
-/
theorem UpperTheory.V.Cj.H.absInv :
    UpperTheory.V.Cj.H.AbsInv := by
  intro H _ _ _ D A hA s hs hd
  let L : D →ₗ[ℂ] H := D.subtype.comp A + (Complex.I * s) • D.subtype
  have hL : ∀ v, L v = ↑(A v) + (Complex.I * s) • (v : H) := fun v => rfl
  have hs' : 0 < |s| := abs_pos.mpr hs
  have hlow : ∀ v : D, |s| * ‖(v : H)‖ ≤ ‖L v‖ := by
    intro v
    rw [hL]
    exact UpperTheory.V.Cj.H.absInv_low _ _ s (hA v v)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖((a - b : D) : H)‖ = 0 :=
      le_antisymm (le_of_mul_le_mul_left (by simpa using h1) hs') (norm_nonneg _)
    rw [norm_eq_zero, Submodule.coe_sub, sub_eq_zero] at h2
    exact Subtype.ext h2
  let R := LinearMap.range L
  let e := LinearEquiv.ofInjective L hinj
  have he : ∀ x : D, ((e x : R) : H) = L x := fun x => LinearEquiv.ofInjective_apply L (h := hinj) x
  let g : R →ₗ[ℂ] H := D.subtype.comp e.symm.toLinearMap
  have hg : ∀ y : R, |s| * ‖g y‖ ≤ ‖(y : H)‖ := by
    intro y
    have h1 : L (e.symm y) = y := by
      have h2 := he (e.symm y)
      rw [LinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    have h3 := hlow (e.symm y)
    rw [h1] at h3
    exact h3
  let gc : R →L[ℂ] H := g.mkContinuous (|s|⁻¹) (fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ hs']
    have := hg y
    change ‖g y‖ * |s| ≤ ‖(y : H)‖
    linarith)
  have hdense : Dense (R : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, ← Submodule.orthogonal_orthogonal_eq_closure]
    have hb : Rᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      apply hd w
      intro v
      exact (Submodule.mem_orthogonal' R w).1 hw _ (LinearMap.mem_range_self L v)
    rw [hb, Submodule.bot_orthogonal_eq_top]
  have hdr : DenseRange (R.subtypeL : R → H) := hdense.denseRange_val
  have hui : IsUniformInducing (R.subtypeL : R → H) := isUniformEmbedding_subtype_val.isUniformInducing
  refine ⟨gc.extend R.subtypeL, ?_, ?_⟩
  · intro v
    have h1 := ContinuousLinearMap.extend_eq gc hdr hui ⟨L v, LinearMap.mem_range_self L v⟩
    have h2 : e.symm ⟨L v, LinearMap.mem_range_self L v⟩ = v := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (he v).symm
    calc gc.extend R.subtypeL (↑(A v) + (Complex.I * ↑s) • ↑v)
        = gc ⟨L v, LinearMap.mem_range_self L v⟩ := h1
      _ = ↑v := by
        show ((e.symm ⟨L v, LinearMap.mem_range_self L v⟩ : D) : H) = v
        rw [h2]
  · intro w
    refine hdense.induction (P := fun w => |s| * ‖gc.extend R.subtypeL w‖ ≤ ‖w‖) ?_ ?_ w
    · intro y hy
      have h1 : gc.extend R.subtypeL y = gc ⟨y, hy⟩ :=
        ContinuousLinearMap.extend_eq gc hdr hui ⟨y, hy⟩
      show |s| * ‖gc.extend R.subtypeL y‖ ≤ ‖y‖
      rw [h1]
      exact hg ⟨y, hy⟩
    · exact isClosed_le (continuous_const.mul (continuous_norm.comp (gc.extend R.subtypeL).continuous))
        continuous_norm
