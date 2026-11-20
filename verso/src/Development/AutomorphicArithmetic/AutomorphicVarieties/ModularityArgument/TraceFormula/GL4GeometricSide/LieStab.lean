import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SkewExp

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open Matrix

/- English proof (translation)
Establish `hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t`. Introduce `t`. Establish `he` using `(hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t`. Establish `h` using `he.clm_apply (hc t)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Simplify using `[ContinuousLinearMap.mul_apply]`. Establish `hconst` using `is_const_of_deriv_eq_zero (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0`. Simplify using `using hconst`.
-/
private theorem flow {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (c : ℝ → S) (hc : ∀ t, HasDerivAt c (D (c t)) t) :
    c 1 = NormedSpace.exp D (c 0) := by
  have hψ : ∀ t : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp ((1 - u) • D) (c u)) 0 t := by
    intro t
    have he := (hasDerivAt_exp_smul_const (𝕂 := ℝ) D (1 - t)).comp_const_sub 1 t
    have h := he.clm_apply (hc t)
    convert h using 1
    simp [ContinuousLinearMap.mul_apply]
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hψ u).differentiableAt) (fun u => (hψ u).deriv) 1 0
  simpa using hconst

/- English proof (translation)
Establish `hs` using `NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D`. Establish `hs2` using `(ContinuousLinearMap.apply ℝ S x).hasSum hs`. Establish `hpow : ∀ m : ℕ, (D ^ m) x ∈ M`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simpa using hx`. Consider the case `succ m ih`. Rewrite using `[pow_succ', ContinuousLinearMap.mul_apply]`. Conclude with `hD _ ih`. Use `hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations.

Use `M.sum_mem fun m _ => ?_` and prove the remaining obligations. Simplify using `using M.smul_mem _ (hpow m)`.
-/
private theorem exp_mem {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
    (D : S →L[ℝ] S) (M : Submodule ℝ S) (hM : IsClosed (M : Set S)) (hD : ∀ y ∈ M, D y ∈ M)
    {x : S} (hx : x ∈ M) : NormedSpace.exp D x ∈ M := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) D
  have hs2 := (ContinuousLinearMap.apply ℝ S x).hasSum hs
  have hpow : ∀ m : ℕ, (D ^ m) x ∈ M := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      exact hD _ ih
  refine hM.mem_of_tendsto hs2 (Filter.Eventually.of_forall fun s => ?_)
  refine M.sum_mem fun m _ => ?_
  simpa using M.smul_mem _ (hpow m)

/- English proof (translation)
Rewrite `h`, the goal using `[hasDerivAt_iff_isLittleO_nhds_zero]`. Conclude with `(Asymptotics.isLittleO_norm_left).1 h.norm_left`.
-/
private theorem lift {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {S : Submodule ℂ V}
    {c : ℝ → S} {d : S} {t : ℝ} (h : HasDerivAt (fun s => (c s : V)) (d : V) t) : HasDerivAt c d t := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  exact (Asymptotics.isLittleO_norm_left).1 h.norm_left

variable {n : ℕ}

private def curve (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (t : ℝ) : Un n :=
  ⟨NormedSpace.exp ((t : ℂ) • X), (UpperTheory.RealTr.skewExp n).1 _ (by
    rw [conjTranspose_smul, hX]; simp)⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)`. Establish `hc : Commute ((s : ℂ) • X) ((t : ℂ) • X)` using `((Commute.refl X).smul_left _).smul_right _`. Rewrite using `[← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]`.
-/
private theorem curve_add (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    curve X hX (s + t) = curve X hX s * curve X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1`. Simplify using the standard rewrite rules.
-/
private theorem curve_zero (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) : curve X hX 0 = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
  simp

end UpperTheory.V.Z.GSp4Splitting.LieStabilizer

open UpperTheory.V.Z.GSp4Splitting.LieStabilizer in
/- English proof (translation)
Introduce `n V _ _ σ Kf hder N hN k x hx`. Take `⟨X, hX, hXk⟩` from `(UpperTheory.RealTr.skewExp n).2 k`. Take `⟨S, hfd, hxS, hσS, hKS, hd⟩` from `hder.2 x`. Use `haveI : FiniteDimensional ℂ S := hfd`. Use `haveI : CompleteSpace S := FiniteDimensional.complete ℂ S`.

Set `L : Module.End ℂ V` to `∑ a, ∑ b, X a b • Kf a b`. Establish `hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w`. Introduce `w`. Simplify using `[L, LinearMap.sum_apply]`. Establish `hLS : ∀ w ∈ S, L w ∈ S`.

Introduce `w hw`. Rewrite using `[hLapp]`. Conclude with `S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)`. Establish `hLN : ∀ w ∈ N, L w ∈ N`. Introduce `w hw`.

Rewrite using `[hLapp]`. Conclude with `N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)`. Set `Dc : S →L[ℂ] S` to `LinearMap.toContinuousLinearMap (L.restrict hLS)`. Set `D : S →L[ℝ] S` to `Dc.restrictScalars ℝ`. Establish `hDapp : ∀ w : S, ((D w : S) : V) = L w` using `fun w => rfl`.

Set `γ` to `curve X hX`. Set `c : ℝ → S` to `fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩`. Establish `hc : ∀ t, HasDerivAt c (D (c t)) t`. Introduce `t`. Apply `lift` to reduce the goal to its premises.

Establish `h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t)`. Rewrite using `[sub_self, hLapp]`. Conclude with `hd X γ (fun _ => rfl) _ (c t).2`. Establish `h1` using `h0.comp_sub_const t t`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s`. Establish `: γ s = γ (s - t) * γ t`. Rewrite using `[← curve_add, sub_add_cancel]`. Use `show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)`. Rewrite using `[this, map_mul, Module.End.mul_apply]`.

Conclude with `hDapp _`. Establish `h1` using `flow D c hc`. Set `M : Submodule ℂ S` to `N.comap S.subtype`. Establish `hMc : IsClosed (M : Set S)` using `Submodule.closed_of_finiteDimensional M`. Establish `hc0 : c 0 ∈ M.restrictScalars ℝ` using `by show σ (γ 0) x ∈ N`.

Establish `: γ 0 = 1` using `curve_zero X hX`. Rewrite using `[this, map_one]`. Conclude with `hx`. Establish `h2` using `exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0`. Rewrite `h2` using `[← h1]`.

Establish `hk : γ 1 = k`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1`. Simplify using `using hXk`. Establish `h3 : σ (γ 1) x ∈ N` using `h2`.

Rewrite `h3` using `[hk]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Z.GSp4Splitting.lieStab :
    LieStab := by
  intro n V _ _ σ Kf hder N hN k x hx
  obtain ⟨X, hX, hXk⟩ := (UpperTheory.RealTr.skewExp n).2 k
  obtain ⟨S, hfd, hxS, hσS, hKS, hd⟩ := hder.2 x
  haveI : FiniteDimensional ℂ S := hfd
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : Module.End ℂ V := ∑ a, ∑ b, X a b • Kf a b
  have hLapp : ∀ w, L w = ∑ a, ∑ b, X a b • Kf a b w := by
    intro w
    simp [L, LinearMap.sum_apply]
  have hLS : ∀ w ∈ S, L w ∈ S := by
    intro w hw
    rw [hLapp]
    exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hKS a b w hw)
  have hLN : ∀ w ∈ N, L w ∈ N := by
    intro w hw
    rw [hLapp]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (hN a b w hw)
  let Dc : S →L[ℂ] S := LinearMap.toContinuousLinearMap (L.restrict hLS)
  let D : S →L[ℝ] S := Dc.restrictScalars ℝ
  have hDapp : ∀ w : S, ((D w : S) : V) = L w := fun w => rfl
  let γ := curve X hX
  let c : ℝ → S := fun t => ⟨σ (γ t) x, hσS _ _ hxS⟩
  have hc : ∀ t, HasDerivAt c (D (c t)) t := by
    intro t
    apply lift
    have h0 : HasDerivAt (fun s : ℝ => σ (γ s) (c t : V)) (L (c t : V)) (t - t) := by
      rw [sub_self, hLapp]
      exact hd X γ (fun _ => rfl) _ (c t).2
    have h1 := h0.comp_sub_const t t
    convert h1 using 1
    funext s
    have : γ s = γ (s - t) * γ t := by
      rw [← curve_add, sub_add_cancel]
    show σ (γ s) x = σ (γ (s - t)) (σ (γ t) x)
    rw [this, map_mul, Module.End.mul_apply]
    exact hDapp _
  have h1 := flow D c hc
  let M : Submodule ℂ S := N.comap S.subtype
  have hMc : IsClosed (M : Set S) := Submodule.closed_of_finiteDimensional M
  have hc0 : c 0 ∈ M.restrictScalars ℝ := by
    show σ (γ 0) x ∈ N
    have : γ 0 = 1 := curve_zero X hX
    rw [this, map_one]
    exact hx
  have h2 := exp_mem D (M.restrictScalars ℝ) hMc (fun y hy => hLN _ hy) hc0
  rw [← h1] at h2
  have hk : γ 1 = k := by
    apply Subtype.ext
    show NormedSpace.exp (((1 : ℝ) : ℂ) • X) = k.1
    simpa using hXk
  have h3 : σ (γ 1) x ∈ N := h2
  rwa [hk] at h3
