import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfJ

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteZeroOrbits

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `: nmat X 0 = ExtFPf.oneF X`. Use function extensionality and compare the values at `τ a b`. Simplify using `only [nmat, ExtFPf.oneF, Matrix.one_apply]`. Use `split_ifs with h1 h2 h3`. Conclude with `absurd h2 (ne_of_gt h1)`.

Both sides reduce to the same expression. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[cpt, this, ExtFPf.rmul_oneF]`.
-/
theorem cpt_origin {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  have : nmat X 0 = ExtFPf.oneF X := by
    funext τ a b
    simp only [nmat, ExtFPf.oneF, Matrix.one_apply]
    split_ifs with h1 h2 h3
    · exact absurd h2 (ne_of_gt h1)
    · rfl
    · rfl
    · rfl
  rw [cpt, this, ExtFPf.rmul_oneF]

/- English proof (translation)
Establish `hu : ∀ τ, IsUnit (mat x τ).det` using `fun τ => isUnit_iff_ne_zero.mpr (hx τ).1`. Establish `hM : ∀ τ, LUPf.Mx X x x τ = 1` using `fun τ => Matrix.nonsing_inv_mul _ (hu τ)`. Establish `hΔ : LUPf.DeltaF X x x ≠ 0`. Establish `: LUPf.DeltaF X x x = 1`. Unfold `LUPf.DeltaF`.

Use `Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Conclude with `LUPf.lminor_one k`. Rewrite using `[this]`. Conclude with `one_ne_zero`.

Establish `hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1`. Use `(LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero) (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm` and prove the remaining obligations. Rewrite using `[Matrix.one_mul]`. Conclude with `Matrix.one_apply_ne (ne_of_gt h)`. Establish `hz0 : LUPf.zF X x x = 0`.

Use extensionality with `k`. Use `set p := (Fintype.equivFin (Ent X)).symm k with hp`. Use `show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0`. Rewrite using `[hM, hL, inv_one]`. Conclude with `Matrix.one_apply_ne (ne_of_gt p.2.2)`.

Establish `hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0}` using `(FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)`. Establish `hn` using `hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)`. Establish `hc : ContinuousAt (LUPf.zF X x) x` using `(LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn`. Establish `hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ` using `hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)`. Use `filter_upwards [hn, hb] with y hy hyb`.

Use `⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ`. Use `show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ * (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)`. Rewrite using `[LUPf.nmat_zF]`. Use `show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) : Matrix (Fin r) (Fin r) ℂ)`.

Establish `hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det` using `by rw [LUPf.Lm_det]; exact isUnit_one`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL', Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]`. Both sides reduce to the same expression.
-/
theorem eventually_split {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∃ z ∈ Metric.closedBall (0 : V (nd X)) δ, ∃ b ∈ Bor X.Ψ r,
      y = rmul (cpt X x z) b := by
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => isUnit_iff_ne_zero.mpr (hx τ).1
  have hM : ∀ τ, LUPf.Mx X x x τ = 1 := fun τ => Matrix.nonsing_inv_mul _ (hu τ)
  have hΔ : LUPf.DeltaF X x x ≠ 0 := by
    have : LUPf.DeltaF X x x = 1 := by
      unfold LUPf.DeltaF
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
      rw [hM]
      exact LUPf.lminor_one k
    rw [this]; exact one_ne_zero
  have hL : LUPf.Lm (1 : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    refine (LUPf.Lm_unique 1 1 (fun k => by rw [LUPf.lminor_one]; exact one_ne_zero)
      (fun i k h => Matrix.one_apply_ne (ne_of_lt h)) (fun i => Matrix.one_apply_eq i) fun i j h => ?_).symm
    rw [Matrix.one_mul]; exact Matrix.one_apply_ne (ne_of_gt h)
  have hz0 : LUPf.zF X x x = 0 := by
    ext k
    set p := (Fintype.equivFin (Ent X)).symm k with hp
    show ((LUPf.Lm (LUPf.Mx X x x p.1))⁻¹ : Matrix (Fin r) (Fin r) ℂ) p.2.1.1 p.2.1.2 = 0
    rw [hM, hL, inv_one]
    exact Matrix.one_apply_ne (ne_of_gt p.2.2)
  have hopen : IsOpen {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun (LUPf.Delta_diff (X := X) (x0 := x)).continuous continuous_const)
  have hn := hopen.mem_nhds (show x ∈ {y | y ∈ X.dom ∧ LUPf.DeltaF X x y ≠ 0} from ⟨hx, hΔ⟩)
  have hc : ContinuousAt (LUPf.zF X x) x :=
    (LUPf.zF_diffOn (X := X) (x0 := x)).continuousOn.continuousAt hn
  have hb : ∀ᶠ y in 𝓝 x, LUPf.zF X x y ∈ Metric.closedBall (0 : V (nd X)) δ :=
    hc.preimage_mem_nhds (by rw [hz0]; exact Metric.closedBall_mem_nhds _ hδ)
  filter_upwards [hn, hb] with y hy hyb
  refine ⟨hy.1, _, hyb, _, LUPf.bF_mem hy.1 hy.2, ?_⟩
  funext τ
  show y τ = (mat x τ * mat (nmat X (LUPf.zF X x y)) τ *
    (LUPf.Lm (LUPf.Mx X x y τ) * LUPf.Mx X x y τ) : Matrix (Fin r) (Fin r) ℂ)
  rw [LUPf.nmat_zF]
  show y τ = (mat x τ * (LUPf.Lm (LUPf.Mx X x y τ))⁻¹ * (LUPf.Lm (LUPf.Mx X x y τ) * ((mat x τ)⁻¹ * mat y τ)) :
    Matrix (Fin r) (Fin r) ℂ)
  have hL' : IsUnit (LUPf.Lm (LUPf.Mx X x y τ)).det := by rw [LUPf.Lm_det]; exact isUnit_one
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (LUPf.Lm (LUPf.Mx X x y τ))⁻¹, Matrix.nonsing_inv_mul _ hL',
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ), Matrix.one_mul]
  rfl

/- English proof (translation)
Distinguish the cases in `hd : DifferentiableAt ℂ f 0`. Conclude with `HE.iso_zero hd.hasFDerivAt hdet h0`. Use `⟨1, one_pos, fun y _ _ => ?_⟩` and prove the remaining obligations. Establish `hk` using `HE.ker_bot_of_det hdet`. Rewrite `hk` using `[fderiv_zero_of_not_differentiableAt hd]`.

Establish `: y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n)` using `by simp`. Rewrite `this` using `[hk]`. Conclude with `(Submodule.mem_bot ℂ).1 this`.
-/
theorem isolated_of_det {n : ℕ} {f : V n → V n} (hdet : (fderiv ℂ f 0).det ≠ 0) (h0 : f 0 = 0) :
    ∃ δ > 0, ∀ y ∈ Metric.closedBall (0 : V n) δ, f y = 0 → y = 0 := by
  by_cases hd : DifferentiableAt ℂ f 0
  · exact HE.iso_zero hd.hasFDerivAt hdet h0
  · refine ⟨1, one_pos, fun y _ _ => ?_⟩
    have hk := HE.ker_bot_of_det hdet
    rw [fderiv_zero_of_not_differentiableAt hd] at hk
    have : y ∈ LinearMap.ker ((0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) := by simp
    rw [hk] at this
    exact (Submodule.mem_bot ℂ).1 this

def orbitSetoid {r : ℕ} (X : Data E r) : Setoid (Frame X.Ψ r) where
  r x y := ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)
  iseqv := by
    refine ⟨fun x => ⟨1, X.Γ.one_mem, ExtFPf.oneF X, ExtFPf.oneF_mem X, ?_⟩, ?_, ?_⟩
    · rw [FundSetPf.lact_one, ExtFPf.rmul_oneF]
    · rintro x y ⟨γ, hγ, b, hb, rfl⟩
      refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ExtFPf.invF X b, ExtFPf.invF_mem X hb, ?_⟩
      rw [← FundSetPf.lact_rmul, FundSetPf.lact_inv, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
        ExtFPf.rmul_oneF]
    · rintro x y z ⟨γ, hγ, b, hb, rfl⟩ ⟨γ', hγ', b', hb', rfl⟩
      refine ⟨γ' * γ, X.Γ.mul_mem hγ' hγ, rmul b b', ExtFPf.mul_mem X hb hb', ?_⟩
      rw [FundSetPf.lact_mul, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc]

/- English proof (translation)
Introduce `r X L w0 s _ hs hsimp C hC hCd hmeet`. Use `set S := orbitSetoid X with hS`. Establish `hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0)`. Introduce and unpack `x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩`. Establish `hxb` using `OntoS.dom_rmul X hx hb`.

Use `⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]`. Establish `hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y`. Introduce `x hx h0`. Take `⟨δ, hδ, hiso⟩` from `isolated_of_det (hsimp x hx h0).2 (by`.

Use extensionality with `k`. Simplify using `[cpt_origin, h0 k])`. Use `filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0`. Establish `hR : S.r (cpt X x z) y` using `⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩`. Establish `h1` using `(hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2`.

Establish `hz0 : z = 0` using `hiso z hz (by`. Use extensionality with `k`. Simplify using `[h1 k])`. Rewrite `hR` using `[hz0, cpt_origin]`. Then use the resulting hypothesis. Establish `hK : IsCompact (C ∩ {x | ∀ k, s k x = 0})`.

Establish `hcont : ContinuousOn (fun x k => s k x) C` using `continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd`. Establish `hcl` using `hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))`. Establish `he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0}`. Use extensionality with `x`. Simplify using `[funext_iff]`.

Rewrite using `[he]`. Conclude with `hC.of_isClosed_subset hcl Set.inter_subset_left`. Take `⟨t, htK, hcov⟩` from `hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y}) (fun x hx => hloc x (hCd hx.1) hx.2)`. Use `set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT`. Establish `hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0`.

Introduce `q hq`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hq`. Conclude with `hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩`. Use `⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1, fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, b, hb, hc⟩` from `hmeet x hx h0`.

Establish `hR : S.r x (lact γ (rmul x b))` using `⟨γ, hγ, b, hb, rfl⟩`. Establish `h1` using `(hstab _ _ hR ⟨hx, h0⟩).2`. Take `⟨u, hu, hy⟩` from `Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)`. Use `⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`.

Conclude with `S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))`. Introduce and unpack `⟨j, hj⟩`. Conclude with `(hstab _ x hj (hout _ (T.equivFin.symm j).2)).2`. Introduce `j j' γ hγ b hb h`. Establish `hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out` using `⟨γ, hγ, b, hb, h⟩`.

Use `Quotient.sound (s := S) hR` as an intermediate fact. Rewrite `this` using `[Quotient.out_eq, Quotient.out_eq]`. Conclude with `T.equivFin.symm.injective (Subtype.ext this)`.
-/
theorem finite_orbits : ∀ (r : ℕ) (X : Data E r) (L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ),
    X.IsSec L w0 → (∀ k, X.IsSec L (s k)) →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → w0 x ≠ 0 ∧ (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x z) / w0 (cpt X x z) : V (nd X))) 0).det ≠ 0) →
    ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
    (∀ x ∈ X.dom, (∀ k, s k x = 0) → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) →
    ∃ (δ : ℕ) (xs : Fin δ → Frame X.Ψ r), (∀ j, xs j ∈ X.dom) ∧
      (∀ x ∈ X.dom, (∀ k, s k x = 0) ↔ ∃ j, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (xs j) b)) ∧
      ∀ j j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, xs j' = lact γ (rmul (xs j) b) → j = j' := by
  classical
  intro r X L w0 s _ hs hsimp C hC hCd hmeet
  set S := orbitSetoid X with hS

  have hstab : ∀ x y, S.r x y → (x ∈ X.dom ∧ ∀ k, s k x = 0) → (y ∈ X.dom ∧ ∀ k, s k y = 0) := by
    rintro x y ⟨γ, hγ, b, hb, rfl⟩ ⟨hx, h0⟩
    have hxb := OntoS.dom_rmul X hx hb
    refine ⟨OntoS.dom_lact X hγ hxb, fun k => ?_⟩
    rw [(hs k).2.2 γ hγ _ hxb, (hs k).2.1 x hx b hb, h0 k, mul_zero, mul_zero]

  have hloc : ∀ x ∈ X.dom, (∀ k, s k x = 0) → ∀ᶠ y in 𝓝 x, (∀ k, s k y = 0) → S.r x y := by
    intro x hx h0
    obtain ⟨δ, hδ, hiso⟩ := isolated_of_det (hsimp x hx h0).2 (by
      ext k
      simp [cpt_origin, h0 k])
    filter_upwards [eventually_split X hx hδ] with y ⟨hy, z, hz, b, hb, he⟩ hy0
    have hR : S.r (cpt X x z) y := ⟨1, X.Γ.one_mem, b, hb, by rw [FundSetPf.lact_one]; exact he⟩
    have h1 := (hstab _ _ (S.iseqv.symm hR) ⟨hy, hy0⟩).2
    have hz0 : z = 0 := hiso z hz (by
      ext k
      simp [h1 k])
    rwa [hz0, cpt_origin] at hR
  have hK : IsCompact (C ∩ {x | ∀ k, s k x = 0}) := by
    have hcont : ContinuousOn (fun x k => s k x) C :=
      continuousOn_pi.2 fun k => (hs k).1.continuousOn.mono hCd
    have hcl := hcont.preimage_isClosed_of_isClosed hC.isClosed (isClosed_singleton (x := 0))
    have he : C ∩ {x | ∀ k, s k x = 0} = C ∩ (fun x k => s k x) ⁻¹' {0} := by
      ext x; simp [funext_iff]
    rw [he]
    exact hC.of_isClosed_subset hcl Set.inter_subset_left
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => {y | (∀ k, s k y = 0) → S.r x y})
    (fun x hx => hloc x (hCd hx.1) hx.2)
  set T : Finset (Quotient S) := t.image (Quotient.mk S) with hT
  have hout : ∀ q ∈ T, q.out ∈ X.dom ∧ ∀ k, s k q.out = 0 := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hq
    exact hstab x _ (S.iseqv.symm (Quotient.mk_out x)) ⟨hCd (htK x hx).1, (htK x hx).2⟩
  refine ⟨T.card, fun j => (T.equivFin.symm j).1.out, fun j => (hout _ (T.equivFin.symm j).2).1,
    fun x hx => ⟨fun h0 => ?_, ?_⟩, ?_⟩
  · obtain ⟨γ, hγ, b, hb, hc⟩ := hmeet x hx h0
    have hR : S.r x (lact γ (rmul x b)) := ⟨γ, hγ, b, hb, rfl⟩
    have h1 := (hstab _ _ hR ⟨hx, h0⟩).2
    obtain ⟨u, hu, hy⟩ := Set.mem_iUnion₂.1 (hcov ⟨hc, h1⟩)
    refine ⟨T.equivFin ⟨Quotient.mk S u, Finset.mem_image_of_mem _ hu⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact S.iseqv.trans (Quotient.mk_out u) (S.iseqv.trans (hy h1) (S.iseqv.symm hR))
  · rintro ⟨j, hj⟩
    exact (hstab _ x hj (hout _ (T.equivFin.symm j).2)).2
  · intro j j' γ hγ b hb h
    have hR : S.r (T.equivFin.symm j).1.out (T.equivFin.symm j').1.out := ⟨γ, hγ, b, hb, h⟩
    have := Quotient.sound (s := S) hR
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact T.equivFin.symm.injective (Subtype.ext this)

end GlobalTheory.FiniteZeroOrbits
