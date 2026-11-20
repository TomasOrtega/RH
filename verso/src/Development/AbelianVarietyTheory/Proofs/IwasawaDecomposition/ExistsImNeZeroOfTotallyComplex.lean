import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeOfImNeZero
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push Not at h`. Use `IsTotallyComplex.complexEmbedding_not_isReal σ ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`. Use extensionality with `a`.

Conclude with `Complex.conj_eq_iff_im.2 (h a)`.
-/
theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

/- English proof (translation)
Rewrite using `[lin_apply]`. Use `conv_rhs => rw [pi_eq_sum_univ' x]`. Simplify using `[map_sum, map_smulₛₗ, cpt]`.
-/
theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]
  simp [map_sum, map_smulₛₗ, cpt]

/- English proof (translation)
Introduce `D Bs A X fc s R cr M eV hX hT`. Take `⟨L, hT⟩` from `hT`. Establish `hn : 0 < X.nP true` using `hX.pos.2.2 true`. Set `g` to `lin (fun k => D.jEE (R.eRR (Pi.single k 1)))`. Establish `hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x)` using `lin_single_cpt _ R.eRR D.jEE`.

Establish `hsurj : Function.Surjective g`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩`. Establish `key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z)`.

Introduce `z`. Rewrite using `[← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, M.eR_eq]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases h : i = k <;> simp [cpt, h]`. Establish `hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z`. Introduce `z`. Use function extensionality and compare the values at `i`.

Apply the tactic sequence `cases s <;> simp [cjv, cj]`. Use `⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `hsurj F`. Rewrite using `[key, ← hX.h2.2.2]`. Conclude with `⟨_, rfl⟩`.

Rewrite `he` using `[← hX.h2.2.2]`. Take `⟨z, rfl⟩` from `he`. Conclude with `⟨g (cjv s z), by rw [key, hcc]⟩`. Take `⟨z, rfl⟩` from `hsurj F`. Rewrite using `[key]`.

Establish `hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _)` using `DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))`. Establish `hcj : Continuous (cj s)`. Consider the cases of `s`. Conclude with `continuous_id`. Conclude with `Complex.continuous_conj`.

Establish `hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z` using `continuous_pi fun i => hcj.comp (continuous_apply i)`. Establish `h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖` using `((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm`. Establish `h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖` using `continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm`. Use `hd.induction_on z (isClosed_eq h1 h2) fun x => ?_` and prove the remaining obligations. Establish `hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x`.

Use function extensionality and compare the values at `i`. Simplify using `[cjv, cpt, R.twist]`. Establish `hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true)`. Simplify using `[CxData.XE, rowXE, rowFrame, spliceFrame]`. Establish `hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1)` using `li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)`.

Establish `hm` using `majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x`. Rewrite `hm` using `[lin_basis]`. Rewrite using `[hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K, ← Real.sqrt_mul hn.le]`. Use `erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re = (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]`. Rewrite using `[mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]`.
-/
theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z
    rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
