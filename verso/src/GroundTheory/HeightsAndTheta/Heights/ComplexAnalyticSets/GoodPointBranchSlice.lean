import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.NormalModelFibreNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

namespace GoodPointBranch

def consZero (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (Fin d → ℂ) →L[ℂ] ℂ) 0
    fun j => ContinuousLinearMap.proj j)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]`.
-/
theorem consZero_apply {d : ℕ} (v : Fin d → ℂ) : consZero d v = Fin.cons 0 v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consZero]

/- English proof (translation)
Rewrite using `[consZero_apply]`. Both sides reduce to the same expression.
-/
theorem consZero_apply_zero {d : ℕ} (v : Fin d → ℂ) : consZero d v 0 = 0 := by
  rw [consZero_apply]
  rfl

/- English proof (translation)
Rewrite using `[consZero_apply, ← ht]`. Conclude with `Fin.cons_self_tail t`.
-/
theorem consZero_tail {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) : consZero d (Fin.tail t) = t := by
  rw [consZero_apply, ← ht]
  exact Fin.cons_self_tail t

/- English proof (translation)
Introduce `a b h` and use `by rw [consZero_apply, consZero_apply] at h exact Fin.cons_right_injective _ h`.
-/
theorem consZero_injective {d : ℕ} : Function.Injective (consZero d) := fun a b h => by
  rw [consZero_apply, consZero_apply] at h
  exact Fin.cons_right_injective _ h

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_ball_zero_iff]`. Establish `hs : 0 < s` using `lt_of_le_of_lt (norm_nonneg _) hv`. Rewrite using `[pi_norm_lt_iff hs]`. Introduce `i`. Rewrite using `[consZero_apply]`.

Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hs`. Simplify using `using (norm_le_pi_norm v j).trans_lt hv`.
-/
theorem consZero_mem_ball {d : ℕ} {s : ℝ} {v : Fin d → ℂ} (hv : v ∈ ball (0 : Fin d → ℂ) s) :
    consZero d v ∈ ball (0 : Fin (d + 1) → ℂ) s := by
  rw [mem_ball_zero_iff] at hv ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hv
  rw [pi_norm_lt_iff hs]
  intro i
  rw [consZero_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hs
  · simpa using (norm_le_pi_norm v j).trans_lt hv

/- English proof (translation)
Rewrite `ht`, the goal using `[mem_ball_zero_iff]`. Establish `hs : 0 < s` using `lt_of_le_of_lt (norm_nonneg _) ht`. Rewrite using `[pi_norm_lt_iff hs]`. Introduce `j`. Conclude with `(norm_le_pi_norm t j.succ).trans_lt ht`.
-/
theorem tail_mem_ball {d : ℕ} {s : ℝ} {t : Fin (d + 1) → ℂ} (ht : t ∈ ball (0 : Fin (d + 1) → ℂ) s) :
    Fin.tail t ∈ ball (0 : Fin d → ℂ) s := by
  rw [mem_ball_zero_iff] at ht ⊢
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) ht
  rw [pi_norm_lt_iff hs]
  intro j
  exact (norm_le_pi_norm t j.succ).trans_lt ht

def consCLM (d : ℕ) : (ℂ × (Fin d → ℂ)) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cons (α := fun _ => (ℂ × (Fin d → ℂ)) →L[ℂ] ℂ)
    (ContinuousLinearMap.fst ℂ ℂ (Fin d → ℂ))
    fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin d → ℂ)))

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp [consCLM]`.
-/
theorem consCLM_apply {d : ℕ} (p : ℂ × (Fin d → ℂ)) : consCLM d p = vecCons p.1 p.2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [consCLM]

/- English proof (translation)
Use `analyticOnNhd_pi_iff.2 fun j => ?_` and prove the remaining obligations. Establish `hj : DifferentiableOn ℂ (fun t => f t j) U` using `differentiableOn_pi.1 hf j`. Use `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_` and prove the remaining obligations. Establish `hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i))`. Rewrite using `[Function.update_eq_self]`.

Conclude with `(hj w hw).differentiableAt (hU.mem_nhds hw)`. Conclude with `hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt`.
-/
theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn
    fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

/- English proof (translation)
Use `set σ : (Fin d → ℂ) → Fin n → ℂ := fun v => ψ (consZero d v) with hσdef`. Establish `hσ : HasStrictFDerivAt σ (D.comp (consZero d)) 0`. Establish `h0 : HasStrictFDerivAt ψ D (consZero d 0)` using `by rw [map_zero]; exact hψ`. Conclude with `h0.comp 0 (consZero d).hasStrictFDerivAt`. Establish `hσ0 : σ 0 = q` using `by simp [hσdef, hψ0]`.

Establish `hev : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), σ v ∈ S ∧ σ v ∈ V` using `hslice.and (hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hV.mem_nhds hqV))`. Establish `hgA : ∀ x ∈ S, x ∈ V → g (A x) = x`. Introduce `x hxS hxV`. Establish `hx : x ∈ g '' O` using `by rw [← hS]; exact ⟨hxS, hxV⟩`. Take `⟨y, hy, rfl⟩` from `hx`.

Rewrite using `[hAg y hy]`. Establish `hqS : q ∈ S` using `hσ0 ▸ hev.self_of_nhds.1`. Establish `hAqO : A q ∈ O`. Establish `hq : q ∈ g '' O` using `by rw [← hS]; exact ⟨hqS, hqV⟩`. Take `⟨y, hy, hyq⟩` from `hq`.

Rewrite using `[← hyq, hAg y hy]`. Conclude with `hy`. Establish `hcomp : σ =ᶠ[𝓝 0] fun v => g (A (σ v))` using `hev.mono fun v hv => (hgA _ hv.1 hv.2).symm`. Establish `hgd : HasFDerivAt g (fderiv ℂ g (A q)) (A (σ 0))`. Rewrite using `[hσ0]`.

Conclude with `(hg _ hAqO).differentiableAt.hasFDerivAt`. Establish `h2 : HasFDerivAt (fun v => g (A (σ v))) ((fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d)))) 0` using `hgd.comp 0 (A.hasFDerivAt.comp 0 hσ.hasFDerivAt)`. Establish `heq : D.comp (consZero d) = (fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d)))` using `hσ.hasFDerivAt.unique (h2.congr_of_eventuallyEq hcomp)`. Establish `ha : ∀ v, v 0 = 0 → A (D v) = 0 → v = 0`. Introduce `v hv0 hAv`.

Apply `hD v hv0` to reduce the goal to its premises. Establish `h` using `congrArg (fun L : (Fin d → ℂ) →L[ℂ] Fin n → ℂ => L (Fin.tail v)) heq`. Simplify using `only [ContinuousLinearMap.comp_apply, consZero_tail v hv0, hAv, map_zero] at h`. Conclude with `h`. Use `⟨ha, ?_⟩` and prove the remaining obligations.

Establish `hinj : Function.Injective (A.comp (D.comp (consZero d)))`. Introduce `a b hab`. Simplify using `only [ContinuousLinearMap.comp_apply] at hab`. Establish `h0 : A (D (consZero d (a - b))) = 0` using `by rw [map_sub, map_sub, map_sub, hab, sub_self]`. Establish `h1` using `ha _ (consZero_apply_zero _) h0`.

Conclude with `sub_eq_zero.1 (consZero_injective (by rw [h1, map_zero]))`. Set `e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)` to `(LinearEquiv.ofInjectiveEndo ((A.comp (D.comp (consZero d))) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) hinj).toContinuousLinearEquiv`. Establish `he : (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = A.comp (D.comp (consZero d))`. Use extensionality with `v`. Both sides reduce to the same expression.

Establish `hF : HasStrictFDerivAt (fun v => A (σ v)) (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0`. Rewrite using `[he]`. Conclude with `A.hasStrictFDerivAt.comp 0 hσ`. Establish `hΦ : ⇑(hF.toOpenPartialHomeomorph (fun v => A (σ v))) = fun v => A (σ v)` using `hF.toOpenPartialHomeomorph_coe`. Use `⟨(hF.toOpenPartialHomeomorph _).source ∩ {v | σ v ∈ S ∧ σ v ∈ V}, inter_mem ((hF.toOpenPartialHomeomorph _).open_source.mem_nhds hF.mem_toOpenPartialHomeomorph_source) hev, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a ha' b hb' hab`. Conclude with `(hF.toOpenPartialHomeomorph _).injOn ha'.1 hb'.1 (by rw [hΦ]; exact congrArg A hab)`. Introduce `W' hW' hW'W`. Establish `himg : (fun v => A (σ v)) '' W' ∈ 𝓝 (A q)`. Establish `h1 : (fun v => A (σ v)) '' W' ∈ map (fun v => A (σ v)) (𝓝 0)` using `image_mem_map hW'`.

Rewrite `h1` using `[hF.map_nhds_eq_of_equiv]`. Simplify `h1` using `only [hσ0]`. Use `⟨V ∩ A ⁻¹' ((fun v => A (σ v)) '' W'), inter_mem (hV.mem_nhds hqV) (A.continuous.continuousAt.preimage_mem_nhds himg), ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxS, hxV, hxW⟩`. Take `⟨v, hv, hvx⟩` from `hxW`.

Establish `hvx' : A (σ v) = A x` using `hvx`. Establish `hvW` using `hW'W hv`. Use `⟨v, hv, ?_⟩` and prove the remaining obligations. Use `show σ v = x`. Rewrite using `[← hgA _ hvW.2.1 hvW.2.2, hvx', hgA x hxS hxV]`.
-/
theorem slice_chart {d n : ℕ} {ψ : (Fin (d + 1) → ℂ) → Fin n → ℂ} {D : (Fin (d + 1) → ℂ) →L[ℂ] Fin n → ℂ}
    {q : Fin n → ℂ} {S : Set (Fin n → ℂ)} {A : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)} {O : Set (Fin d → ℂ)}
    {V : Set (Fin n → ℂ)} {g : (Fin d → ℂ) → Fin n → ℂ}
    (hψ : HasStrictFDerivAt ψ D 0) (hψ0 : ψ 0 = q) (hD : ∀ v, v 0 = 0 → D v = 0 → v = 0)
    (hV : IsOpen V) (hqV : q ∈ V) (hg : AnalyticOnNhd ℂ g O) (hAg : ∀ y ∈ O, A (g y) = y)
    (hS : S ∩ V = g '' O) (hslice : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), ψ (consZero d v) ∈ S) :
    (∀ v, v 0 = 0 → A (D v) = 0 → v = 0) ∧
    ∃ W ∈ 𝓝 (0 : Fin d → ℂ), Set.InjOn (fun v => ψ (consZero d v)) W ∧
      ∀ W' ∈ 𝓝 (0 : Fin d → ℂ), W' ⊆ W → ∃ N ∈ 𝓝 q, S ∩ N ⊆ (fun v => ψ (consZero d v)) '' W' := by
  set σ : (Fin d → ℂ) → Fin n → ℂ := fun v => ψ (consZero d v) with hσdef
  have hσ : HasStrictFDerivAt σ (D.comp (consZero d)) 0 := by
    have h0 : HasStrictFDerivAt ψ D (consZero d 0) := by rw [map_zero]; exact hψ
    exact h0.comp 0 (consZero d).hasStrictFDerivAt
  have hσ0 : σ 0 = q := by simp [hσdef, hψ0]
  have hev : ∀ᶠ v in 𝓝 (0 : Fin d → ℂ), σ v ∈ S ∧ σ v ∈ V :=
    hslice.and (hσ.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact hV.mem_nhds hqV))
  have hgA : ∀ x ∈ S, x ∈ V → g (A x) = x := by
    intro x hxS hxV
    have hx : x ∈ g '' O := by rw [← hS]; exact ⟨hxS, hxV⟩
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hAg y hy]
  have hqS : q ∈ S := hσ0 ▸ hev.self_of_nhds.1
  have hAqO : A q ∈ O := by
    have hq : q ∈ g '' O := by rw [← hS]; exact ⟨hqS, hqV⟩
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq, hAg y hy]
    exact hy
  have hcomp : σ =ᶠ[𝓝 0] fun v => g (A (σ v)) := hev.mono fun v hv => (hgA _ hv.1 hv.2).symm
  have hgd : HasFDerivAt g (fderiv ℂ g (A q)) (A (σ 0)) := by
    rw [hσ0]
    exact (hg _ hAqO).differentiableAt.hasFDerivAt
  have h2 : HasFDerivAt (fun v => g (A (σ v))) ((fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d)))) 0 :=
    hgd.comp 0 (A.hasFDerivAt.comp 0 hσ.hasFDerivAt)
  have heq : D.comp (consZero d) = (fderiv ℂ g (A q)).comp (A.comp (D.comp (consZero d))) :=
    hσ.hasFDerivAt.unique (h2.congr_of_eventuallyEq hcomp)
  have ha : ∀ v, v 0 = 0 → A (D v) = 0 → v = 0 := by
    intro v hv0 hAv
    apply hD v hv0
    have h := congrArg (fun L : (Fin d → ℂ) →L[ℂ] Fin n → ℂ => L (Fin.tail v)) heq
    simp only [ContinuousLinearMap.comp_apply, consZero_tail v hv0, hAv, map_zero] at h
    exact h
  refine ⟨ha, ?_⟩
  have hinj : Function.Injective (A.comp (D.comp (consZero d))) := by
    intro a b hab
    simp only [ContinuousLinearMap.comp_apply] at hab
    have h0 : A (D (consZero d (a - b))) = 0 := by rw [map_sub, map_sub, map_sub, hab, sub_self]
    have h1 := ha _ (consZero_apply_zero _) h0
    exact sub_eq_zero.1 (consZero_injective (by rw [h1, map_zero]))
  let e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) :=
    (LinearEquiv.ofInjectiveEndo ((A.comp (D.comp (consZero d))) : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ))
      hinj).toContinuousLinearEquiv
  have he : (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) = A.comp (D.comp (consZero d)) := by
    ext v
    rfl
  have hF : HasStrictFDerivAt (fun v => A (σ v)) (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0 := by
    rw [he]
    exact A.hasStrictFDerivAt.comp 0 hσ
  have hΦ : ⇑(hF.toOpenPartialHomeomorph (fun v => A (σ v))) = fun v => A (σ v) :=
    hF.toOpenPartialHomeomorph_coe
  refine ⟨(hF.toOpenPartialHomeomorph _).source ∩ {v | σ v ∈ S ∧ σ v ∈ V},
    inter_mem ((hF.toOpenPartialHomeomorph _).open_source.mem_nhds hF.mem_toOpenPartialHomeomorph_source) hev,
    ?_, ?_⟩
  · intro a ha' b hb' hab
    exact (hF.toOpenPartialHomeomorph _).injOn ha'.1 hb'.1 (by rw [hΦ]; exact congrArg A hab)
  · intro W' hW' hW'W
    have himg : (fun v => A (σ v)) '' W' ∈ 𝓝 (A q) := by
      have h1 : (fun v => A (σ v)) '' W' ∈ map (fun v => A (σ v)) (𝓝 0) := image_mem_map hW'
      rw [hF.map_nhds_eq_of_equiv] at h1
      simpa only [hσ0] using h1
    refine ⟨V ∩ A ⁻¹' ((fun v => A (σ v)) '' W'),
      inter_mem (hV.mem_nhds hqV) (A.continuous.continuousAt.preimage_mem_nhds himg), ?_⟩
    rintro x ⟨hxS, hxV, hxW⟩
    obtain ⟨v, hv, hvx⟩ := hxW
    have hvx' : A (σ v) = A x := hvx
    have hvW := hW'W hv
    refine ⟨v, hv, ?_⟩
    show σ v = x
    rw [← hgA _ hvW.2.1 hvW.2.2, hvx', hgA x hxS hxV]

end GoodPointBranch

end

end GroundTheory.Heights₂.Heights
