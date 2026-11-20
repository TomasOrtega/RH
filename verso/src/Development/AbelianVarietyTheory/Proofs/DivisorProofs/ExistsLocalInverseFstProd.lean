import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
open Filter Topology Set Metric MeasureTheory GlobalTheory.ChernReg
open scoped ContDiff

namespace GlobalTheory.LocalInverseProduct

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- English proof (translation)
Use `set f : E × E →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E E).prod D with hf`. Establish `hu : IsUnit ((D.comp (ContinuousLinearMap.inr ℝ E E)) : E →ₗ[ℝ] E)` using `(LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)`. Establish `hinj2 : Function.Injective (D.comp (ContinuousLinearMap.inr ℝ E E))`. Use `(Module.End.isUnit_iff _).1 hu` as an intermediate fact. Conclude with `this.1`.

Establish `hinj : Function.Injective (f : E × E →ₗ[ℝ] E × E)`. Introduce `v w hvw`. Express the relevant statement in the definitionally equal form `f v = f w at hvw`. Establish `h1 : v.1 = w.1` using `by simpa [f] using congrArg Prod.fst hvw`. Establish `h2 : D v = D w` using `by simpa [f] using congrArg Prod.snd hvw`.

Establish `hv : v = (v.1, 0) + (0, v.2)` using `by simp`. Establish `hw : w = (w.1, 0) + (0, w.2)` using `by simp`. Establish `h3 : D (0, v.2) = D (0, w.2)`. Establish `e1 : D v = D (v.1, 0) + D (0, v.2)` using `by rw [← map_add]; simp`. Establish `e2 : D w = D (w.1, 0) + D (0, w.2)` using `by rw [← map_add]; simp`.

Rewrite `h2` using `[e1, e2, h1]`. Conclude with `add_left_cancel h2`. Establish `h4 : v.2 = w.2` using `hinj2 (by simpa using h3)`. Conclude with `Prod.ext h1 h4`. Use `⟨(LinearEquiv.ofInjectiveEndo (f : E × E →ₗ[ℝ] E × E) hinj).toContinuousLinearEquiv, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext v <;> rfl`.
-/
theorem exists_equiv_fst_prod (D : E × E →L[ℝ] E)
    (h : (D.comp (ContinuousLinearMap.inr ℝ E E)).det ≠ 0) :
    ∃ L : (E × E) ≃L[ℝ] (E × E),
      (L : E × E →L[ℝ] E × E) = (ContinuousLinearMap.fst ℝ E E).prod D := by
  set f : E × E →L[ℝ] E × E := (ContinuousLinearMap.fst ℝ E E).prod D with hf
  have hu : IsUnit ((D.comp (ContinuousLinearMap.inr ℝ E E)) : E →ₗ[ℝ] E) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have hinj2 : Function.Injective (D.comp (ContinuousLinearMap.inr ℝ E E)) := by
    have := (Module.End.isUnit_iff _).1 hu
    exact this.1
  have hinj : Function.Injective (f : E × E →ₗ[ℝ] E × E) := by
    intro v w hvw
    change f v = f w at hvw
    have h1 : v.1 = w.1 := by simpa [f] using congrArg Prod.fst hvw
    have h2 : D v = D w := by simpa [f] using congrArg Prod.snd hvw
    have hv : v = (v.1, 0) + (0, v.2) := by simp
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    have h3 : D (0, v.2) = D (0, w.2) := by
      have e1 : D v = D (v.1, 0) + D (0, v.2) := by rw [← map_add]; simp
      have e2 : D w = D (w.1, 0) + D (0, w.2) := by rw [← map_add]; simp
      rw [e1, e2, h1] at h2
      exact add_left_cancel h2
    have h4 : v.2 = w.2 := hinj2 (by simpa using h3)
    exact Prod.ext h1 h4
  refine ⟨(LinearEquiv.ofInjectiveEndo (f : E × E →ₗ[ℝ] E × E) hinj).toContinuousLinearEquiv, ?_⟩
  ext v <;> rfl

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun ξ => G (p.1, ξ)) ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)) p.2`. Use `hG.hasFDerivAt` as an intermediate fact. Establish `h2` using `hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2`. Conclude with `this.comp p.2 (by simpa using h2)`. Conclude with `h1.fderiv`.
-/
theorem fderiv_partial_eq {G : E × E → E} {p : E × E} (hG : DifferentiableAt ℝ G p) :
    fderiv ℝ (fun ξ => G (p.1, ξ)) p.2 = (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E) := by
  have h1 : HasFDerivAt (fun ξ => G (p.1, ξ))
      ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)) p.2 := by
    have := hG.hasFDerivAt
    have h2 := hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2
    exact this.comp p.2 (by simpa using h2)
  exact h1.fderiv

/- English proof (translation)
Use `set Φ : E × E → E × E := fun p => (p.1, G p) with hΦ`. Establish `hGd : ∀ p ∈ N, DifferentiableAt ℝ G p` using `fun p hp => (hG.contDiffAt (hN.mem_nhds hp)).differentiableAt (by simp)`. Establish `hΦd : ∀ p ∈ N, HasFDerivAt Φ ((ContinuousLinearMap.fst ℝ E E).prod (fderiv ℝ G p)) p` using `fun p hp => (hasFDerivAt_fst).prodMk (hGd p hp).hasFDerivAt`. Establish `hpart : ∀ p ∈ N, fderiv ℝ (fun ξ => G (p.1, ξ)) p.2 = (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)` using `fun p hp => fderiv_partial_eq (hGd p hp)`. Use `set W : Set (E × E) := N ∩ (fun p => ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)).det) ⁻¹' {0}ᶜ with hW`.

Establish `hWo : IsOpen W`. Apply `ContinuousOn.isOpen_inter_preimage _ hN isOpen_compl_singleton` to reduce the goal to its premises. Establish `hc : ContinuousOn (fderiv ℝ G) N` using `hG.continuousOn_fderiv_of_isOpen hN (by simp)`. Establish `hc2 : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)) N` using `((ContinuousLinearMap.compL ℝ E (E × E) E).flip (ContinuousLinearMap.inr ℝ E E)).continuous.comp_continuousOn hc`. Conclude with `ContinuousLinearMap.continuous_det.comp_continuousOn hc2`.

Establish `hz0 : (fderiv ℝ G (z₀, 0)).comp (ContinuousLinearMap.inr ℝ E E) = ContinuousLinearMap.id ℝ E`. Rewrite using `[← hpart _ hz, hD.fderiv]`. Establish `hzW : (z₀, (0 : E)) ∈ W`. Use `⟨hz, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]`.

Rewrite using `[hz0]`. Use `show LinearMap.det ((ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0`. Rewrite using `[ContinuousLinearMap.coe_id, LinearMap.det_id]`. Conclude with `one_ne_zero`. Establish `hL : ∀ p ∈ W, ∃ L : (E × E) ≃L[ℝ] (E × E), HasFDerivAt Φ (L : E × E →L[ℝ] E × E) p`.

Introduce `p hp`. Take `⟨L, hL⟩` from `exists_equiv_fst_prod (fderiv ℝ G p) hp.2`. Conclude with `⟨L, hL ▸ hΦd p hp.1⟩`. Establish `hΦc : ∀ p ∈ N, ContDiffAt ℝ ∞ Φ p` using `fun p hp => contDiffAt_fst.prodMk (hG.contDiffAt (hN.mem_nhds hp))`. Take `⟨L₀, hL₀⟩` from `hL _ hzW`.

Establish `hstrict : HasStrictFDerivAt Φ (L₀ : E × E →L[ℝ] E × E) (z₀, 0)`. Use `(hΦc _ hz).hasStrictFDerivAt (by simp)` as an intermediate fact. Rewrite `this` using `[hL₀.fderiv]`. Then use the resulting hypothesis. Use `set e₀ := hstrict.toOpenPartialHomeomorph Φ with he₀`. Establish `he₀c : (e₀ : E × E → E × E) = Φ` using `hstrict.toOpenPartialHomeomorph_coe`.

Use `⟨e₀.restrOpen W hWo, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Conclude with `⟨hstrict.mem_toOpenPartialHomeomorph_source, hzW⟩`. Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Conclude with `fun p hp => hp.2.1`.

Introduce `p _ show e₀ p = _`. Rewrite using `[he₀c]`. Introduce `a ha`. Establish `hs : (e₀.restrOpen W hWo).symm a ∈ (e₀.restrOpen W hWo).source` using `(e₀.restrOpen W hWo).map_target ha`. Rewrite `hs` using `[OpenPartialHomeomorph.restrOpen_source]`.

Take `⟨L, hLp⟩` from `hL _ hs.2`. Establish `hcoe : ((e₀.restrOpen W hWo) : E × E → E × E) = Φ` using `he₀c`. Use `(OpenPartialHomeomorph.contDiffAt_symm (e₀.restrOpen W hWo) (f₀' := L) ha ?_ ?_).contDiffWithinAt` and prove the remaining obligations. Rewrite using `[hcoe]`. Conclude with `hLp`.

Rewrite using `[hcoe]`. Conclude with `hΦc _ hs.2.1`. Introduce `p hp`. Rewrite `hp` using `[OpenPartialHomeomorph.restrOpen_source]`. Rewrite using `[hpart p hp.2.1]`.

Conclude with `hp.2.2`.
-/
theorem localInverse_fst_prod_general (N : Set (E × E)) (G : E × E → E) (z₀ : E)
    (hN : IsOpen N) (hz : (z₀, (0 : E)) ∈ N) (hG : ContDiffOn ℝ ∞ G N)
    (hD : HasFDerivAt (fun ξ => G (z₀, ξ)) (ContinuousLinearMap.id ℝ E) 0) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × E), (z₀, 0) ∈ e.source ∧ e.source ⊆ N ∧
      (∀ p ∈ e.source, e p = (p.1, G p)) ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p ∈ e.source, (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det ≠ 0 := by
  set Φ : E × E → E × E := fun p => (p.1, G p) with hΦ
  have hGd : ∀ p ∈ N, DifferentiableAt ℝ G p := fun p hp =>
    (hG.contDiffAt (hN.mem_nhds hp)).differentiableAt (by simp)
  have hΦd : ∀ p ∈ N, HasFDerivAt Φ ((ContinuousLinearMap.fst ℝ E E).prod (fderiv ℝ G p)) p :=
    fun p hp => (hasFDerivAt_fst).prodMk (hGd p hp).hasFDerivAt
  have hpart : ∀ p ∈ N, fderiv ℝ (fun ξ => G (p.1, ξ)) p.2
      = (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E) := fun p hp =>
    fderiv_partial_eq (hGd p hp)

  set W : Set (E × E) := N ∩ (fun p => ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)).det) ⁻¹' {0}ᶜ
    with hW
  have hWo : IsOpen W := by
    apply ContinuousOn.isOpen_inter_preimage _ hN isOpen_compl_singleton
    have hc : ContinuousOn (fderiv ℝ G) N := hG.continuousOn_fderiv_of_isOpen hN (by simp)
    have hc2 : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E E)) N :=
      ((ContinuousLinearMap.compL ℝ E (E × E) E).flip (ContinuousLinearMap.inr ℝ E E)).continuous.comp_continuousOn hc
    exact ContinuousLinearMap.continuous_det.comp_continuousOn hc2
  have hz0 : (fderiv ℝ G (z₀, 0)).comp (ContinuousLinearMap.inr ℝ E E) = ContinuousLinearMap.id ℝ E := by
    rw [← hpart _ hz, hD.fderiv]
  have hzW : (z₀, (0 : E)) ∈ W := by
    refine ⟨hz, ?_⟩
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [hz0]
    show LinearMap.det ((ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0
    rw [ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact one_ne_zero

  have hL : ∀ p ∈ W, ∃ L : (E × E) ≃L[ℝ] (E × E), HasFDerivAt Φ (L : E × E →L[ℝ] E × E) p := by
    intro p hp
    obtain ⟨L, hL⟩ := exists_equiv_fst_prod (fderiv ℝ G p) hp.2
    exact ⟨L, hL ▸ hΦd p hp.1⟩
  have hΦc : ∀ p ∈ N, ContDiffAt ℝ ∞ Φ p := fun p hp =>
    contDiffAt_fst.prodMk (hG.contDiffAt (hN.mem_nhds hp))
  obtain ⟨L₀, hL₀⟩ := hL _ hzW
  have hstrict : HasStrictFDerivAt Φ (L₀ : E × E →L[ℝ] E × E) (z₀, 0) := by
    have := (hΦc _ hz).hasStrictFDerivAt (by simp)
    rwa [hL₀.fderiv] at this
  set e₀ := hstrict.toOpenPartialHomeomorph Φ with he₀
  have he₀c : (e₀ : E × E → E × E) = Φ := hstrict.toOpenPartialHomeomorph_coe
  refine ⟨e₀.restrOpen W hWo, ?_, ?_, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hzW⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact fun p hp => hp.2.1
  · intro p _
    show e₀ p = _
    rw [he₀c]
  · intro a ha
    have hs : (e₀.restrOpen W hWo).symm a ∈ (e₀.restrOpen W hWo).source :=
      (e₀.restrOpen W hWo).map_target ha
    rw [OpenPartialHomeomorph.restrOpen_source] at hs
    obtain ⟨L, hLp⟩ := hL _ hs.2
    have hcoe : ((e₀.restrOpen W hWo) : E × E → E × E) = Φ := he₀c
    refine (OpenPartialHomeomorph.contDiffAt_symm (e₀.restrOpen W hWo) (f₀' := L) ha ?_ ?_).contDiffWithinAt
    · rw [hcoe]; exact hLp
    · rw [hcoe]; exact hΦc _ hs.2.1
  · intro p hp
    rw [OpenPartialHomeomorph.restrOpen_source] at hp
    rw [hpart p hp.2.1]
    exact hp.2.2

end GlobalTheory.LocalInverseProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `_ N G z₀ hN hz hG hD` and use `GlobalTheory.LocalInverseProduct.localInverse_fst_prod_general N G z₀ hN hz hG hD`.
-/
theorem localInverse_fst_prod : ∀ (d : ℕ) (N : Set ((Fin d → ℂ) × (Fin d → ℂ))) (G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ) (z₀ : Fin d → ℂ), IsOpen N → (z₀, 0) ∈ N → ContDiffOn ℝ ∞ G N → HasFDerivAt (fun ξ => G (z₀, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 → ∃ e : OpenPartialHomeomorph ((Fin d → ℂ) × (Fin d → ℂ)) ((Fin d → ℂ) × (Fin d → ℂ)), (z₀, 0) ∈ e.source ∧ e.source ⊆ N ∧ (∀ p ∈ e.source, e p = (p.1, G p)) ∧ ContDiffOn ℝ ∞ e.symm e.target ∧ ∀ p ∈ e.source, (fderiv ℝ (fun ξ => G (p.1, ξ)) p.2).det ≠ 0 :=
  fun _ N G z₀ hN hz hG hD => GlobalTheory.LocalInverseProduct.localInverse_fst_prod_general N G z₀ hN hz hG hD

end GlobalTheory
