import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Set

namespace GlobalTheory

/- English proof (translation)
Establish `hda : ∀ x ∈ C, HasFDerivAt (fun w => F (z, w)) ((fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ))) x`. Introduce `x hx`. Conclude with `(hF (z, x) ⟨hz, hx⟩).differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)`. Establish `hzero : ∀ x ∈ C, (fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ)) = 0`. Introduce `x hx`.

Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Apply `LinearMap.pi_ext` to reduce the goal to its premises. Introduce `a t`. Establish `e : ((0 : P), (Pi.single a t : Fin g → ℂ)) = t • ((0 : P), (Pi.single a 1 : Fin g → ℂ))`. Use `Prod.ext (by simp) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.

Use `show fderiv ℂ F (z, x) ((0 : P), Pi.single a t) = 0`. Rewrite using `[e, map_smul, hd a (z, x) ⟨hz, hx⟩, smul_zero]`. Conclude with `hCc.is_const_of_fderivWithin_eq_zero (fun x hx => (hda x hx).differentiableAt.differentiableWithinAt) (fun x hx => by rw [fderivWithin_of_isOpen hC hx, (hda x hx).fderiv, hzero x hx]) hy hy'`.
-/
private lemma eq_of_fderiv_fibre_zero_convex {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (F : P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (hC : IsOpen C)
    (hCc : Convex ℝ C) (hF : AnalyticOnNhd ℂ F (Z ×ˢ C))
    (hd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0)
    {z : P} (hz : z ∈ Z) {y y' : Fin g → ℂ} (hy : y ∈ C) (hy' : y' ∈ C) :
    F (z, y) = F (z, y') := by
  have hda : ∀ x ∈ C, HasFDerivAt (fun w => F (z, w))
      ((fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ))) x := by
    intro x hx
    exact (hF (z, x) ⟨hz, hx⟩).differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)
  have hzero : ∀ x ∈ C,
      (fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ)) = 0 := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.pi_ext
    intro a t
    have e : ((0 : P), (Pi.single a t : Fin g → ℂ)) = t • ((0 : P), (Pi.single a 1 : Fin g → ℂ)) := by
      refine Prod.ext (by simp) ?_
      funext j
      by_cases h : j = a
      · subst h; simp
      · simp [h]
    show fderiv ℂ F (z, x) ((0 : P), Pi.single a t) = 0
    rw [e, map_smul, hd a (z, x) ⟨hz, hx⟩, smul_zero]
  exact hCc.is_const_of_fderivWithin_eq_zero
    (fun x hx => (hda x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [fderivWithin_of_isOpen hC hx, (hda x hx).fderiv, hzero x hx]) hy hy'

/- English proof (translation)
Introduce `P _ _ _ g K W c ω Z C G G' hW hZ hC hCc hCn hcov hG hG'`. Take `⟨hGa, hGd, hGc⟩` from `hG`. Take `⟨hG'a, hG'd, hG'c⟩` from `hG'`. Establish `hov : ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G' k p = G l p - G' l p`. Introduce `k l p hk hl hp`.

Establish `h1` using `hGc k l p hk hl hp`. Establish `h2` using `hG'c k l p hk hl hp`. Take the linear combination `h1 - h2`. Set `F : P × (Fin g → ℂ) → ℂ` to `fun p => if h : ∃ k, p ∈ W k then G h.choose p - G' h.choose p else 0`. Establish `hFeq : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → F p = G k p - G' k p`.

Introduce `k p hk hp`. Establish `h : ∃ k, p ∈ W k` using `⟨k, hk⟩`. Simplify using `only [F, dif_pos h]`. Conclude with `hov _ _ p h.choose_spec hk hp`. Establish `hFloc : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → (fun q => G k q - G' k q) =ᶠ[nhds p] F`.

Introduce `k p hk hp`. Use `filter_upwards [((hW k).inter (hZ.prod hC)).mem_nhds ⟨hk, hp⟩] with q hq`. Conclude with `(hFeq k q hq.1 hq.2).symm`. Establish `hFa : AnalyticOnNhd ℂ F (Z ×ˢ C)`. Introduce `p hp`.

Take `⟨k, hk⟩` from `hcov p hp`. Conclude with `((hGa k p ⟨hk, hp⟩).sub (hG'a k p ⟨hk, hp⟩)).congr (hFloc k p hk hp)`. Establish `hFd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0`. Introduce `a p hp`. Take `⟨k, hk⟩` from `hcov p hp`.

Establish `hs : HasFDerivAt (fun q => G k q - G' k q) (fderiv ℂ (G k) p - fderiv ℂ (G' k) p) p` using `(hGa k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt.sub (hG'a k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt`. Rewrite using `[← (hFloc k p hk hp).fderiv_eq, hs.fderiv]`. Simplify using `[hGd k a p hk hp, hG'd k a p hk hp]`. Take `⟨y₀, hy₀⟩` from `hCn`. Use `⟨fun z => F (z, y₀), ?_, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Establish `hi : AnalyticAt ℂ (fun w : P => (w, y₀)) z` using `analyticAt_id.prod analyticAt_const`. Conclude with `AnalyticAt.comp (g := F) (f := fun w : P => (w, y₀)) (hFa (z, y₀) ⟨hz, hy₀⟩) hi`. Introduce `k p hk hp`. Establish `hc` using `eq_of_fderiv_fibre_zero_convex F Z C hC hCc hFa hFd hp.1 hp.2 hy₀`.

Establish `hp' : ((p.1, p.2) : P × (Fin g → ℂ)) = p` using `rfl`. Rewrite `hc` using `[hp']`. Use `show G k p = G' k p + F (p.1, y₀)`. Rewrite using `[← hc, hFeq k p hk hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_analytic_param_of_primitives_on_box : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → C.Nonempty → (∀ p ∈ Z ×ˢ C, ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G' k p - G' l p = c k l p) → ∃ h : P → ℂ, AnalyticOnNhd ℂ h Z ∧ ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → G k p = G' k p + h p.1 := by
  intro P _ _ _ g K W c ω Z C G G' hW hZ hC hCc hCn hcov hG hG'
  obtain ⟨hGa, hGd, hGc⟩ := hG
  obtain ⟨hG'a, hG'd, hG'c⟩ := hG'
  classical
  have hov : ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G' k p = G l p - G' l p := by
    intro k l p hk hl hp
    have h1 := hGc k l p hk hl hp
    have h2 := hG'c k l p hk hl hp
    linear_combination h1 - h2
  let F : P × (Fin g → ℂ) → ℂ := fun p =>
    if h : ∃ k, p ∈ W k then G h.choose p - G' h.choose p else 0
  have hFeq : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → F p = G k p - G' k p := by
    intro k p hk hp
    have h : ∃ k, p ∈ W k := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact hov _ _ p h.choose_spec hk hp
  have hFloc : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → (fun q => G k q - G' k q) =ᶠ[nhds p] F := by
    intro k p hk hp
    filter_upwards [((hW k).inter (hZ.prod hC)).mem_nhds ⟨hk, hp⟩] with q hq
    exact (hFeq k q hq.1 hq.2).symm
  have hFa : AnalyticOnNhd ℂ F (Z ×ˢ C) := by
    intro p hp
    obtain ⟨k, hk⟩ := hcov p hp
    exact ((hGa k p ⟨hk, hp⟩).sub (hG'a k p ⟨hk, hp⟩)).congr (hFloc k p hk hp)
  have hFd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0 := by
    intro a p hp
    obtain ⟨k, hk⟩ := hcov p hp
    have hs : HasFDerivAt (fun q => G k q - G' k q)
        (fderiv ℂ (G k) p - fderiv ℂ (G' k) p) p :=
      (hGa k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt.sub
        (hG'a k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt
    rw [← (hFloc k p hk hp).fderiv_eq, hs.fderiv]
    simp [hGd k a p hk hp, hG'd k a p hk hp]
  obtain ⟨y₀, hy₀⟩ := hCn
  refine ⟨fun z => F (z, y₀), ?_, ?_⟩
  · intro z hz
    have hi : AnalyticAt ℂ (fun w : P => (w, y₀)) z := analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := F) (f := fun w : P => (w, y₀)) (hFa (z, y₀) ⟨hz, hy₀⟩) hi
  · intro k p hk hp
    have hc := eq_of_fderiv_fibre_zero_convex F Z C hC hCc hFa hFd hp.1 hp.2 hy₀
    have hp' : ((p.1, p.2) : P × (Fin g → ℂ)) = p := rfl
    rw [hp'] at hc
    show G k p = G' k p + F (p.1, y₀)
    rw [← hc, hFeq k p hk hp]
    ring

end GlobalTheory
