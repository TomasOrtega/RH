import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveElementFibres
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `n d J A hJ hdim hA`. Take `⟨c, m, Δ, Q, hmon, hdeg, hΔ, hgood⟩` from `hP n d J A hJ hdim hA`. Use `set ℓ : (Fin n → ℂ) → ℂ := fun x => ∑ j, c j * x j with hℓ`. Establish `hdet : ∀ w, eval w Δ ≠ 0 → ∀ x ∈ fibre J A w, x = fun j => ((Q j).map (eval w)).eval (ℓ x) / eval w Δ`. Introduce `w hw x hx`.

Use function extensionality and compare the values at `j`. Rewrite using `[eq_div_iff hw, mul_comm]`. Conclude with `((hgood w hw).2.1 x hx).2 j`. Use `⟨Δ, hΔ, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨hsep, hfib, hsurj⟩` from `hgood y hy`.

Establish `hm0 : m.map (eval y) ≠ 0` using `(hmon.map _).ne_zero`. Establish `hinj : Set.InjOn ℓ (fibre J A y)` using `fun x hx x' hx' h => by`. Rewrite using `[hdet y hy x hx, hdet y hy x' hx', h]`. Establish `himg : ℓ '' fibre J A y = ↑(m.map (eval y)).roots.toFinset`. Use extensionality with `τ`.

Simplify using `only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hm0]`. Conclude with `⟨fun ⟨x, hx, hτ⟩ => hτ ▸ (hfib x hx).1, fun h => hsurj τ h⟩`. Establish `hfin : (fibre J A y).Finite` using `Set.Finite.of_finite_image (by rw [himg]; exact Finset.finite_toSet _) hinj`. Use `⟨hfin, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[← hinj.ncard_image, himg, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree, hmon.natDegree_map, hdeg]`.

Establish `hroot : (m.map (eval y)).IsRoot (ℓ x)` using `(hfib x hx).1`. Establish `hder : (m.map (eval y)).derivative.eval (ℓ x) ≠ 0`. Use `hsep.aeval_derivative_ne_zero (x := ℓ x) (by simpa [Polynomial.aeval_def] using hroot)` as an intermediate fact. Simplify `this` using `[Polynomial.aeval_def]`. Take `⟨U₀, B, ψ, hU₀o, hyU₀, hBo, hτB, hψd, hψy, hψ⟩` from `SimpleRootBranch.proof d m y (ℓ x) hroot hder`.

Use `set U : Set (Fin d → ℂ) := U₀ ∩ {w | eval w Δ ≠ 0} with hU`. Establish `hUo : IsOpen U` using `hU₀o.inter (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const)`. Use `set g : (Fin d → ℂ) → (Fin n → ℂ) := fun w j => ((Q j).map (eval w)).eval (ψ w) / eval w Δ with hg`. Establish `hkey : ∀ w ∈ U, g w ∈ fibre J A w ∧ ℓ (g w) = ψ w`. Introduce `w hw`.

Establish `hr : (m.map (eval w)).IsRoot (ψ w)` using `((hψ w hw.1).2 (ψ w) (hψ w hw.1).1).mpr rfl`. Take `⟨x', hx', hℓx'⟩` from `(hgood w hw.2).2.2 (ψ w) hr`. Establish `hℓx'' : ℓ x' = ψ w` using `hℓx'`. Establish `he : x' = g w` using `by rw [hdet w hw.2 x' hx']; simp only [hg]; rw [hℓx'']`. Conclude with `⟨he ▸ hx', he ▸ hℓx'⟩`.

Establish `hℓc : Continuous ℓ` using `by simp only [hℓ]; fun_prop`. Establish `hAc : Continuous fun z : Fin n → ℂ => A.mulVec z` using `continuous_const.matrix_mulVec continuous_id`. Use `⟨U, {z | A.mulVec z ∈ U ∧ ℓ z ∈ B}, g, hUo, ⟨hyU₀, hy⟩, (hUo.preimage hAc).inter (hBo.preimage hℓc), ⟨by rw [hx.2]; exact ⟨hyU₀, hy⟩, hτB⟩, fun w hw => ?_, ?_, fun w hw => (hkey w hw).1.2, ?_⟩` and prove the remaining obligations. Establish `hψw : DifferentiableAt ℂ ψ w` using `(hψd w hw.1).differentiableAt (hU₀o.mem_nhds hw.1)`. Use `DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)` and prove the remaining obligations.

Establish `hΔd : DifferentiableAt ℂ (fun w => eval w Δ) w` using `(AnalyticOnNhd.eval_mvPolynomial Δ w trivial).differentiableAt`. Establish `hF : DifferentiableAt ℂ (fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (w, ψ w)` using `(analyticAt_eval_map (Q j) (w, ψ w)).differentiableAt`. Establish `hQd : DifferentiableAt ℂ (fun w => ((Q j).map (eval w)).eval (ψ w)) w` using `DifferentiableAt.comp (g := fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (f := fun v => (v, ψ v)) w hF (differentiableAt_fun_id.prodMk hψw)`. Establish `hfun : (fun w => g w j) = fun w => ((Q j).map (eval w)).eval (ψ w) * (eval w Δ)⁻¹`. Use function extensionality and compare the values at `v`.

Simplify using `only [hg, div_eq_mul_inv]`. Rewrite using `[hfun]`. Conclude with `hQd.mul (hΔd.inv hw.2)`. Use function extensionality and compare the values at `j`. Rewrite using `[congrFun (hdet y hy x hx) j]`.

Simplify using `only [hg, hψy]`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, hzU, hzB⟩`. Establish `hzf : z ∈ fibre J A (A.mulVec z)` using `⟨hz, rfl⟩`.

Establish `hr` using `((hgood _ hzU.2).2.1 z hzf).1`. Establish `hℓz : ℓ z = ψ (A.mulVec z)` using `((hψ _ hzU.1).2 (ℓ z) hzB).mp hr`. Use `⟨A.mulVec z, hzU, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Rewrite using `[congrFun (hdet _ hzU.2 z hzf) j]`.

Simplify using `only [hg]`. Rewrite using `[hℓz]`. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨hf, hℓg⟩` from `hkey w hw`. Conclude with `⟨hf.1, by rw [hf.2]; exact hw, by rw [hℓg]; exact (hψ w hw.1).1⟩`.
-/
theorem DiscriminantCover.proof (hP : PrimitiveElementFibres.Statement) :
    DiscriminantCover.Statement := by
  intro n d J A hJ hdim hA
  obtain ⟨c, m, Δ, Q, hmon, hdeg, hΔ, hgood⟩ := hP n d J A hJ hdim hA
  set ℓ : (Fin n → ℂ) → ℂ := fun x => ∑ j, c j * x j with hℓ

  have hdet : ∀ w, eval w Δ ≠ 0 → ∀ x ∈ fibre J A w,
      x = fun j => ((Q j).map (eval w)).eval (ℓ x) / eval w Δ := by
    intro w hw x hx
    funext j
    rw [eq_div_iff hw, mul_comm]
    exact ((hgood w hw).2.1 x hx).2 j
  refine ⟨Δ, hΔ, fun y hy => ?_⟩
  obtain ⟨hsep, hfib, hsurj⟩ := hgood y hy
  have hm0 : m.map (eval y) ≠ 0 := (hmon.map _).ne_zero
  have hinj : Set.InjOn ℓ (fibre J A y) := fun x hx x' hx' h => by
    rw [hdet y hy x hx, hdet y hy x' hx', h]
  have himg : ℓ '' fibre J A y = ↑(m.map (eval y)).roots.toFinset := by
    ext τ
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hm0]
    exact ⟨fun ⟨x, hx, hτ⟩ => hτ ▸ (hfib x hx).1, fun h => hsurj τ h⟩
  have hfin : (fibre J A y).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact Finset.finite_toSet _) hinj
  refine ⟨hfin, ?_, fun x hx => ?_⟩
  · rw [← hinj.ncard_image, himg, Set.ncard_coe_finset,
      Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, hmon.natDegree_map, hdeg]

  have hroot : (m.map (eval y)).IsRoot (ℓ x) := (hfib x hx).1
  have hder : (m.map (eval y)).derivative.eval (ℓ x) ≠ 0 := by
    have := hsep.aeval_derivative_ne_zero (x := ℓ x) (by simpa [Polynomial.aeval_def] using hroot)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨U₀, B, ψ, hU₀o, hyU₀, hBo, hτB, hψd, hψy, hψ⟩ := SimpleRootBranch.proof d m y (ℓ x) hroot hder
  set U : Set (Fin d → ℂ) := U₀ ∩ {w | eval w Δ ≠ 0} with hU
  have hUo : IsOpen U := hU₀o.inter (isOpen_ne_fun (MvPolynomial.continuous_eval Δ) continuous_const)
  set g : (Fin d → ℂ) → (Fin n → ℂ) :=
    fun w j => ((Q j).map (eval w)).eval (ψ w) / eval w Δ with hg

  have hkey : ∀ w ∈ U, g w ∈ fibre J A w ∧ ℓ (g w) = ψ w := by
    intro w hw
    have hr : (m.map (eval w)).IsRoot (ψ w) := ((hψ w hw.1).2 (ψ w) (hψ w hw.1).1).mpr rfl
    obtain ⟨x', hx', hℓx'⟩ := (hgood w hw.2).2.2 (ψ w) hr
    have hℓx'' : ℓ x' = ψ w := hℓx'
    have he : x' = g w := by rw [hdet w hw.2 x' hx']; simp only [hg]; rw [hℓx'']
    exact ⟨he ▸ hx', he ▸ hℓx'⟩
  have hℓc : Continuous ℓ := by simp only [hℓ]; fun_prop
  have hAc : Continuous fun z : Fin n → ℂ => A.mulVec z := continuous_const.matrix_mulVec continuous_id
  refine ⟨U, {z | A.mulVec z ∈ U ∧ ℓ z ∈ B}, g, hUo, ⟨hyU₀, hy⟩,
    (hUo.preimage hAc).inter (hBo.preimage hℓc), ⟨by rw [hx.2]; exact ⟨hyU₀, hy⟩, hτB⟩,
    fun w hw => ?_, ?_, fun w hw => (hkey w hw).1.2, ?_⟩
  ·
    have hψw : DifferentiableAt ℂ ψ w := (hψd w hw.1).differentiableAt (hU₀o.mem_nhds hw.1)
    refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun j => ?_)
    have hΔd : DifferentiableAt ℂ (fun w => eval w Δ) w :=
      (AnalyticOnNhd.eval_mvPolynomial Δ w trivial).differentiableAt
    have hF : DifferentiableAt ℂ (fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2) (w, ψ w) :=
      (analyticAt_eval_map (Q j) (w, ψ w)).differentiableAt
    have hQd : DifferentiableAt ℂ (fun w => ((Q j).map (eval w)).eval (ψ w)) w :=
      DifferentiableAt.comp (g := fun v : (Fin d → ℂ) × ℂ => ((Q j).map (eval v.1)).eval v.2)
        (f := fun v => (v, ψ v)) w hF (differentiableAt_fun_id.prodMk hψw)
    have hfun : (fun w => g w j) = fun w => ((Q j).map (eval w)).eval (ψ w) * (eval w Δ)⁻¹ := by
      funext v; simp only [hg, div_eq_mul_inv]
    rw [hfun]
    exact hQd.mul (hΔd.inv hw.2)
  · funext j
    rw [congrFun (hdet y hy x hx) j]
    simp only [hg, hψy]
  · ext z
    constructor
    · rintro ⟨hz, hzU, hzB⟩
      have hzf : z ∈ fibre J A (A.mulVec z) := ⟨hz, rfl⟩
      have hr := ((hgood _ hzU.2).2.1 z hzf).1
      have hℓz : ℓ z = ψ (A.mulVec z) := ((hψ _ hzU.1).2 (ℓ z) hzB).mp hr
      refine ⟨A.mulVec z, hzU, ?_⟩
      funext j
      rw [congrFun (hdet _ hzU.2 z hzf) j]
      simp only [hg]
      rw [hℓz]
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨hf, hℓg⟩ := hkey w hw
      exact ⟨hf.1, by rw [hf.2]; exact hw, by rw [hℓg]; exact (hψ w hw.1).1⟩

end

end GroundTheory.Heights₂.Heights.ComplexSets
