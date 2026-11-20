import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology NNReal

/- English proof (translation)
Establish `h` using `MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)`. Use `h.congr fun y => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_map, MvPolynomial.aeval_def]`.
-/
theorem RootsBounded.continuous_aeval {e : ℕ} (g : MvPolynomial (Fin e) ℚ) :
    Continuous fun y : Fin e → ℂ => aeval y g := by
  have h := MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℂ) g)
  refine h.congr fun y => ?_
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

/- English proof (translation)
Introduce `e G hG y₀`. Use `set m := G.natDegree`. Set `a : ℕ → (Fin e → ℂ) → ℂ` to `fun k y => aeval y (G.coeff k)`. Use `⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩` and prove the remaining obligations. Establish `hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1`.

Rewrite using `[eventually_all_finset]`. Introduce `k _`. Establish `hc : Continuous fun y => ‖a k y‖₊` using `(RootsBounded.continuous_aeval (G.coeff k)).nnnorm`. Conclude with `hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le`. Use `filter_upwards [hev] with y hy t ht`.

Use `set P : Polynomial ℂ := G.map (aeval y).toRingHom`. Establish `hPm : P.Monic` using `hG.map _`. Establish `hdeg : P.natDegree = m` using `hG.natDegree_map _`. Establish `hroot : P.IsRoot t`. Rewrite using `[Polynomial.IsRoot, Polynomial.eval_map]`.

Conclude with `ht`. Establish `hlt` using `Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot`. Establish `hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1)`. Rewrite using `[Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]`. Use `gcongr`.

Rewrite using `[hdeg]`. Use `Finset.sup_le fun k hk => ?_` and prove the remaining obligations. Establish `hcoeff : P.coeff k = a k y`. Simplify using `[P, a, Polynomial.coeff_map]`. Rewrite using `[hcoeff]`.

Conclude with `(hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1) (fun _ _ => bot_le) hk)`. Establish `: ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1)` using `(hlt.trans_le hcb).le`. Conclude with `this` after adjusting the coercions.
-/
theorem RootsBounded.proof : RootsBounded.Statement := by
  intro e G hG y₀
  set m := G.natDegree
  let a : ℕ → (Fin e → ℂ) → ℂ := fun k y => aeval y (G.coeff k)
  refine ⟨((1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) : ℝ≥0) : ℝ), ?_⟩
  have hev : ∀ᶠ y in 𝓝 y₀, ∀ k ∈ Finset.range m, ‖a k y‖₊ ≤ ‖a k y₀‖₊ + 1 := by
    rw [eventually_all_finset]
    intro k _
    have hc : Continuous fun y => ‖a k y‖₊ :=
      (RootsBounded.continuous_aeval (G.coeff k)).nnnorm
    exact hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun _ h => h.le
  filter_upwards [hev] with y hy t ht
  set P : Polynomial ℂ := G.map (aeval y).toRingHom
  have hPm : P.Monic := hG.map _
  have hdeg : P.natDegree = m := hG.natDegree_map _
  have hroot : P.IsRoot t := by
    rw [Polynomial.IsRoot, Polynomial.eval_map]; exact ht
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hPm.ne_zero hroot
  have hcb : Polynomial.cauchyBound P ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := by
    rw [Polynomial.cauchyBound, hPm.leadingCoeff, nnnorm_one, div_one, add_comm]
    gcongr
    rw [hdeg]
    refine Finset.sup_le fun k hk => ?_
    have hcoeff : P.coeff k = a k y := by
      simp [P, a, Polynomial.coeff_map]
    rw [hcoeff]
    exact (hy k hk).trans (Finset.single_le_sum (f := fun k => ‖a k y₀‖₊ + 1)
      (fun _ _ => bot_le) hk)
  have : ‖t‖₊ ≤ 1 + ∑ k ∈ Finset.range m, (‖a k y₀‖₊ + 1) := (hlt.trans_le hcb).le
  exact_mod_cast this

end GroundTheory.Heights₂.Heights.HilbertSamuel
