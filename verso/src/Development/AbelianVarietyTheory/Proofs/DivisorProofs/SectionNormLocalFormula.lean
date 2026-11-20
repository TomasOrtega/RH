import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Take `⟨_, ⟨hsecH, hsecG⟩, hsnc, _⟩` from `hB i`. Use `set x := ψ.symm z with hx`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `A.cover x`. Establish `h1 : AnalyticAt ℂ (s i x ∘ (A.chart j).symm) (A.chart j x)`.

Apply `hsecH x j` to reduce the goal to its premises. Use `⟨(A.chart j).map_source hj, ?_⟩` and prove the remaining obligations. Use `show (A.chart j).symm (A.chart j x) ∈ (L i).U x`. Rewrite using `[(A.chart j).left_inv hj]`. Conclude with `(L i).mem_U x`.

Establish `h2 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z` using `(hψ j).2 z ⟨hz, hj⟩`. Establish `h3 : AnalyticAt ℂ ((s i x ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm)) z` using `AnalyticAt.comp h1 h2`. Use `h3.congr ?_` and prove the remaining obligations. Establish `hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source)` using `ψ.isOpen_inter_preimage_symm (A.chart j).open_source`. Use `filter_upwards [hO.mem_nhds ⟨hz, hj⟩] with y hy`.

Simplify using `only [Function.comp]`. Rewrite using `[(A.chart j).left_inv hy.2]`. Take `⟨ψ', _, hxψ', _, σ, _, hDσ, u, _, hu0, hs⟩` from `hsnc x`. Rewrite using `[hs x hxψ']`. Use `mul_ne_zero (hu0 x hxψ') ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `k _`. Consider the cases of `hk : σ k with`. Consider the case `none => simp`. Consider the case `some a`.

Simplify using `only`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Rewrite using `[Pi.single_eq_same, pow_one]`. Introduce `h0`.

Apply `hD` to reduce the goal to its premises. Establish `: x ∈ {y ∈ ψ'.source | ∃ a, σ k = some a ∧ ψ' y a = 0}` using `⟨hxψ', a, hk, h0⟩`. Rewrite `this` using `[← hDσ k]`. Conclude with `this.1`. Rewrite using `[Pi.single_eq_of_ne hki, pow_zero]`.

Conclude with `one_ne_zero`. Establish `hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (L i).U x)` using `ψ.isOpen_inter_preimage_symm ((L i).isOpen_U x)`. Establish `hzO : z ∈ ψ.target ∩ ψ.symm ⁻¹' (L i).U x` using `⟨hz, (L i).mem_U x⟩`. Use `filter_upwards [hO.mem_nhds hzO] with y hy`. Establish `hg` using `hsecG (ψ.symm y) x (ψ.symm y) ⟨(L i).mem_U _, hy.2⟩`.

Simplify using `only [normSec, Function.comp]`. Rewrite using `[hg, mul_pow, ← Real.exp_nat_mul]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem boundary_chart_facts {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (hB : IsBoundary A L s D) (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hψ : IsCompatChart A ψ) (z : Fin e → ℂ) (hz : z ∈ ψ.target) (hD : ψ.symm z ∉ D i) :
    AnalyticAt ℂ (s i (ψ.symm z) ∘ ψ.symm) z ∧ s i (ψ.symm z) (ψ.symm z) ≠ 0 ∧
      (fun y => normSec (L i) (s i) (ψ.symm y) ^ 2) =ᶠ[nhds z]
        (fun y => ‖(s i (ψ.symm z) ∘ ψ.symm) y‖ ^ 2 *
          Real.exp (-2 * ((L i).φ (ψ.symm z) ∘ ψ.symm) y)) := by
  obtain ⟨_, ⟨hsecH, hsecG⟩, hsnc, _⟩ := hB i
  set x := ψ.symm z with hx
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨j, hj⟩ := A.cover x
    have h1 : AnalyticAt ℂ (s i x ∘ (A.chart j).symm) (A.chart j x) := by
      apply hsecH x j
      refine ⟨(A.chart j).map_source hj, ?_⟩
      show (A.chart j).symm (A.chart j x) ∈ (L i).U x
      rw [(A.chart j).left_inv hj]
      exact (L i).mem_U x
    have h2 : AnalyticAt ℂ (A.chart j ∘ ψ.symm) z := (hψ j).2 z ⟨hz, hj⟩
    have h3 : AnalyticAt ℂ ((s i x ∘ (A.chart j).symm) ∘ (A.chart j ∘ ψ.symm)) z :=
      AnalyticAt.comp h1 h2
    refine h3.congr ?_
    have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
      ψ.isOpen_inter_preimage_symm (A.chart j).open_source
    filter_upwards [hO.mem_nhds ⟨hz, hj⟩] with y hy
    simp only [Function.comp]
    rw [(A.chart j).left_inv hy.2]
  ·
    obtain ⟨ψ', _, hxψ', _, σ, _, hDσ, u, _, hu0, hs⟩ := hsnc x
    rw [hs x hxψ']
    refine mul_ne_zero (hu0 x hxψ') ?_
    rw [Finset.prod_ne_zero_iff]
    intro k _
    cases hk : σ k with
    | none => simp
    | some a =>
      simp only
      by_cases hki : k = i
      · subst hki
        rw [Pi.single_eq_same, pow_one]
        intro h0
        apply hD
        have : x ∈ {y ∈ ψ'.source | ∃ a, σ k = some a ∧ ψ' y a = 0} := ⟨hxψ', a, hk, h0⟩
        rw [← hDσ k] at this
        exact this.1
      · rw [Pi.single_eq_of_ne hki, pow_zero]
        exact one_ne_zero
  ·
    have hO : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (L i).U x) :=
      ψ.isOpen_inter_preimage_symm ((L i).isOpen_U x)
    have hzO : z ∈ ψ.target ∩ ψ.symm ⁻¹' (L i).U x := ⟨hz, (L i).mem_U x⟩
    filter_upwards [hO.mem_nhds hzO] with y hy
    have hg := hsecG (ψ.symm y) x (ψ.symm y) ⟨(L i).mem_U _, hy.2⟩
    simp only [normSec, Function.comp]
    rw [hg, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

end GlobalTheory
