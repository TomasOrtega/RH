import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.PshBack

/- English proof (translation)
Introduce `e X _ A B th x₀ j V g hAB hth hsrc hV hVt hg hlevi`. Establish `hτ : ∀ (k : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart k).target → (A.chart k).symm y ∈ (B.chart j).source → AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y` using `fun k y hy hp => hAB.1 k j y ⟨hy, hp⟩`. Use `⟨fun k y hy => ?_, fun x k y hy w => ?_⟩` and prove the remaining obligations. Take `⟨hyt, hp, hpV⟩` from `hy`. Establish `h1 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y)` using `hg.contDiffAt (hV.mem_nhds hpV)`.

Establish `h2 : ContDiffAt ℝ ∞ (B.chart j ∘ (A.chart k).symm) y` using `((hτ k y hyt hp).contDiffAt (n := ∞)).restrict_scalars ℝ`. Conclude with `(h1.comp y h2).contDiffWithinAt`. Take `⟨hyt, ⟨hpx, -⟩, hp, hpV⟩` from `hy`. Establish `hτy : AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y` using `hτ k y hyt hp`. Take `⟨W, hW, hpW, G, hG, hGe⟩` from `hth.2 x x₀ ((A.chart k).symm y) ⟨hpx, hsrc hp⟩`.

Establish `hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y` using `hG k y ⟨hyt, hpW⟩`. Set `h : (Fin e → ℂ) → ℝ` to `fun z' => th.φ x₀ ((B.chart j).symm z') + g z'`. Establish `hB : B.SmoothOn (th.U x₀) (th.φ x₀)` using `smoothOn_of_compatible hAB (th.isOpen_U x₀) (hth.1 x₀)`. Establish `hτyV : (B.chart j ∘ (A.chart k).symm) y ∈ V` using `hpV`. Establish `hh : ContDiffAt ℝ 2 h ((B.chart j ∘ (A.chart k).symm) y)`.

Establish `hmem : (B.chart j ∘ (A.chart k).symm) y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' th.U x₀`. Use `⟨hVt hτyV, ?_⟩` and prove the remaining obligations. Use `show (B.chart j).symm (B.chart j ((A.chart k).symm y)) ∈ th.U x₀`. Rewrite using `[(B.chart j).left_inv hp]`. Conclude with `hsrc hp`.

Establish `h1 : ContDiffAt ℝ ∞ (th.φ x₀ ∘ (B.chart j).symm) ((B.chart j ∘ (A.chart k).symm) y)` using `(hB j).contDiffAt (((B.chart j).isOpen_inter_preimage_symm (th.isOpen_U x₀)).mem_nhds hmem)`. Establish `h2 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y)` using `hg.contDiffAt (hV.mem_nhds hτyV)`. Conclude with `(h1.add h2).of_le (by norm_cast)`. Establish `hhτ : ContDiffAt ℝ 2 (h ∘ (B.chart j ∘ (A.chart k).symm)) y` using `hh.comp y ((hτy.contDiffAt).restrict_scalars ℝ)`. Establish `hGre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart k).symm) y').re) y` using `Complex.reCLM.contDiff.contDiffAt.comp y ((hGa.contDiffAt).restrict_scalars ℝ)`.

Establish `hopen : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source))` using `(A.chart k).isOpen_inter_preimage_symm (((hW.inter (th.isOpen_U x)).inter (th.isOpen_U x₀)).inter (B.chart j).open_source)`. Establish `hymem : y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source)` using `⟨hyt, ⟨⟨hpW, hpx⟩, hsrc hp⟩, hp⟩`. Establish `hev : ((th + LocPot.ofFun (g ∘ B.chart j)).φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y] (fun y' => (h ∘ (B.chart j ∘ (A.chart k).symm)) y' + 1 * ((G ∘ (A.chart k).symm) y').re)` using `by filter_upwards [hopen.mem_nhds hymem] with y' hy'`. Take `⟨-, ⟨⟨hW', hx'⟩, hx0'⟩, hs'⟩` from `hy'`. Establish `hd` using `hGe _ ⟨⟨hW', hx'⟩, hx0'⟩`.

Express the relevant statement in the definitionally equal form `th.φ x ((A.chart k).symm y') + g (B.chart j ((A.chart k).symm y')) = th.φ x₀ ((B.chart j).symm (B.chart j ((A.chart k).symm y'))) + g (B.chart j ((A.chart k).symm y')) + 1 * (G ((A.chart k).symm y')).re`. Rewrite using `[(B.chart j).left_inv hs']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1` using `levi_add_smul (f := h ∘ (B.chart j ∘ (A.chart k).symm)) (g := fun y' => ((G ∘ (A.chart k).symm) y').re) (z := y) 1 hhτ hGre w`. Rewrite using `[levi_congr hev w, e1, levi_re_analytic hGa w, levi_comp w hτy hh]`.

Use `hlevi _ hτyV (fderiv ℂ (B.chart j ∘ (A.chart k).symm) y w)` as an intermediate fact. Simplify using `only [mul_zero, add_zero]`. Conclude with `this`.
-/
theorem smoothOn_isPshOn_chartBack : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ),
    A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V →
    V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V →
    (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) →
    A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧
      IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  intro e X _ A B th x₀ j V g hAB hth hsrc hV hVt hg hlevi
  have hτ : ∀ (k : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart k).target →
      (A.chart k).symm y ∈ (B.chart j).source →
      AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := fun k y hy hp => hAB.1 k j y ⟨hy, hp⟩
  refine ⟨fun k y hy => ?_, fun x k y hy w => ?_⟩
  · obtain ⟨hyt, hp, hpV⟩ := hy
    have h1 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hpV)
    have h2 : ContDiffAt ℝ ∞ (B.chart j ∘ (A.chart k).symm) y :=
      ((hτ k y hyt hp).contDiffAt (n := ∞)).restrict_scalars ℝ
    exact (h1.comp y h2).contDiffWithinAt
  · obtain ⟨hyt, ⟨hpx, -⟩, hp, hpV⟩ := hy
    have hτy : AnalyticAt ℂ (B.chart j ∘ (A.chart k).symm) y := hτ k y hyt hp
    obtain ⟨W, hW, hpW, G, hG, hGe⟩ := hth.2 x x₀ ((A.chart k).symm y) ⟨hpx, hsrc hp⟩
    have hGa : AnalyticAt ℂ (G ∘ (A.chart k).symm) y := hG k y ⟨hyt, hpW⟩
    let h : (Fin e → ℂ) → ℝ := fun z' => th.φ x₀ ((B.chart j).symm z') + g z'
    have hB : B.SmoothOn (th.U x₀) (th.φ x₀) :=
      smoothOn_of_compatible hAB (th.isOpen_U x₀) (hth.1 x₀)
    have hτyV : (B.chart j ∘ (A.chart k).symm) y ∈ V := hpV
    have hh : ContDiffAt ℝ 2 h ((B.chart j ∘ (A.chart k).symm) y) := by
      have hmem : (B.chart j ∘ (A.chart k).symm) y ∈
          (B.chart j).target ∩ (B.chart j).symm ⁻¹' th.U x₀ := by
        refine ⟨hVt hτyV, ?_⟩
        show (B.chart j).symm (B.chart j ((A.chart k).symm y)) ∈ th.U x₀
        rw [(B.chart j).left_inv hp]
        exact hsrc hp
      have h1 : ContDiffAt ℝ ∞ (th.φ x₀ ∘ (B.chart j).symm) ((B.chart j ∘ (A.chart k).symm) y) :=
        (hB j).contDiffAt
          (((B.chart j).isOpen_inter_preimage_symm (th.isOpen_U x₀)).mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ g ((B.chart j ∘ (A.chart k).symm) y) := hg.contDiffAt (hV.mem_nhds hτyV)
      exact (h1.add h2).of_le (by norm_cast)
    have hhτ : ContDiffAt ℝ 2 (h ∘ (B.chart j ∘ (A.chart k).symm)) y :=
      hh.comp y ((hτy.contDiffAt).restrict_scalars ℝ)
    have hGre : ContDiffAt ℝ 2 (fun y' => ((G ∘ (A.chart k).symm) y').re) y :=
      Complex.reCLM.contDiff.contDiffAt.comp y ((hGa.contDiffAt).restrict_scalars ℝ)
    have hopen : IsOpen ((A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source)) :=
      (A.chart k).isOpen_inter_preimage_symm
        (((hW.inter (th.isOpen_U x)).inter (th.isOpen_U x₀)).inter (B.chart j).open_source)
    have hymem : y ∈ (A.chart k).target ∩
        (A.chart k).symm ⁻¹' (W ∩ th.U x ∩ th.U x₀ ∩ (B.chart j).source) :=
      ⟨hyt, ⟨⟨hpW, hpx⟩, hsrc hp⟩, hp⟩
    have hev : ((th + LocPot.ofFun (g ∘ B.chart j)).φ x ∘ (A.chart k).symm) =ᶠ[𝓝 y]
        (fun y' => (h ∘ (B.chart j ∘ (A.chart k).symm)) y' +
          1 * ((G ∘ (A.chart k).symm) y').re) := by
      filter_upwards [hopen.mem_nhds hymem] with y' hy'
      obtain ⟨-, ⟨⟨hW', hx'⟩, hx0'⟩, hs'⟩ := hy'
      have hd := hGe _ ⟨⟨hW', hx'⟩, hx0'⟩
      change th.φ x ((A.chart k).symm y') + g (B.chart j ((A.chart k).symm y')) =
        th.φ x₀ ((B.chart j).symm (B.chart j ((A.chart k).symm y'))) +
          g (B.chart j ((A.chart k).symm y')) + 1 * (G ((A.chart k).symm y')).re
      rw [(B.chart j).left_inv hs']
      linarith
    have e1 := levi_add_smul (f := h ∘ (B.chart j ∘ (A.chart k).symm))
      (g := fun y' => ((G ∘ (A.chart k).symm) y').re) (z := y) 1 hhτ hGre w
    rw [levi_congr hev w, e1, levi_re_analytic hGa w, levi_comp w hτy hh]
    have := hlevi _ hτyV (fderiv ℂ (B.chart j ∘ (A.chart k).symm) y w)
    simp only [mul_zero, add_zero]
    exact this

end GlobalTheory.CompanionTheory.Metric.PshBack
