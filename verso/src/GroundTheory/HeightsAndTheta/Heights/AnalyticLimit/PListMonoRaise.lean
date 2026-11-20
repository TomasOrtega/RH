import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StListMonoRaise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_add_smul levi_re_analytic)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential potSmoothAt)

/- English proof (translation)
Introduce `D X _ A Yo th Om u hYo hth hOm hu hle hnn x k y hy w`. Use `set s := (A.chart k).symm with hs`. Establish `hyt : y ∈ (A.chart k).target` using `hy.1`. Establish `hyYo : s y ∈ Yo` using `hy.2.1`. Establish `hyOx : s y ∈ Om.U x` using `hy.2.2.1`.

Establish `hadd : ∀ {f g : (Fin D → ℂ) → ℝ}, ContDiffAt ℝ 2 f y → ContDiffAt ℝ 2 g y → levi (fun v => f v + g v) y w = levi f y w + levi g y w`. Introduce `f g hf hg`. Simplify using `using levi_add_smul 1 hf hg w`. Establish `hus : ContDiffAt ℝ 2 (u ∘ s) y` using `((hu k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hYo).mem_nhds ⟨hyt, hyYo⟩)).of_le (WithTop.coe_le_coe.2 le_top)`. Establish `hths : ContDiffAt ℝ 2 (th.φ (s y) ∘ s) y` using `potSmoothAt A th hth (s y) k ⟨hyt, th.mem_U _⟩`.

Establish `hOms : ContDiffAt ℝ 2 (Om.φ (s y) ∘ s) y` using `potSmoothAt A Om hOm (s y) k ⟨hyt, Om.mem_U _⟩`. Take `⟨W, hWo, hpW, G, hG, hGeq⟩` from `hOm.2 (s y) x (s y) ⟨Om.mem_U _, hyOx⟩`. Establish `hGa : AnalyticAt ℂ (G ∘ s) y` using `hG k y ⟨hyt, hpW⟩`. Establish `hGre : ContDiffAt ℝ 2 (fun v => ((G ∘ s) v).re) y` using `(Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars.contDiffAt (n := 2)))`. Establish `hVo : IsOpen ((A.chart k).target ∩ s ⁻¹' (W ∩ Om.U (s y) ∩ Om.U x))` using `(A.chart k).isOpen_inter_preimage_symm ((hWo.inter (Om.isOpen_U _)).inter (Om.isOpen_U x))`.

Establish `hgerm : (potForm Om u).φ x ∘ s =ᶠ[𝓝 y] fun v => ((Om.φ (s y) ∘ s) v + (u ∘ s) v) + (-1) * ((G ∘ s) v).re` using `by filter_upwards [hVo.mem_nhds ⟨hyt, ⟨hpW, Om.mem_U _⟩, hyOx⟩] with v hv`. Use `hGeq (s v) hv.2` as an intermediate fact. Use `show Om.φ x (s v) + u (s v) = (Om.φ (s y) (s v) + u (s v)) + (-1) * (G (s v)).re`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hΩ : levi ((potForm Om u).φ x ∘ s) y w = levi (Om.φ (s y) ∘ s) y w + levi (u ∘ s) y w`.

Rewrite using `[levi_congr hgerm, levi_add_smul (-1) (hOms.add hus) hGre, levi_re_analytic hGa, hadd hOms hus]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hle (s y) k y ⟨hyt, ⟨trivial, th.mem_U _⟩, Om.mem_U _⟩ w`. Establish `h2` using `hnn (s y) k y ⟨hyt, hyYo, th.mem_U _, trivial⟩ w`. Establish `hT : levi ((potForm th u).φ (s y) ∘ s) y w = levi (th.φ (s y) ∘ s) y w + levi (u ∘ s) y w` using `hadd hths hus`.

Rewrite `h2` using `[hT]`. Rewrite using `[hΩ]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ListMonoRaise.proof : ListMonoRaise.Statement := by
  intro D X _ A Yo th Om u hYo hth hOm hu hle hnn x k y hy w
  set s := (A.chart k).symm with hs
  have hyt : y ∈ (A.chart k).target := hy.1
  have hyYo : s y ∈ Yo := hy.2.1
  have hyOx : s y ∈ Om.U x := hy.2.2.1

  have hadd : ∀ {f g : (Fin D → ℂ) → ℝ}, ContDiffAt ℝ 2 f y → ContDiffAt ℝ 2 g y →
      levi (fun v => f v + g v) y w = levi f y w + levi g y w := by
    intro f g hf hg
    simpa using levi_add_smul 1 hf hg w

  have hus : ContDiffAt ℝ 2 (u ∘ s) y :=
    ((hu k).contDiffAt (((A.chart k).isOpen_inter_preimage_symm hYo).mem_nhds ⟨hyt, hyYo⟩)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hths : ContDiffAt ℝ 2 (th.φ (s y) ∘ s) y := potSmoothAt A th hth (s y) k ⟨hyt, th.mem_U _⟩
  have hOms : ContDiffAt ℝ 2 (Om.φ (s y) ∘ s) y := potSmoothAt A Om hOm (s y) k ⟨hyt, Om.mem_U _⟩

  obtain ⟨W, hWo, hpW, G, hG, hGeq⟩ := hOm.2 (s y) x (s y) ⟨Om.mem_U _, hyOx⟩
  have hGa : AnalyticAt ℂ (G ∘ s) y := hG k y ⟨hyt, hpW⟩
  have hGre : ContDiffAt ℝ 2 (fun v => ((G ∘ s) v).re) y :=
    (Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars.contDiffAt (n := 2)))
  have hVo : IsOpen ((A.chart k).target ∩ s ⁻¹' (W ∩ Om.U (s y) ∩ Om.U x)) :=
    (A.chart k).isOpen_inter_preimage_symm ((hWo.inter (Om.isOpen_U _)).inter (Om.isOpen_U x))
  have hgerm : (potForm Om u).φ x ∘ s =ᶠ[𝓝 y]
      fun v => ((Om.φ (s y) ∘ s) v + (u ∘ s) v) + (-1) * ((G ∘ s) v).re := by
    filter_upwards [hVo.mem_nhds ⟨hyt, ⟨hpW, Om.mem_U _⟩, hyOx⟩] with v hv
    have := hGeq (s v) hv.2
    show Om.φ x (s v) + u (s v) = (Om.φ (s y) (s v) + u (s v)) + (-1) * (G (s v)).re
    linarith
  have hΩ : levi ((potForm Om u).φ x ∘ s) y w = levi (Om.φ (s y) ∘ s) y w + levi (u ∘ s) y w := by
    rw [levi_congr hgerm, levi_add_smul (-1) (hOms.add hus) hGre, levi_re_analytic hGa,
      hadd hOms hus]
    ring

  have h1 := hle (s y) k y ⟨hyt, ⟨trivial, th.mem_U _⟩, Om.mem_U _⟩ w
  have h2 := hnn (s y) k y ⟨hyt, hyYo, th.mem_U _, trivial⟩ w
  have hT : levi ((potForm th u).φ (s y) ∘ s) y w = levi (th.φ (s y) ∘ s) y w + levi (u ∘ s) y w :=
    hadd hths hus
  rw [hT] at h2
  rw [hΩ]
  linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
