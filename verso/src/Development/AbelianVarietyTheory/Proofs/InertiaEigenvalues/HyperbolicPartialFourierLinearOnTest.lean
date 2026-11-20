import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

/- English proof (translation)
Introduce `F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'`. Use `haveI := hν`. Use `haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective (IsModuleTopology.continuous_of_linearMap _)`. Establish `hψc : Continuous (fun t : F => ψ t)`. Rewrite using `[continuous_iff_continuousAt]`.

Introduce `t`. Establish `hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t` using `by filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs`. Establish `hst : s = t + (s - t)` using `by ring`. Establish `hn : ‖s - t‖ ≤ 1` using `by simpa [dist_eq_norm] using hs`. Rewrite using `[hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]`.

Conclude with `continuousAt_const.congr hev.symm`. Establish `htr : Continuous (fun t : A.K => Algebra.trace F A.K t)` using `IsModuleTopology.continuous_of_linearMap _`. Establish `hk : ∀ u, Continuous (fun b => kx A ψ x b u)` using `fun u => by`. Unfold `kx Et.psiK`. Conclude with `hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))`.

Establish `hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν`. Introduce `Ψ hΨ a u`. Establish `hc : Continuous (fun b => Ψ (a, b))` using `hΨ.1.continuous.comp (Continuous.prodMk_right a)`. Establish `hs : HasCompactSupport (fun b => Ψ (a, b))`. Apply `HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)` to reduce the goal to its premises.

Introduce `b hb`. Assume the negation of the conclusion as `h`. Conclude with `hb ⟨(a, b), subset_tsupport _ h, rfl⟩`. Conclude with `(hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right`. Use function extensionality and compare the values at `p`.

Establish `h1` using `hint Φ hΦ p.1 p.2`. Establish `h2` using `hint Φ' hΦ' p.1 p.2`. Simplify using `only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← integral_const_mul, ← integral_add (h1.const_mul c) h2]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring

end GlobalTheory.JR.Hyp
