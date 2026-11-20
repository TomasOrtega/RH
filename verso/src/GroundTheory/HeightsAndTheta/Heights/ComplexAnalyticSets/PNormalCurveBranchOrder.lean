import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveBranchOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserBranchSimpleZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PointLocalRingOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

/- English proof (translation)
Introduce `n J M w r φ hJ hdim hr hdiff hinj hmaps hw0 g`. Establish `hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ)`. Rewrite using `[M.ringKrullDim_eq, hdim]`. Establish `hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal` using `hw0 ▸ hmaps (Metric.mem_ball_self hr)`. Take `⟨hdom, hD⟩` from `hdvr _ M.ideal w M.isPrime M.isIntegrallyClosed hdim' hwZ`.

Establish `hnear : ∀ q ∈ M.ideal, ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q = 0`. Use `fun q hq ↦ Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun τ hτ ↦ hmaps ?_ q hq` and prove the remaining obligations. Rewrite `hτ`, the goal using `[mem_ball_zero_iff]`. Conclude with `lt_of_le_of_lt (pi_norm_const_le τ) hτ`. Establish `hat0 : ∀ q, eval (φ fun _ ↦ (0 : ℂ)) q = eval w q` using `fun q ↦ by rw [← hw0]; rfl`.

Establish `han` using `fun q ↦ analyticAt_eval_disc hr hdiff q`. Establish `hne0 : ∀ q, eval w q ≠ 0 → ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q ≠ 0` using `fun q hq ↦ (han q).continuousAt.eventually_ne (by simpa [hat0] using hq)`. Establish `hord0 : ∀ q, eval w q ≠ 0 → analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) q) 0 = 0` using `fun q hq ↦ analyticOrderAt_eq_zero.2 (Or.inr (by simpa [hat0] using hq))`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (pointLocalRing M.ideal w)`. Take `⟨t, s₀, hs₀, hts⟩` from `pointLocalRing_exists_mul_eq M.ideal w ϖ`.

Establish `hassoc : Associated ϖ (algebraMap _ (pointLocalRing M.ideal w) t)` using `⟨(isUnit_algebraMap_pointLocalRing _ w s₀ hs₀).unit, hts⟩`. Establish `ht` using `hassoc.irreducible hϖ`. Establish `ht1` using `hsz _ M.ideal w t r φ M.isPrime M.isIntegrallyClosed hdim' ht hr hdiff hinj hmaps hw0`. Distinguish the cases in `hg : algebraMap _ (pointLocalRing M.ideal w) g = 0`. Rewrite using `[hg, ord_zero_eq_top_of_dvr, eq_comm, analyticOrderAt_eq_top]`.

Take `⟨s, hs, hsg⟩` from `pointLocalRing_exists_mul_mem M.ideal w g hg`. Use `filter_upwards [hnear _ hsg, hne0 s hs] with τ h1 h2`. Rewrite `h1` using `[map_mul]`. Conclude with `(mul_eq_zero.1 h1).resolve_left h2`. Take `⟨e, v, hv⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hg ht`.

Take `⟨a, s, hs, has⟩` from `pointLocalRing_exists_mul_eq M.ideal w (v : pointLocalRing M.ideal w)`. Establish `ha : eval w a ≠ 0` using `pointLocalRing_eval_ne_zero_of_isUnit M.ideal w hwZ a (by rw [← has]; exact v.isUnit.mul (isUnit_algebraMap_pointLocalRing _ w s hs))`. Establish `hrel : algebraMap _ (pointLocalRing M.ideal w) (g * a - t ^ e * s) = 0`. Rewrite using `[map_sub, map_mul, map_mul, map_pow, ← has, ← hv]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨s', hs', hmem⟩` from `pointLocalRing_exists_mul_mem M.ideal w _ hrel`. Establish `heq : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) =ᶠ[𝓝 0] (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s)` using `by filter_upwards [hnear _ hmem, hne0 s' hs'] with τ h1 h2`. Simplify using `only [map_mul, map_sub, map_pow] at h1`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)`. Establish `hL : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) 0 = analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 + analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) a) 0` using `analyticOrderAt_mul (han g) (han a)`.

Establish `hR : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) 0 = e • analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 + analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) s) 0`. Rewrite using `[← analyticOrderAt_pow (han t)]`. Conclude with `analyticOrderAt_mul ((han t).pow e) (han s)`. Establish `hc` using `analyticOrderAt_congr heq`. Rewrite `hc` using `[hL, hR, ht1, hord0 a ha, hord0 s hs, add_zero, add_zero]`.

Rewrite using `[hc, ← Ring.ord_mul_of_isUnit_right v.isUnit, hv, ord_pow_irreducible_of_dvr ht]`. Simplify using the standard rewrite rules.
-/
theorem NormalCurveBranchOrder.proof (hdvr : NormalCurvePointDVR.Statement)
    (hsz : UniformiserBranchSimpleZero.Statement) : NormalCurveBranchOrder.Statement := by
  intro n J M w r φ hJ hdim hr hdiff hinj hmaps hw0 g
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  obtain ⟨hdom, hD⟩ := hdvr _ M.ideal w M.isPrime M.isIntegrallyClosed hdim' hwZ
  have hnear : ∀ q ∈ M.ideal, ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q = 0 := by
    refine fun q hq ↦ Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun τ hτ ↦ hmaps ?_ q hq
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hat0 : ∀ q, eval (φ fun _ ↦ (0 : ℂ)) q = eval w q := fun q ↦ by rw [← hw0]; rfl
  have han := fun q ↦ analyticAt_eval_disc hr hdiff q
  have hne0 : ∀ q, eval w q ≠ 0 → ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q ≠ 0 :=
    fun q hq ↦ (han q).continuousAt.eventually_ne (by simpa [hat0] using hq)
  have hord0 : ∀ q, eval w q ≠ 0 → analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) q) 0 = 0 :=
    fun q hq ↦ analyticOrderAt_eq_zero.2 (Or.inr (by simpa [hat0] using hq))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointLocalRing M.ideal w)
  obtain ⟨t, s₀, hs₀, hts⟩ := pointLocalRing_exists_mul_eq M.ideal w ϖ
  have hassoc : Associated ϖ (algebraMap _ (pointLocalRing M.ideal w) t) :=
    ⟨(isUnit_algebraMap_pointLocalRing _ w s₀ hs₀).unit, hts⟩
  have ht := hassoc.irreducible hϖ
  have ht1 := hsz _ M.ideal w t r φ M.isPrime M.isIntegrallyClosed hdim' ht hr hdiff hinj hmaps hw0
  by_cases hg : algebraMap _ (pointLocalRing M.ideal w) g = 0
  · rw [hg, ord_zero_eq_top_of_dvr, eq_comm, analyticOrderAt_eq_top]
    obtain ⟨s, hs, hsg⟩ := pointLocalRing_exists_mul_mem M.ideal w g hg
    filter_upwards [hnear _ hsg, hne0 s hs] with τ h1 h2
    rw [map_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hg ht
  obtain ⟨a, s, hs, has⟩ := pointLocalRing_exists_mul_eq M.ideal w (v : pointLocalRing M.ideal w)
  have ha : eval w a ≠ 0 := pointLocalRing_eval_ne_zero_of_isUnit M.ideal w hwZ a
    (by rw [← has]; exact v.isUnit.mul (isUnit_algebraMap_pointLocalRing _ w s hs))
  have hrel : algebraMap _ (pointLocalRing M.ideal w) (g * a - t ^ e * s) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, ← has, ← hv]
    ring
  obtain ⟨s', hs', hmem⟩ := pointLocalRing_exists_mul_mem M.ideal w _ hrel
  have heq : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) =ᶠ[𝓝 0]
      (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) := by
    filter_upwards [hnear _ hmem, hne0 s' hs'] with τ h1 h2
    simp only [map_mul, map_sub, map_pow] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)
  have hL : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) 0 =
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) a) 0 :=
    analyticOrderAt_mul (han g) (han a)
  have hR : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) 0 =
      e • analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) s) 0 := by
    rw [← analyticOrderAt_pow (han t)]
    exact analyticOrderAt_mul ((han t).pow e) (han s)
  have hc := analyticOrderAt_congr heq
  rw [hL, hR, ht1, hord0 a ha, hord0 s hs, add_zero, add_zero] at hc
  rw [hc, ← Ring.ord_mul_of_isUnit_right v.isUnit, hv, ord_pow_irreducible_of_dvr ht]
  simp

end GroundTheory.Heights₂.Heights
