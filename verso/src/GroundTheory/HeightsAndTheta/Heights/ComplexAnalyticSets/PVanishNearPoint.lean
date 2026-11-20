import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteMapOpen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

/- English proof (translation)
Introduce `n J f x hJ hx hf`. Assume the negation of the conclusion as `hfJ`. Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J)` using `Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top`. Take `⟨d, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)`. Use `choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))`.

Establish `hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[hp]`. Substitute `hg` using the available equality.

Set `_` to `((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra`. Establish `hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f)` using `RingHom.IsIntegral.of_finite hfin _`. Establish `hf0 : Ideal.Quotient.mk J f ≠ 0`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]` and apply the resulting hypothesis. Take `⟨h, hh, hh0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)`.

Rewrite `hh` using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `hh`. Take `⟨q, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `hJmem : aeval p h - q * f ∈ J`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]`.

Conclude with `ha.symm`. Establish `hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f`. Introduce `z hz`. Establish `h1` using `hz _ hJmem`. Rewrite `h1` using `[map_sub, map_mul, sub_eq_zero]`.

Rewrite using `[← h1]`. Establish `h2` using `DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h`. Rewrite `h2` using `[AlgHom.comp_apply]`. Conclude with `h2.symm`. Establish `hV` using `hOpen n d J p hJ hinj hfin x hx _ hf`.

Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hV`. Apply `hh0` to reduce the goal to its premises. Use `MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε) (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_` and prove the remaining obligations. Rewrite `hw` using `[← ball_pi _ hε]`. Take `⟨z, ⟨hz, hzU⟩, rfl⟩` from `hball hw`.

Rewrite using `[hval z hz, hzU hz, mul_zero, map_zero]`.
-/
theorem VanishNearPoint.proof (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
