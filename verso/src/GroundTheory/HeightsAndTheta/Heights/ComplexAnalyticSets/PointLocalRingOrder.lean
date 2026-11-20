import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

variable {σ : Type*}

/- English proof (translation)
Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl y`. Use `⟨a, s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)))))) (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) a s)`. Rewrite `h` using `[map_mul]`.

Conclude with `h`.
-/
theorem pointLocalRing_exists_mul_eq (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (x : pointLocalRing I w) :
    ∃ a s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧
      x * algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) s = algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl y
  refine ⟨a, s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have h := congrArg (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ)
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) a s)
  rw [map_mul] at h
  exact h

/- English proof (translation)
Use `set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)`. Establish `hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈ I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p))` using `Ideal.Quotient.eq_zero_iff_mem.1 hg`. Take `⟨⟨j, s⟩, hjs⟩` from `(IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem`. Use `⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩` and prove the remaining obligations. Establish `hinj` using `IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors`.

Establish `: (s : MvPolynomial σ ℂ) * g = j` using `hinj (by rw [map_mul, mul_comm]; exact hjs)`. Rewrite using `[this]`. Conclude with `j.2`.
-/
theorem pointLocalRing_exists_mul_mem (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈
      I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hg
  obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem
  refine ⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have : (s : MvPolynomial σ ℂ) * g = j := hinj (by rw [map_mul, mul_comm]; exact hjs)
  rw [this]
  exact j.2

/- English proof (translation)
Introduce `h0`. Use `set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)`. Establish `hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime p)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `g hg`.

Rewrite using `[Ideal.mem_comap]`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))`. Establish `hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)` using `(IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)`. Take `⟨v, hv⟩` from `hu.exists_right_inv`. Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective v`.

Establish `hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p))) (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1`. Rewrite using `[map_mul, map_one]`. Conclude with `hv`. Establish `hd` using `hle (Ideal.Quotient.eq.1 hv')`. Establish `h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)`.

Use `(IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem (Ideal.mul_mem_right z _ hum) hd` as an intermediate fact. Simplify using `at this`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem pointLocalRing_eval_ne_zero_of_isUnit (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by
  intro h0
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  have hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)))
      (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, map_one]
    exact hv
  have hd := hle (Ideal.Quotient.eq.1 hv')
  have h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    have := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem
      (Ideal.mul_mem_right z _ hum) hd
    simp at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Rewrite using `[Ring.ord_zero]`. Assume the negation of the conclusion as `h`. Establish `hfin` using `Module.length_ne_top_iff.1 h`. Take `⟨_, _⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.1 hfin`. Conclude with `IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)`.
-/
theorem ord_zero_eq_top_of_dvr (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by
  rw [Ring.ord_zero]
  by_contra h
  have hfin := Module.length_ne_top_iff.1 h
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

/- English proof (translation)
Rewrite using `[Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]`. Simplify using the standard rewrite rules.
-/
theorem ord_pow_irreducible_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [eval_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp => simp only [eval_mul, eval_X]`.

Conclude with `hp.mul (differentiable_apply i)`.
-/
theorem differentiable_eval_pointLocal [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

/- English proof (translation)
Establish `hc : DifferentiableOn ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r)` using `(differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn`. Establish `hmaps : Set.MapsTo (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) (Metric.ball 0 r)`. Introduce `τ hτ`. Rewrite `hτ`, the goal using `[mem_ball_zero_iff]`. Conclude with `lt_of_le_of_lt (pi_norm_const_le τ) hτ`.

Establish `hd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) (Metric.ball 0 r)` using `(differentiable_eval_pointLocal g).comp_differentiableOn (hφ.comp hc hmaps)`. Conclude with `hd.analyticAt (Metric.ball_mem_nhds 0 hr)`.
-/
theorem analyticAt_eval_disc [Fintype σ] {r : ℝ} (hr : 0 < r) {φ : (Fin 1 → ℂ) → σ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) (g : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 := by
  have hc : DifferentiableOn ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) :=
    (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn
  have hmaps : Set.MapsTo (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) (Metric.ball 0 r) := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) (Metric.ball 0 r) :=
    (differentiable_eval_pointLocal g).comp_differentiableOn (hφ.comp hc hmaps)
  exact hd.analyticAt (Metric.ball_mem_nhds 0 hr)

end

end GroundTheory.Heights₂.Heights
