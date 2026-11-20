import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatPrimeDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonvanishDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

/- English proof (translation)
Repeatedly rewrite using `[aeval_def, ← eval_map]`. Conclude with `MvPolynomial.continuous_eval _`.
-/
theorem RatPrimeDense.continuous_aeval {σ : Type} (g : MvPolynomial σ ℚ) :
    Continuous fun z : σ → ℂ => aeval z g := by
  simp_rw [aeval_def, ← eval_map]
  exact MvPolynomial.continuous_eval _

/- English proof (translation)
Introduce `σ _ P f hP hf x hx`. Take `⟨e, ℓ, u, G, c, D, hG, hc, hD, hint, hGz, hcf, hlift, hsep⟩` from `h₁ σ P f x hP hf hx`. Use `set L : (σ → ℂ) → Fin e → ℂ := fun z j => aeval z (ℓ j) with hL`. Establish `hLc : Continuous L` using `continuous_pi fun j => RatPrimeDense.continuous_aeval (ℓ j)`. Establish `huc : Continuous fun z : σ → ℂ => aeval z u` using `RatPrimeDense.continuous_aeval u`.

Establish `hZ : IsClosed {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0}`. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_iInter fun g => isClosed_iInter fun _ => isClosed_eq (RatPrimeDense.continuous_aeval g) continuous_const`. Use `choose p hp hpz using hint`. Use `choose R hR using fun i => h₃ e (p i) (hp i) (L x)`.

Use `set Rb : ℝ := ∑ i, max (R i) 0`. Establish `hRb : 0 ≤ Rb` using `Finset.sum_nonneg fun i _ => le_max_right _ _`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Use `set C := ({z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ∩ Metric.closedBall 0 Rb) ∩ {z | ε ≤ dist z x}`.

Establish `hCc : IsCompact C` using `((isCompact_closedBall 0 Rb).inter_left hZ).inter_right (isClosed_le continuous_const (continuous_id.dist continuous_const))`. Use `set φ : (σ → ℂ) → ℝ := fun z => dist (L z) (L x) + dist (aeval z u) (aeval x u)`. Establish `hφc : Continuous φ` using `(hLc.dist continuous_const).add (huc.dist continuous_const)`. Choose the witnesses or unpack the hypotheses as in `⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ C, δ ≤ φ z := by`. Break down `C.eq_empty_or_nonempty with hC | hC` into its components or cases.

Conclude with `⟨1, one_pos, by simp [hC]⟩`. Take `⟨z₀, hz₀, hmin⟩` from `hCc.exists_isMinOn hC hφc.continuousOn`. Use `⟨φ z₀, ?_, fun z hz => hmin hz⟩` and prove the remaining obligations. Use `lt_of_le_of_ne (add_nonneg dist_nonneg dist_nonneg) fun h0 => ?_` and prove the remaining obligations. Establish `h1` using `(add_eq_zero_iff_of_nonneg dist_nonneg dist_nonneg).mp h0.symm`.

Use `hsep z₀ hz₀.1.1 (dist_eq_zero.mp h1.1) (dist_eq_zero.mp h1.2)` as an intermediate fact. Establish `h2` using `hz₀.2`. Simplify using `only [Set.mem_ofPred_eq, this, dist_self] at h2`. Conclude with `absurd h2 (not_le.mpr hε)`. Establish `hE : ∀ᶠ y in 𝓝 (L x), (∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧ dist t (aeval x u) < δ / 2) ∧ (∀ i, ∀ t : ℂ, (p i).eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R i) ∧ dist y (L x) < δ / 2` using `(h₂ e G hG (L x) (aeval x u) (hGz x hx) (δ / 2) (half_pos hδ)).and ((eventually_all.mpr hR).and (Metric.ball_mem_nhds _ (half_pos hδ)))`.

Take `⟨y, ⟨⟨t, ht, htd⟩, hyR, hyd⟩, hyB⟩` from `(mem_closure_iff_nhds.mp (h₄ e (D * c) (mul_ne_zero hD hc) (L x)) _ hE)`. Simplify using `only [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hyB`. Take `⟨z, hz, hzy, hzt⟩` from `hlift y t hyB.1 ht`. Establish `hzL : L z = y` using `hzy`. Use `⟨z, ⟨hz, hcf z hz (by rw [hzy]; exact hyB.2)⟩, ?_⟩` and prove the remaining obligations.

Establish `hzR : z ∈ Metric.closedBall 0 Rb`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRb]`. Introduce `i`. Use `hyR i (z i) (by rw [← hzL]; exact hpz i z hz)` as an intermediate fact. Conclude with `this.trans ((le_max_left _ _).trans (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))`.

Assume the negation of the conclusion as `hfar`. Establish `hφz : φ z < δ`. Express the relevant statement in the definitionally equal form `dist (L z) (L x) + dist (aeval z u) (aeval x u) < δ`. Rewrite using `[hzL, hzt]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `absurd (hδC z ⟨⟨hz, hzR⟩, by show ε ≤ dist z x; rw [dist_comm]; exact not_lt.mp hfar⟩) (not_le.mpr hφz)`.
-/
theorem RatPrimeDense.proof (h₁ : FiniteSeparatingModel.Statement) (h₂ : RootsNear.Statement)
    (h₃ : RootsBounded.Statement) (h₄ : PolyNonvanishDense.Statement) : RatPrimeDense.Statement := by
  intro σ _ P f hP hf x hx
  obtain ⟨e, ℓ, u, G, c, D, hG, hc, hD, hint, hGz, hcf, hlift, hsep⟩ := h₁ σ P f x hP hf hx
  set L : (σ → ℂ) → Fin e → ℂ := fun z j => aeval z (ℓ j) with hL
  have hLc : Continuous L := continuous_pi fun j => RatPrimeDense.continuous_aeval (ℓ j)
  have huc : Continuous fun z : σ → ℂ => aeval z u := RatPrimeDense.continuous_aeval u
  have hZ : IsClosed {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun g => isClosed_iInter fun _ =>
      isClosed_eq (RatPrimeDense.continuous_aeval g) continuous_const

  choose p hp hpz using hint
  choose R hR using fun i => h₃ e (p i) (hp i) (L x)
  set Rb : ℝ := ∑ i, max (R i) 0
  have hRb : 0 ≤ Rb := Finset.sum_nonneg fun i _ => le_max_right _ _
  rw [Metric.mem_closure_iff]
  intro ε hε
  set C := ({z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ∩ Metric.closedBall 0 Rb) ∩ {z | ε ≤ dist z x}
  have hCc : IsCompact C := ((isCompact_closedBall 0 Rb).inter_left hZ).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  set φ : (σ → ℂ) → ℝ := fun z => dist (L z) (L x) + dist (aeval z u) (aeval x u)
  have hφc : Continuous φ :=
    (hLc.dist continuous_const).add (huc.dist continuous_const)
  obtain ⟨δ, hδ, hδC⟩ : ∃ δ > 0, ∀ z ∈ C, δ ≤ φ z := by
    rcases C.eq_empty_or_nonempty with hC | hC
    · exact ⟨1, one_pos, by simp [hC]⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hCc.exists_isMinOn hC hφc.continuousOn
    refine ⟨φ z₀, ?_, fun z hz => hmin hz⟩
    refine lt_of_le_of_ne (add_nonneg dist_nonneg dist_nonneg) fun h0 => ?_
    have h1 := (add_eq_zero_iff_of_nonneg dist_nonneg dist_nonneg).mp h0.symm
    have := hsep z₀ hz₀.1.1 (dist_eq_zero.mp h1.1) (dist_eq_zero.mp h1.2)
    have h2 := hz₀.2
    simp only [Set.mem_ofPred_eq, this, dist_self] at h2
    exact absurd h2 (not_le.mpr hε)

  have hE : ∀ᶠ y in 𝓝 (L x), (∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧
      dist t (aeval x u) < δ / 2) ∧ (∀ i, ∀ t : ℂ, (p i).eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R i) ∧
      dist y (L x) < δ / 2 :=
    (h₂ e G hG (L x) (aeval x u) (hGz x hx) (δ / 2) (half_pos hδ)).and
      ((eventually_all.mpr hR).and (Metric.ball_mem_nhds _ (half_pos hδ)))
  obtain ⟨y, ⟨⟨t, ht, htd⟩, hyR, hyd⟩, hyB⟩ := (mem_closure_iff_nhds.mp
    (h₄ e (D * c) (mul_ne_zero hD hc) (L x)) _ hE)
  simp only [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hyB
  obtain ⟨z, hz, hzy, hzt⟩ := hlift y t hyB.1 ht
  have hzL : L z = y := hzy
  refine ⟨z, ⟨hz, hcf z hz (by rw [hzy]; exact hyB.2)⟩, ?_⟩
  have hzR : z ∈ Metric.closedBall 0 Rb := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hRb]
    intro i
    have := hyR i (z i) (by rw [← hzL]; exact hpz i z hz)
    exact this.trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun j _ => le_max_right (R j) 0) (Finset.mem_univ i)))
  by_contra hfar
  have hφz : φ z < δ := by
    change dist (L z) (L x) + dist (aeval z u) (aeval x u) < δ
    rw [hzL, hzt]
    linarith
  exact absurd (hδC z ⟨⟨hz, hzR⟩, by show ε ≤ dist z x; rw [dist_comm]; exact not_lt.mp hfar⟩) (not_le.mpr hφz)

end GroundTheory.Heights₂.Heights.HilbertSamuel
