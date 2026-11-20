import Mathlib
open NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace GlobalTheory

/- English proof (translation)
Establish `hfib : ∀ σ : F →+* ℂ, c σ = c (InfinitePlace.mk σ).embedding`. Introduce `σ`. Establish `h1 : InfinitePlace.mk σ = InfinitePlace.mk (InfinitePlace.mk σ).embedding`. Rewrite using `[InfinitePlace.mk_embedding]`. Break down `InfinitePlace.mk_eq_iff.mp h1 with h | h` into its components or cases.

Rewrite using `[← h]`. Rewrite using `[← h]`. Establish `: ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ` using `RingHom.ext fun r => rfl`. Rewrite using `[this, hc]`. Use `set g : InfinitePlace F → ℝ := fun w => c w.embedding with hg`.

Establish `hsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * g w = 0`. Rewrite using `[← hs, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hf : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), c φ = g w`. Introduce `φ hφ`.

Rewrite using `[hfib φ, (Finset.mem_filter.mp hφ).2]`. Rewrite using `[Finset.sum_congr rfl hf, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]`. Set `B` to `(basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)`. Set `v : logSpace F` to `fun w => (w.1.mult : ℝ) * g w.1 / 2`. Set `r : Fin (rank F) → ℝ` to `fun i => B.repr v i`.

Establish `hB : ∀ i, (B i : logSpace F) = logEmbedding F (Additive.ofMul (fundSystem F i))`. Introduce `i`. Rewrite using `[Module.Basis.ofZLatticeBasis_apply, logEmbedding_fundSystem]`. Establish `hv : v = ∑ i, r i • B i` using `(B.sum_repr v).symm`. Use `set h : InfinitePlace F → ℝ := fun w => g w - ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) with hh`.

Establish `hne : ∀ w (hw : w ≠ w₀), h w = 0`. Introduce `w hw`. Establish `hvw` using `congrFun hv ⟨w, hw⟩`. Simplify using `only [v, Finset.sum_apply, Pi.smul_apply, hB, logEmbedding_component, smul_eq_mul] at hvw`. Establish `hvw' : (w.mult : ℝ) * g w / 2 = ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F)))` using `hvw`.

Establish `hm : (0 : ℝ) < w.mult` using `by exact_mod_cast InfinitePlace.mult_pos`. Establish `hS : (w.mult : ℝ) * ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) = 2 * ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F)))`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `: (w.mult : ℝ) * h w = 0`.

Simplify using `only [hh]`. Rewrite using `[mul_sub, hS, ← hvw']`. Expand and normalize the polynomial expressions, which then agree. Break down `mul_eq_zero.mp this with h0 | h0` into its components or cases. Conclude with `absurd h0 hm.ne'`.

Conclude with `h0`. Establish `htot : ∑ w : InfinitePlace F, (w.mult : ℝ) * h w = 0`. Establish `hi : ∀ i, ∑ w : InfinitePlace F, (w.mult : ℝ) * (r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F)))) = 0`. Introduce `i`. Establish `h0` using `sum_mult_mul_log (fundSystem F i)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring`. Use `_ = 0 := by rw [h0, mul_zero]`. Simplify using `only [hh, mul_sub, Finset.sum_sub_distrib, hsum, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, Finset.sum_eq_zero fun i _ => hi i, sub_zero]`.

Establish `hall : ∀ w, h w = 0`. Introduce `w`. Distinguish the cases in `hw : w = w₀`. Substitute `hw` using the available equality. Rewrite `htot` using `[Finset.sum_eq_single w₀ (fun b _ hb => by rw [hne b hb, mul_zero]) (fun h' => absurd (Finset.mem_univ _) h')]`.

Establish `hm : (0 : ℝ) < (w₀ : InfinitePlace F).mult` using `by exact_mod_cast InfinitePlace.mult_pos`. Break down `mul_eq_zero.mp htot with h0 | h0` into its components or cases. Conclude with `absurd h0 hm.ne'`. Conclude with `h0`. Conclude with `hne w hw`.

Use `⟨rank F, fundSystem F, r, fun σ => ?_⟩` and prove the remaining obligations. Establish `e1` using `hall (InfinitePlace.mk σ)`. Simplify using `only [hh, sub_eq_zero] at e1`. Rewrite using `[hfib σ]`. Use `e1.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[InfinitePlace.apply, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjInvariant_sum_zero_eq_sum_log_units (F : Type) [Field F] [NumberField F]
    (c : (F →+* ℂ) → ℝ) (hc : ∀ σ, c ((starRingEnd ℂ).comp σ) = c σ) (hs : ∑ σ, c σ = 0) :
    ∃ (m : ℕ) (u : Fin m → (𝓞 F)ˣ) (r : Fin m → ℝ), ∀ σ,
      c σ = ∑ j, r j * Real.log (‖σ ((u j : 𝓞 F) : F)‖ ^ 2) := by
  classical
  have hfib : ∀ σ : F →+* ℂ, c σ = c (InfinitePlace.mk σ).embedding := by
    intro σ
    have h1 : InfinitePlace.mk σ = InfinitePlace.mk (InfinitePlace.mk σ).embedding := by
      rw [InfinitePlace.mk_embedding]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · rw [← h]
    · rw [← h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := RingHom.ext fun r => rfl
      rw [this, hc]
  set g : InfinitePlace F → ℝ := fun w => c w.embedding with hg
  have hsum : ∑ w : InfinitePlace F, (w.mult : ℝ) * g w = 0 := by
    rw [← hs, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hf : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), c φ = g w := by
      intro φ hφ
      rw [hfib φ, (Finset.mem_filter.mp hφ).2]
    rw [Finset.sum_congr rfl hf, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  let B := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let v : logSpace F := fun w => (w.1.mult : ℝ) * g w.1 / 2
  let r : Fin (rank F) → ℝ := fun i => B.repr v i
  have hB : ∀ i, (B i : logSpace F) = logEmbedding F (Additive.ofMul (fundSystem F i)) := by
    intro i
    rw [Module.Basis.ofZLatticeBasis_apply, logEmbedding_fundSystem]
  have hv : v = ∑ i, r i • B i := (B.sum_repr v).symm
  set h : InfinitePlace F → ℝ := fun w =>
    g w - ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) with hh
  have hne : ∀ w (hw : w ≠ w₀), h w = 0 := by
    intro w hw
    have hvw := congrFun hv ⟨w, hw⟩
    simp only [v, Finset.sum_apply, Pi.smul_apply, hB, logEmbedding_component, smul_eq_mul] at hvw
    have hvw' : (w.mult : ℝ) * g w / 2 =
        ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F))) := hvw
    have hm : (0 : ℝ) < w.mult := by exact_mod_cast InfinitePlace.mult_pos
    have hS : (w.mult : ℝ) * ∑ i, r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F))) =
        2 * ∑ i, r i * ((w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have : (w.mult : ℝ) * h w = 0 := by
      simp only [hh]
      rw [mul_sub, hS, ← hvw']
      ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hm.ne'
    · exact h0
  have htot : ∑ w : InfinitePlace F, (w.mult : ℝ) * h w = 0 := by
    have hi : ∀ i, ∑ w : InfinitePlace F,
        (w.mult : ℝ) * (r i * (2 * Real.log (w ((fundSystem F i : 𝓞 F) : F)))) = 0 := by
      intro i
      have h0 := sum_mult_mul_log (fundSystem F i)
      calc _ = r i * 2 * ∑ w : InfinitePlace F,
            (w.mult : ℝ) * Real.log (w ((fundSystem F i : 𝓞 F) : F)) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
        _ = 0 := by rw [h0, mul_zero]
    simp only [hh, mul_sub, Finset.sum_sub_distrib, hsum, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_zero fun i _ => hi i, sub_zero]
  have hall : ∀ w, h w = 0 := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      rw [Finset.sum_eq_single w₀ (fun b _ hb => by rw [hne b hb, mul_zero])
        (fun h' => absurd (Finset.mem_univ _) h')] at htot
      have hm : (0 : ℝ) < (w₀ : InfinitePlace F).mult := by exact_mod_cast InfinitePlace.mult_pos
      rcases mul_eq_zero.mp htot with h0 | h0
      · exact absurd h0 hm.ne'
      · exact h0
    · exact hne w hw
  refine ⟨rank F, fundSystem F, r, fun σ => ?_⟩
  have e1 := hall (InfinitePlace.mk σ)
  simp only [hh, sub_eq_zero] at e1
  rw [hfib σ]
  refine e1.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [InfinitePlace.apply, Real.log_pow]
  push_cast
  ring

end GlobalTheory
