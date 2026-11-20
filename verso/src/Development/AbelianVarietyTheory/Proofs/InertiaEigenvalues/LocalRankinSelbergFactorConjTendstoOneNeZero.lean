import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

namespace GlobalTheory.JSW

/- English proof (translation)
Introduce `q A B hq hA hB`. Use `set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'`. Establish `hq0 : (q : ℂ) ≠ 0` using `by exact_mod_cast (show q ≠ 0 by omega)`. Establish `hqr : (1 : ℝ) < q` using `by exact_mod_cast hq`. Establish `key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0`.

Introduce `p hp`. Rewrite `hp` using `[Multiset.mem_product]`. Take `⟨h1, h2⟩` from `hp`. Rewrite `h2` using `[hB', Multiset.mem_map]`. Take `⟨β, hβ, hpe⟩` from `h2`.

Rewrite using `[← hpe]`. Establish `ha` using `hA _ h1`. Establish `hb` using `hB _ hβ`. Establish `hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖`. Simplify using `[Units.coe_map]`.

Establish `hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q`. Establish `h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖` using `by positivity`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖)` using `mul_le_mul hc hc (by positivity) h0`.

Establish `h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2` using `by ring`. Establish `h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q` using `mul_lt_mul'' ha hb (by positivity) (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h0`. Establish `hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1`.

Take the linear combination `-h0`. Establish `hn` using `congrArg norm hz`. Rewrite `hn` using `[Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one]`. Establish `hqpos : (0 : ℝ) < q` using `by linarith`. Rewrite `hn` using `[mul_inv_eq_one₀ hqpos.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion. Prove the components needed by the constructor for the conclusion. Establish `hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1) (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹))`. Introduce `p hp`. Apply `Tendsto.mono_left _ nhdsWithin_le_nhds` to reduce the goal to its premises.

Apply `ContinuousAt.tendsto` to reduce the goal to its premises. Apply `ContinuousAt.inv₀` to reduce the goal to its premises. Apply `ContinuousAt.sub continuousAt_const` to reduce the goal to its premises. Apply `ContinuousAt.mul continuousAt_const` to reduce the goal to its premises. Apply `ContinuousAt.const_cpow` to reduce the goal to its premises.

Conclude with `(Complex.continuous_ofReal.neg).continuousAt`. Conclude with `Or.inl hq0`. Simplify using `using key p hp`. Use `tendsto_multiset_prod (A ×ˢ B') hc` as an intermediate fact. Simplify `this` using `[locL]`.

Unfold `locL`. Apply `Multiset.prod_ne_zero` to reduce the goal to its premises. Rewrite using `[Multiset.mem_map]`. Introduce and unpack `⟨p, hp, h⟩`. Conclude with `inv_ne_zero (key p hp) h`.
-/
theorem locL_conj_tendsto_one_and_ne_zero : ∀ (q : ℕ) (A B : Multiset ℂˣ), 1 < q → (∀ α ∈ A, ‖(α : ℂ)‖ ^ 2 < (q : ℝ)) →
    (∀ β ∈ B, ‖(β : ℂ)‖ ^ 2 < (q : ℝ)) →
    Tendsto (fun x : ℝ => locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1)
      (𝓝 (locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1)) ∧
    locL q A (B.map (Units.map (starRingEnd ℂ).toMonoidHom)) 1 ≠ 0 := by
  intro q A B hq hA hB
  set B' := B.map (Units.map (starRingEnd ℂ).toMonoidHom) with hB'
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast hq

  have key : ∀ p ∈ A ×ˢ B', (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(1 : ℂ))) ≠ 0 := by
    intro p hp
    rw [Multiset.mem_product] at hp
    obtain ⟨h1, h2⟩ := hp
    rw [hB', Multiset.mem_map] at h2
    obtain ⟨β, hβ, hpe⟩ := h2
    rw [← hpe]
    have ha := hA _ h1
    have hb := hB _ hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ)‖ = ‖(β : ℂ)‖ := by
      simp [Units.coe_map]
    have hprod : ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ < q := by
      have h0 : 0 ≤ ‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖ := by positivity
      by_contra hc
      push_neg at hc
      have : (q : ℝ) * q ≤ (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) :=
        mul_le_mul hc hc (by positivity) h0
      have h3 : (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) * (‖(p.1 : ℂ)‖ * ‖(β : ℂ)‖) = ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 := by ring
      have h4 : ‖(p.1 : ℂ)‖ ^ 2 * ‖(β : ℂ)‖ ^ 2 < (q : ℝ) * q :=
        mul_lt_mul'' ha hb (by positivity) (by positivity)
      linarith
    intro h0
    have hz : (p.1 : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom β : ℂˣ) : ℂ) * (q : ℂ) ^ (-(1 : ℂ)) = 1 := by
      linear_combination -h0
    have hn := congrArg norm hz
    rw [Complex.cpow_neg_one, norm_mul, norm_mul, hnb, norm_inv, Complex.norm_natCast, norm_one] at hn
    have hqpos : (0 : ℝ) < q := by linarith
    rw [mul_inv_eq_one₀ hqpos.ne'] at hn
    linarith
  constructor
  · have hc : ∀ p ∈ A ×ˢ B', Tendsto (fun x : ℝ => (1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-(x : ℂ)))⁻¹) (𝓝[>] 1)
        (𝓝 ((1 - (p.1 : ℂ) * p.2 * (q : ℂ) ^ (-((1 : ℝ) : ℂ)))⁻¹)) := by
      intro p hp
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.inv₀
      · apply ContinuousAt.sub continuousAt_const
        apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.const_cpow
        · exact (Complex.continuous_ofReal.neg).continuousAt
        · exact Or.inl hq0
      · simpa using key p hp
    have := tendsto_multiset_prod (A ×ˢ B') hc
    simpa [locL] using this
  · unfold locL
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨p, hp, h⟩
    exact inv_ne_zero (key p hp) h
end GlobalTheory.JSW
