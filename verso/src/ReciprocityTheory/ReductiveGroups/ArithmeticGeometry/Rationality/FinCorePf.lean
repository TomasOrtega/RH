import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.UnitPointLiftBall

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

/- English proof (translation)
Unfold `FinCoreStatement`. Introduce `K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv`. Establish `step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 → ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0)`. Introduce `x hx hxδ`. Establish `hd` using `disc_holds`.

Unfold `DiscStatement at hd`. Use `hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_` and prove the remaining obligations. Introduce `n hn show MvPolynomial.eval x (P n) = 0`. Rewrite using `[hPb n hn, map_zero]`. Introduce `t ht`.

Use `⟨(hconv t ht x hx hxδ).1, ?_⟩` and prove the remaining obligations. Introduce `τ hτ hτ1`. Conclude with `(hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2`. Establish `key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧ ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖MvPolynomial.coeff μ p‖ ∧ MvPolynomial.coeff μ p ≠ 0 ∧ ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖`. Introduce `p hp`.

Establish `hne : p.support.Nonempty`. Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h`. Conclude with `hp (MvPolynomial.support_eq_empty.mp h)`. Take `⟨μ, hμ, hmax⟩` from `Finset.exists_max_image p.support (fun ν => ‖MvPolynomial.coeff ν p‖) hne`.

Establish `hc : MvPolynomial.coeff μ p ≠ 0` using `MvPolynomial.mem_support_iff.mp hμ`. Establish `hmax' : ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖`. Introduce `ν`. Distinguish the cases in `hν : ν ∈ p.support`. Conclude with `hmax ν hν`.

Establish `h0 : MvPolynomial.coeff ν p = 0`. Simplify `hν` using `[MvPolynomial.mem_support_iff]`. Rewrite using `[h0, norm_zero]`. Conclude with `norm_nonneg _`. Establish `hcpos : 0 < ‖MvPolynomial.coeff μ p‖` using `norm_pos_iff.mpr hc`.

Establish `hQ : ∀ ν, ‖MvPolynomial.coeff ν (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ ≤ 1`. Introduce `ν`. Rewrite using `[MvPolynomial.coeff_C_mul, norm_mul, norm_inv]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hmax' ν`.

Use `_ = 1 := inv_mul_cancel₀ hcpos.ne'`. Establish `hQ1 : ∃ ν, ‖MvPolynomial.coeff ν (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ = 1`. Use `⟨μ, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]`. Take `⟨x, hx, hxQ, hxδ⟩` from `UnitPointLiftBall.exists_unit_point K₀ hK₀ (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p) δ hQ hQ1 hδ hδ1`.

Use `⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩` and prove the remaining obligations. Establish `he : MvPolynomial.eval x p = MvPolynomial.coeff μ p * MvPolynomial.eval x (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)`. Rewrite using `[MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]`. Rewrite using `[he, norm_mul, hxQ, mul_one]`. Introduce `n`.

Prove the components needed by the constructor for the conclusion. Introduce `μ`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hp : P n ≠ 0`.

Introduce `h`. Rewrite `hlt` using `[h, MvPolynomial.coeff_zero, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨x, hx, hxδ, ν, hev, -, hmax⟩` from `key (P n) hp`. Establish `h1` using `(step1 x hx hxδ n).1`.

Rewrite `h1` using `[hev]`. Combine the linear relations using `[hmax μ]`. Introduce `hn`. Assume the negation of the conclusion as `hp`. Take `⟨x, hx, hxδ, ν, hev, hc, -⟩` from `key (P n) hp`.

Establish `h0` using `(step1 x hx hxδ n).2 hn`. Rewrite `hev` using `[h0, norm_zero]`. Conclude with `hc (norm_eq_zero.mp hev.symm)`.
-/
theorem finCore_holds : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖MvPolynomial.coeff μ p‖ ∧
        MvPolynomial.coeff μ p ≠ 0 ∧ ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖MvPolynomial.coeff ν p‖) hne
    have hc : MvPolynomial.coeff μ p ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖MvPolynomial.coeff ν p‖ ≤ ‖MvPolynomial.coeff μ p‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : MvPolynomial.coeff ν p = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖MvPolynomial.coeff μ p‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖MvPolynomial.coeff ν
        (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖MvPolynomial.coeff μ p‖⁻¹ * ‖MvPolynomial.coeff ν p‖
          ≤ ‖MvPolynomial.coeff μ p‖⁻¹ * ‖MvPolynomial.coeff μ p‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖MvPolynomial.coeff ν
        (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p)‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = MvPolynomial.coeff μ p *
        MvPolynomial.eval x (MvPolynomial.C (MvPolynomial.coeff μ p)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push_neg at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, MvPolynomial.coeff_zero, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
