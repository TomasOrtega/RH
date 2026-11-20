import Formalism.LocalToGlobal.IndefiniteReal.PHeisThP

noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Filter Topology
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

A detailed English derivation is pending.
-/
theorem eq_one_of_re_pow_gt (u : ℂ) (hu : ‖u‖ = 1) (h : ∀ n : ℕ, 1 / 2 < (u ^ n).re) : u = 1 := by
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖u - 1‖)
  have h1 : ‖u ^ N - 1‖ ≤ 2 := by
    calc ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hu]; norm_num
  have h2 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ _i ∈ Finset.range N, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => (h i).le
  have h3 : (N : ℝ) / 2 * ‖u - 1‖ ≤ 2 := by
    calc (N : ℝ) / 2 * ‖u - 1‖ ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = ‖u ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ 2 := h1
  have h4 : 4 / ‖u - 1‖ * ‖u - 1‖ = 4 := div_mul_cancel₀ _ hpos.ne'
  nlinarith [mul_lt_mul_of_pos_right hN hpos]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Replace the relevant objects with their definitions.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem psiOpen : PsiOpenP := by
  intro F _ _ ψ hψ
  obtain ⟨hcont, hnorm, -, -⟩ := hψ
  let g : Af F → ℂ := fun y => ψ (pairA F 0 y)
  have hp : Continuous (pairA F 0) := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  have hg : Continuous g := hcont.comp hp
  have gzero : g 0 = 1 := by
    show ψ (pairA F 0 0) = 1
    have e : pairA F 0 0 = 0 := rfl
    rw [e, AddChar.map_zero_eq_one]
  have gadd : ∀ a b, g (a + b) = g a * g b := by
    intro a b
    show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairA
    show ((0 : Ainf F), a + b) = ((0 + 0 : Ainf F), a + b)
    rw [add_zero]
  have gnsmul : ∀ (n : ℕ) a, g (n • a) = g a ^ n := by
    intro n a
    induction n with
    | zero => simp [gzero]
    | succ n ih => rw [succ_nsmul, gadd, ih, pow_succ]
  let G : AddSubgroup (Af F) :=
    { carrier := {y | ∀ z ∈ Ohat F, g (z * y) = 1}
      zero_mem' := by
        intro z _
        rw [mul_zero]; exact gzero
      add_mem' := by
        intro a b ha hb z hz
        rw [mul_add, gadd, ha z hz, hb z hz, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := gadd (z * -a) (z * a)
        rw [← mul_add, neg_add_cancel, mul_zero, gzero, ha z hz, mul_one] at h1
        exact h1.symm }
  refine ⟨G, ?_, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    have key : ∀ᶠ d in 𝓝 (0 : Af F), ∀ z ∈ Ohat F, 1 / 2 < (g (z * d)).re := by
      refine (isCompact_Ohat F).eventually_forall_of_forall_eventually fun z _ => ?_
      have hc : Continuous fun p : Af F × Af F => (g (p.2 * p.1)).re :=
        Complex.continuous_re.comp (hg.comp (continuous_snd.mul continuous_fst))
      have h0 : 1 / 2 < (g (z * 0)).re := by rw [mul_zero, gzero]; norm_num
      exact (isOpen_lt continuous_const hc).mem_nhds h0
    refine Filter.mem_of_superset key fun d hd z hz => ?_
    apply eq_one_of_re_pow_gt _ (hnorm _)
    intro n
    have hnz : n • z ∈ Ohat F :=
      SetLike.mem_coe.mpr (nsmul_mem (SetLike.mem_coe.mp hz) n)
    have := hd _ hnz
    rwa [smul_mul_assoc, gnsmul] at this
  · intro y hy z hz w hw
    show g (w * (z * y)) = 1
    rw [← mul_assoc]
    exact hy _ (SetLike.mem_coe.mpr (mul_mem (SetLike.mem_coe.mp hw) (SetLike.mem_coe.mp hz)))
  · intro y hy
    have := hy 1 (SetLike.mem_coe.mpr (one_mem _))
    rwa [one_mul] at this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem psiSmooth : PsiSmoothP := by
  intro D ψ hψ k s hs
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := hψ
  have h := hall θ hθ
  have hc : ∀ ρ, ContDiff ℝ ∞ fun t : Fin k → ℝ => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro ρ
    let L : (Fin k → ℝ) →+ ℂ :=
      { toFun := fun t => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))
        map_zero' := by simp
        map_add' := fun a b => by simp [map_add, TensorProduct.add_tmul] }
    have hL : Continuous L := (hθ ρ).2.comp hs
    exact (L.toRealLinearMap hL).contDiff
  have e : (fun t => ψ (pairA D.host.F (s t) 0)) = fun t =>
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
        ∑ ρ, θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    funext t; exact h (s t)
  rw [e]
  exact (contDiff_const.mul (ContDiff.sum fun ρ _ => hc ρ)).cexp

end Formalism.IndefR.PHeisTh

end
