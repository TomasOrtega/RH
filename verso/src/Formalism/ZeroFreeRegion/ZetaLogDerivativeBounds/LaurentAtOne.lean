import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

def laHfun (y : ℝ) (s : ℂ) : ℂ :=
  (1 - (s - 1) * (deriv riemannZeta₁ s / riemannZeta₁ s)) * ((y : ℂ) ^ s / s)

def laU : Set ℂ := {s | riemannZeta₁ s ≠ 0} ∩ {s | s ≠ 0}

/- English proof (authored)
Regularized zeta is continuous, so its nonzero set is open. Intersect that set with the open set of nonzero arguments.
-/
theorem laU_open : IsOpen laU :=
  (isOpen_ne_fun differentiable_riemannZeta₁.continuous continuous_const).inter isOpen_ne

/- English proof (authored)
At one the regularized zeta value is one, and the argument one is nonzero. Both conditions for membership hold.
-/
theorem one_mem_laU : (1 : ℂ) ∈ laU := by simp [laU]

/- English proof (authored)
On the given open set the regularized zeta function and the argument are nonzero. Hence the quotient of its derivative by itself and the quotient of the power of y by the argument are holomorphic. The defining products and difference preserve holomorphy.
-/
theorem laH_diffOn (y : ℝ) (hy : 0 < y) : DifferentiableOn ℂ (laHfun y) laU := by
  intro s hs
  have hZ : riemannZeta₁ s ≠ 0 := hs.1
  have h0 : s ≠ 0 := hs.2
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply DifferentiableAt.differentiableWithinAt
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s := differentiable_riemannZeta₁.deriv s
  have hz : DifferentiableAt ℂ riemannZeta₁ s := differentiable_riemannZeta₁ s
  have hc : DifferentiableAt ℂ (fun s : ℂ => (y : ℂ) ^ s) s :=
    differentiableAt_id.const_cpow (Or.inl hy0)
  exact ((differentiableAt_const _).sub ((differentiableAt_id.sub_const 1).mul
    (hd.div hz hZ))).mul (hc.div differentiableAt_id h0)

/- English proof (authored)
At one the factor containing s − 1 vanishes, leaving one in the first bracket. The remaining quotient is y to the first power divided by one.
-/
theorem laH_one (y : ℝ) : laHfun y 1 = y := by simp [laHfun]

/- English proof (authored)
Differentiate the product of the first bracket and the power of y divided by s. At one the derivative of the first bracket is minus the logarithmic derivative of regularized zeta, which is minus the Euler–Mascheroni constant. The derivative of the second factor at one is y log y − y. The two product-rule contributions give the formula.
-/
theorem laH_deriv_one (y : ℝ) (hy : 0 < y) :
    deriv (laHfun y) 1 = (y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y := by
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hB : DifferentiableAt ℂ (fun s => deriv riemannZeta₁ s / riemannZeta₁ s) 1 :=
    (differentiable_riemannZeta₁.deriv 1).div (differentiable_riemannZeta₁ 1) (by simp)
  have hk := (((hasDerivAt_id' (1 : ℂ)).sub_const 1).mul hB.hasDerivAt).const_sub 1
  have hc : HasDerivAt (fun s : ℂ => (y : ℂ) ^ s) ((y : ℂ) ^ (1 : ℂ) * Complex.log y) 1 := by
    simpa using (hasStrictDerivAt_const_cpow (x := (y : ℂ)) (y := 1) (Or.inl hy0)).hasDerivAt
  have hg := hc.div (hasDerivAt_id' (1 : ℂ)) one_ne_zero
  have hh := hk.mul hg
  have hh' : HasDerivAt (laHfun y) _ 1 := hh
  rw [hh'.deriv]
  rw [← Complex.ofReal_log hy.le]
  simp
  ring

/- English proof (authored)
Near one, write the Perron integrand as the holomorphic numerator divided by (s − 1)², using the regularized logarithmic derivative identity. The numerator has value y and derivative equal to the stated coefficient at one. Two successive divided differences give a holomorphic remainder after subtracting the constant and linear terms of the numerator. Dividing by (s − 1)² gives the two Laurent terms and that remainder.
-/
theorem laurentExpansionAtOne : LaurentAtOne := by
  intro y hy
  set h := laHfun y with hdef
  have hn : laU ∈ 𝓝 (1 : ℂ) := laU_open.mem_nhds one_mem_laU
  refine ⟨dslope (dslope h 1) 1, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (dslope (dslope h 1) 1) laU :=
      (differentiableOn_dslope hn).2 ((differentiableOn_dslope hn).2 (laH_diffOn y hy))
    exact h1.differentiableAt hn
  · have hU : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ laU := nhdsWithin_le_nhds hn
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, hU, self_mem_nhdsWithin]
      with w hw hwU hw1
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
    have hw0 : w ≠ 0 := hwU.2
    have e1 := sub_smul_dslope h 1 w
    have e2 := sub_smul_dslope (dslope h 1) 1 w
    rw [dslope_same] at e2
    simp only [smul_eq_mul] at e1 e2
    rw [hdef, laH_deriv_one y hy] at e2
    rw [hdef, laH_one y] at e1
    have hhw : laHfun y w =
        (1 - (w - 1) * (deriv riemannZeta₁ w / riemannZeta₁ w)) * ((y : ℂ) ^ w / w) := rfl
    unfold Fy
    rw [hw]
    rw [hdef] at *
    generalize deriv riemannZeta₁ w / riemannZeta₁ w = B at hhw ⊢
    generalize (y : ℂ) ^ w = P at hhw ⊢
    generalize dslope (dslope (laHfun y) 1) 1 w = q at e2 ⊢
    generalize dslope (laHfun y) 1 w = D at e1 e2
    generalize laHfun y w = H at e1 hhw
    have key : (1 - (w - 1) * B) * (P / w) =
        y + (w - 1) * (((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)
          + (w - 1) * q) := by
      rw [← hhw]; linear_combination -e1 - (w - 1) * e2
    have lhs : -(-(w - 1)⁻¹ + B) * P / (w * (w - 1)) =
        (1 - (w - 1) * B) * (P / w) / (w - 1) ^ 2 := by
      field_simp
      ring
    rw [lhs, key]
    field_simp
    ring

end Formalism.ZF
