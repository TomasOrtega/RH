import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.IntOfIntegers
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CoefAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsF

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

/- English proof (translation)
Simplify using `[reAt]`.
-/
private theorem reAt_rat (v : InfinitePlace ℚ) (q : ℚ) : reAt v q = (q : ℝ) := by
  simp [reAt]

/- English proof (translation)
Use `haveI : NeZero M := ⟨by omega⟩`. Establish `hp : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods` using `by simp`. Establish `h` using `hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp) f.holo' (ModularFormClass.bdd_at_infty f) τ`. Establish `h0 : (qExpansion 1 f).coeff 0 = 0` using `CuspFormClass.qExpansion_coeff_zero f one_pos hp`. Rewrite `h` using `[← hasSum_nat_add_iff' 1]`.

Simplify using `only [Finset.range_one, Finset.sum_singleton, h0, zero_smul, sub_zero] at h`. Use `cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h` and prove the remaining obligations. Rewrite using `[smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]`. Use `congr 2`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_f {k M : ℕ} (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) * (τ : ℂ)))) (f τ) := by
  haveI : NeZero M := ⟨by omega⟩
  have hp : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  have h0 : (qExpansion 1 f).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos hp
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, h0, zero_smul, sub_zero] at h
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

/- English proof (translation)
Establish `hd : (aff y x : GL (Fin 2) ℝ).val.det = y` using `by simp [aff, Matrix.det_fin_two]`. Rewrite using `[nsl, hd, abs_of_pos hy, sign_pos hy]`. Simplify using `[aff, add_comm, mul_comm]`.
-/
private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (y : ℝˣ) (hy : 0 < (y : ℝ)) (x : ℝ) :
    nsl k f (aff y x : GL (Fin 2) ℝ) UpperHalfPlane.I =
      (((y : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f (ofComplex ((x : ℂ) + Complex.I * (y : ℝ))) := by
  have hd : (aff y x : GL (Fin 2) ℝ).val.det = y := by simp [aff, Matrix.det_fin_two]
  rw [nsl, hd, abs_of_pos hy, sign_pos hy]
  simp [aff, add_comm, mul_comm]

/- English proof (translation)
Establish `hr : ((r : ℚ) : ℝ) ≠ 0` using `by exact_mod_cast r.ne_zero`. Rewrite using `[ratGL_eq, mul_assoc, ← mul_assoc (finGL ℚ 2 _), ← upR_comm, mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← upR_ev]`. Use `congr 2`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [aff, toR, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp`. Apply the tactic sequence `ext i j : 2 fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
private theorem pt_eq (x : TR.Rinf ℚ) (y : (TR.Rinf ℚ)ˣ) (r : ℚˣ) (u : (Af ℚ)ˣ) :
    TR.infGL ℚ 2 (aff y x) * finGL ℚ 2 (aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u) 0) =
      ratGL ℚ 2 (aff r 0) * (upR (aff (Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹)
        (ev x / (r : ℚ))) * finGL ℚ 2 (aff u 0)) := by
  have hr : ((r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast r.ne_zero
  rw [ratGL_eq, mul_assoc, ← mul_assoc (finGL ℚ 2 _), ← upR_comm, mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← upR_ev]
  congr 2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toR, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_succ]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
/- English proof (translation)
Introduce `k M hM f φ hφ x y hy yf`. Take `⟨r, u, hr, hu, rfl⟩` from `ratAd.1 yf`. Establish `hr' : (0 : ℝ) < ((r : ℚ) : ℝ)` using `by exact_mod_cast hr`. Establish `hrc : (((r : ℚ) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr.ne'`. Establish `hy0 : 0 < ev y.val` using `hy _`.

Establish `hyv : ((Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹ : ℝˣ) : ℝ) = ev y.val * ((r : ℚ) : ℝ)⁻¹`. Simplify using the standard rewrite rules. Establish `hpos : 0 < ev y.val * ((r : ℚ) : ℝ)⁻¹` using `by positivity`. Establish `hprod : ∏ v, y.val v = ev y.val` using `Fintype.prod_subsingleton _ _`. Rewrite using `[pt_eq, hφ _ _ _ ((kOpen M hM).2 u hu 0 (zero_mem _)), nsl_aff _ _ _ (hyv ▸ hpos), UpperTheory.V.Af.Nf.absF r hr u hu, hyv, hprod, mul_div_cancel_left₀ _ (by exact_mod_cast (Real.rpow_pos_of_pos hpos _).ne'), Pi.zero_apply, sub_zero]`.

Establish `him : 0 < (((ev x / (r : ℚ) : ℝ) : ℂ) + Complex.I * ((ev y.val * ((r : ℚ) : ℝ)⁻¹ : ℝ) : ℂ)).im`. Simplify `hpos` using `only [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add]`. Establish `hc : ∀ q : ℚ, 0 < q → UpperTheory.V.Sd.coefAt (icoef f) (algebraMap ℚ (Af ℚ) q * ((Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u : (Af ℚ)ˣ) : Af ℚ)) = if (q * r).den = 1 then coef f (q * r).num.toNat else 0` using `fun q hq => by`. Rewrite using `[← UpperTheory.V.Af.Nf.coefAt (coef f) (q * r) (mul_pos hq hr) u hu, map_mul, mul_assoc]`. Both sides reduce to the same expression.

Set `j : ℕ → {ξ : ℚ // ∀ v, 0 < reAt v ξ}` to `fun n => ⟨((n + 1 : ℕ) : ℚ) / r, fun v => by`. Rewrite using `[reAt_rat]; exact_mod_cast div_pos (by positivity) hr⟩`. Establish `hj : Function.Injective j` using `fun a b h => by`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[j, hr.ne']`.

Establish `hq : ∀ ξ : {ξ : ℚ // ∀ v, 0 < reAt v ξ}, 0 < ξ.1` using `fun ξ => by`. Use `ξ.2 Rat.infinitePlace` as an intermediate fact. Rewrite `this` using `[reAt_rat]`. Conclude with `this` after adjusting the coercions. Rewrite using `[← hj.hasSum_iff fun ξ hξ => ?_]`.

Use `sum_f hM f (ofComplex _) using 2 with n` and compare the differences between its conclusion and the goal. Rewrite using `[ofComplex_apply_of_im_pos him]`. Establish `e : (j n).1 * r = ((n + 1 : ℕ) : ℚ)` using `div_mul_cancel₀ _ hr.ne'`. Simplify using `only [Function.comp]`. Rewrite using `[hc _ (hq _), e, Fintype.sum_subsingleton _ Rat.infinitePlace, reAt_rat]`.

Simplify using `only [Rat.den_natCast, Rat.num_natCast, Int.toNat_natCast, if_true]`. Use `congr 3`. Express the relevant statement in the definitionally equal form `((((((n + 1 : ℕ) : ℚ) / r : ℚ) : ℝ)) : ℂ) * ((ev x : ℂ) + Complex.I * (ev y.val : ℂ)) = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hc _ (hq ξ), if_neg, zero_mul]`. Introduce `hd`. Establish `h1 : 0 < (ξ.1 * r).num` using `Rat.num_pos.2 (mul_pos (hq ξ) hr)`. Use `hξ ⟨(ξ.1 * r).num.toNat - 1, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `h2 : (((ξ.1 * r).num.toNat - 1 + 1 : ℕ) : ℤ) = (ξ.1 * r).num` using `by omega`.

Express the relevant statement in the definitionally equal form `((_ : ℕ) : ℚ) / r = _`. Rewrite using `[← Int.cast_natCast, h2, Rat.coe_int_num_of_den_eq_one hd, mul_div_cancel_right₀ _ hr.ne']`.
-/
theorem UpperTheory.V.Af.Nf.liftExp :
    UpperTheory.V.Af.Nf.LiftExp := by
  intro k M hM f φ hφ x y hy yf
  obtain ⟨r, u, hr, hu, rfl⟩ := ratAd.1 yf
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have hrc : (((r : ℚ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hy0 : 0 < ev y.val := hy _
  have hyv : ((Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹ : ℝˣ) : ℝ) = ev y.val * ((r : ℚ) : ℝ)⁻¹ := by
    simp
  have hpos : 0 < ev y.val * ((r : ℚ) : ℝ)⁻¹ := by positivity
  have hprod : ∏ v, y.val v = ev y.val := Fintype.prod_subsingleton _ _
  rw [pt_eq, hφ _ _ _ ((kOpen M hM).2 u hu 0 (zero_mem _)), nsl_aff _ _ _ (hyv ▸ hpos), UpperTheory.V.Af.Nf.absF r hr u hu, hyv, hprod,
    mul_div_cancel_left₀ _ (by exact_mod_cast (Real.rpow_pos_of_pos hpos _).ne'), Pi.zero_apply, sub_zero]
  have him : 0 < (((ev x / (r : ℚ) : ℝ) : ℂ) + Complex.I * ((ev y.val * ((r : ℚ) : ℝ)⁻¹ : ℝ) : ℂ)).im := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add] using hpos
  have hc : ∀ q : ℚ, 0 < q → UpperTheory.V.Sd.coefAt (icoef f) (algebraMap ℚ (Af ℚ) q *
      ((Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u : (Af ℚ)ˣ) : Af ℚ)) =
      if (q * r).den = 1 then coef f (q * r).num.toNat else 0 := fun q hq => by
    rw [← UpperTheory.V.Af.Nf.coefAt (coef f) (q * r) (mul_pos hq hr) u hu, map_mul, mul_assoc]
    rfl
  let j : ℕ → {ξ : ℚ // ∀ v, 0 < reAt v ξ} := fun n => ⟨((n + 1 : ℕ) : ℚ) / r, fun v => by
    rw [reAt_rat]; exact_mod_cast div_pos (by positivity) hr⟩
  have hj : Function.Injective j := fun a b h => by
    have := congrArg Subtype.val h
    simpa [j, hr.ne'] using this
  have hq : ∀ ξ : {ξ : ℚ // ∀ v, 0 < reAt v ξ}, 0 < ξ.1 := fun ξ => by
    have := ξ.2 Rat.infinitePlace
    rw [reAt_rat] at this
    exact_mod_cast this
  rw [← hj.hasSum_iff fun ξ hξ => ?_]
  · convert sum_f hM f (ofComplex _) using 2 with n
    rw [ofComplex_apply_of_im_pos him]
    have e : (j n).1 * r = ((n + 1 : ℕ) : ℚ) := div_mul_cancel₀ _ hr.ne'
    simp only [Function.comp]
    rw [hc _ (hq _), e, Fintype.sum_subsingleton _ Rat.infinitePlace, reAt_rat]
    simp only [Rat.den_natCast, Rat.num_natCast, Int.toNat_natCast, if_true]
    congr 3
    change ((((((n + 1 : ℕ) : ℚ) / r : ℚ) : ℝ)) : ℂ) * ((ev x : ℂ) + Complex.I * (ev y.val : ℂ)) = _
    push_cast
    ring
  · rw [hc _ (hq ξ), if_neg, zero_mul]
    intro hd
    have h1 : 0 < (ξ.1 * r).num := Rat.num_pos.2 (mul_pos (hq ξ) hr)
    refine hξ ⟨(ξ.1 * r).num.toNat - 1, Subtype.ext ?_⟩
    have h2 : (((ξ.1 * r).num.toNat - 1 + 1 : ℕ) : ℤ) = (ξ.1 * r).num := by omega
    change ((_ : ℕ) : ℚ) / r = _
    rw [← Int.cast_natCast, h2, Rat.coe_int_num_of_den_eq_one hd, mul_div_cancel_right₀ _ hr.ne']
