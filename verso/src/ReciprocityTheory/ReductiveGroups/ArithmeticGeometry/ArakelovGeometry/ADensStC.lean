import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStA

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
open scoped ComplexOrder

section Poly

variable {J : Type} [Fintype J]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]`. Conclude with `hasFDerivAt_const a z`. Consider the case `add p q hp hq`.

Simplify using `only [map_add, add_smul, Finset.sum_add_distrib]`. Conclude with `hp.add hq`. Consider the case `mul_X p n hp => classical`. Establish `h` using `hp.mul (hasFDerivAt_apply n z)`. Establish `hf : (fun w : J → ℂ => eval w (p * X n)) = fun w => eval w p * w n`.

Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules. Rewrite using `[hf]`. Use `h.congr_fderiv ?_` and prove the remaining obligations. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations.

Establish `h1 : ∀ x, eval z (pderiv x (X n : MvPolynomial J ℂ)) = if x = n then 1 else 0`. Introduce `x`. Rewrite using `[pderiv_X]`. Distinguish the cases in `hx : x = n`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hx]`. Establish `h2 : ∀ x, eval z (pderiv x (p * X n)) = eval z p * (if x = n then 1 else 0) + z n * eval z (pderiv x p)`. Introduce `x`. Rewrite using `[Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, h1, eval_X]`.

Establish `h3 : ∑ x, eval z (pderiv x (p * X n)) * v x = eval z p * v n + z n * ∑ x, eval z (pderiv x p) * v x`. Simplify using `only [h2, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]`. Simplify `h3.symm` using `[Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]`.
-/
theorem adens_hasFDerivAt_eval (F : MvPolynomial J ℂ) (z : J → ℂ) :
    HasFDerivAt (fun w => eval w F)
      (∑ i, eval z (pderiv i F) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J => ℂ) i) z := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a z
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p n hp =>
    classical
    have h := hp.mul (hasFDerivAt_apply n z)
    have hf : (fun w : J → ℂ => eval w (p * X n)) = fun w => eval w p * w n := by
      funext w
      simp
    rw [hf]
    refine h.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 : ∀ x, eval z (pderiv x (X n : MvPolynomial J ℂ)) = if x = n then 1 else 0 := by
      intro x
      rw [pderiv_X]
      by_cases hx : x = n
      · subst hx
        simp
      · simp [hx]
    have h2 : ∀ x, eval z (pderiv x (p * X n)) =
        eval z p * (if x = n then 1 else 0) + z n * eval z (pderiv x p) := by
      intro x
      rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, h1, eval_X]
    have h3 : ∑ x, eval z (pderiv x (p * X n)) * v x =
        eval z p * v n + z n * ∑ x, eval z (pderiv x p) * v x := by
      simp only [h2, add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc]
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using h3.symm

end Poly

variable {J : Type} [Fintype J] {D : ℕ}

/- English proof (translation)
Introduce `f hf`. Use `set F := map (Int.castRingHom ℂ) f`. Establish `hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ)` using `by filter_upwards [hU.mem_nhds hy] with w hw`. Conclude with `(hpts w hw).2 f hf`. Establish `hd` using `(adens_hasFDerivAt_eval F (γ y)).comp y (hγ y hy).differentiableAt.hasFDerivAt`.

Establish `h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin D → ℂ) →L[ℂ] ℂ) y` using `(hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero`. Use `congrArg (fun L => L ξ) (hd.unique h0)` as an intermediate fact. Simplify `this` using `[ContinuousLinearMap.sum_apply, smul_eq_mul]`.
-/
theorem adens_isConeTangent {P : Ideal (MvPolynomial J ℤ)} {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hU : IsOpen U) (hγ : AnalyticOnNhd ℂ γ U)
    (hpts : ∀ y ∈ U, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ U) (ξ : Fin D → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hU.mem_nhds hy] with w hw
    exact (hpts w hw).2 f hf
  have hd := (adens_hasFDerivAt_eval F (γ y)).comp y (hγ y hy).differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin D → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

/- English proof (translation)
Establish `hρ : ContDiffAt ℝ 2 m.ρ z` using `(hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)`. Conclude with `hρ.log (m.pos _ hne).ne'`.
-/
theorem adens_contDiffAt_logρ_id {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {z : J → ℂ}
    (hne : z ≠ 0) : ContDiffAt ℝ 2 (fun w => Real.log (m.ρ w)) z := by
  have hρ : ContDiffAt ℝ 2 m.ρ z :=
    (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
  exact hρ.log (m.pos _ hne).ne'

/- English proof (translation)
Establish `hne : γ y ≠ 0` using `(hpts y hy).1`. Establish `h2` using `adens_contDiffAt_logρ hsp.1 (hγ y hy) hne`. Rewrite using `[adens_maDensity_eq_maDens]`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_` and prove the remaining obligations. Use `ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_` and prove the remaining obligations.

Establish `hl` using `ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (m.ρ z)) ξ (hγ y hy) (adens_contDiffAt_logρ_id hsp.1 hne)`. Express the relevant statement in the definitionally equal form `0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (m.ρ z)) ∘ γ) y ξ`. Rewrite using `[hl]`. Conclude with `hsp.2 _ (hpts y hy) hne _ (adens_isConeTangent hV hγ hpts hy ξ)`.
-/
theorem adens_maDensity_nonneg_of {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {V : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (hV : IsOpen V) (hγ : AnalyticOnNhd ℂ γ V)
    (hpts : ∀ y ∈ V, γ y ∈ pts P) {y : Fin D → ℂ} (hy : y ∈ V) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hne : γ y ≠ 0 := (hpts y hy).1
  have h2 := adens_contDiffAt_logρ hsp.1 (hγ y hy) hne
  rw [adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (m.ρ z)) ξ (hγ y hy)
    (adens_contDiffAt_logρ_id hsp.1 hne)
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (m.ρ z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ (hpts y hy) hne _ (adens_isConeTangent hV hγ hpts hy ξ)

/- English proof (translation)
Take `⟨s, hs, hsγ⟩` from `hγ.exists_mem`. Take `⟨V, hVs, hV, hyV⟩` from `mem_nhds_iff.1 hs`. Conclude with `adens_maDensity_nonneg_of hsp hV (fun w hw => (hsγ w (hVs hw)).1) (fun w hw => (hsγ w (hVs hw)).2) hyV`.
-/
theorem adens_maDensity_nonneg_loc {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {γ : (Fin D → ℂ) → J → ℂ}
    {y : Fin D → ℂ} (hγ : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ γ y' ∧ γ y' ∈ pts P) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  obtain ⟨s, hs, hsγ⟩ := hγ.exists_mem
  obtain ⟨V, hVs, hV, hyV⟩ := mem_nhds_iff.1 hs
  exact adens_maDensity_nonneg_of hsp hV (fun w hw => (hsγ w (hVs hw)).1)
    (fun w hw => (hsγ w (hVs hw)).2) hyV

/- English proof (translation)
The claim follows from `adens_maDensity_nonneg_of hsp h.1 h.2.1 h.2.2.1 hy`.
-/
theorem adens_maDensity_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} (h : IsParam P U γ) {y : Fin D → ℂ} (hy : y ∈ U) :
    0 ≤ maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y :=
  adens_maDensity_nonneg_of hsp h.1 h.2.1 h.2.2.1 hy

/- English proof (translation)
Establish `hH : ∀ k, ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z) V` using `fun k => ((h k).fderiv_of_isOpen hV (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl`. Establish `hap : ∀ k (v w : Fin D → ℂ), ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z v w) V` using `fun k v w => ((hH k).clm_apply continuousOn_const).clm_apply continuousOn_const`. Establish `hE : ∀ k i j, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z i j) V`. Introduce `k i j`. Unfold `ReciprocityTheory.AnForm.hessC`.

Simplify using `only []`. Use `ContinuousOn.div_const ?_ _` and prove the remaining obligations. Use `ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn ((hap _ _ _).add (hap _ _ _))) (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ((hap _ _ _).sub (hap _ _ _))))` and prove the remaining obligations. Establish `hM : ∀ k, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z) V` using `fun k => continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hE k i j`. Unfold `ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc`.

Use `continuousOn_const.mul (Complex.continuous_re.comp_continuousOn (continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)))` and prove the remaining obligations. Conclude with `(continuous_id.matrix_det).comp_continuousOn (continuousOn_finsetSum _ fun k _ => hM k)`.
-/
theorem adens_continuousOn_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) {V : Set (Fin D → ℂ)}
    (hV : IsOpen V) (h : ∀ k, ContDiffOn ℝ 2 (φ k) V) :
    ContinuousOn (ReciprocityTheory.AnForm.maDens φ) V := by
  have hH : ∀ k, ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z) V := fun k =>
    ((h k).fderiv_of_isOpen hV (by norm_num)).continuousOn_fderiv_of_isOpen hV le_rfl
  have hap : ∀ k (v w : Fin D → ℂ), ContinuousOn (fun z => fderiv ℝ (fderiv ℝ (φ k)) z v w) V :=
    fun k v w => ((hH k).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hE : ∀ k i j, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z i j) V := by
    intro k i j
    unfold ReciprocityTheory.AnForm.hessC
    simp only []
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.add (Complex.continuous_ofReal.comp_continuousOn ((hap _ _ _).add (hap _ _ _)))
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
        ((hap _ _ _).sub (hap _ _ _))))
  have hM : ∀ k, ContinuousOn (fun z => ReciprocityTheory.AnForm.hessC (φ k) z) V := fun k =>
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hE k i j
  unfold ReciprocityTheory.AnForm.maDens ReciprocityTheory.AnForm.mdisc
  refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
    (continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)))
  exact (continuous_id.matrix_det).comp_continuousOn
    (continuousOn_finsetSum _ fun k _ => hM k)

def adensF (m : ConeMetric ℂ J) (γ : (Fin D → ℂ) → J → ℂ) (ν : (Fin D → ℂ) → ℝ)
    (y : Fin D → ℂ) : ℝ :=
  maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y / ((D.factorial : ℝ) * ν y)

/- English proof (translation)
Establish `hτ : q' (γ y) ∈ U'` using `(adens_trans_fac h.2.2.1 hOP' hsc' hqγ' hy hyO).1`. Establish `e1` using `adens_density_compare h hν h'.1 h'.2.1 hν' hO' hq' hOP' hsc' hqγ' hy hyO`. Establish `e2` using `adens_maDensity_compare hsm h h'.2.1 hO' hq' hOP' hsc' hqγ' hy hyO`. Establish `hpos : 0 < ν' (q' (γ y))` using `hν'.2.1 _ hτ`. Establish `hD : (0 : ℝ) < D.factorial` using `by exact_mod_cast Nat.factorial_pos D`.

Rewrite using `[e1, e2]`. Unfold `adensF`. Clear the denominators using the available nonvanishing facts.
-/
theorem adensF_compat {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    {ν ν' : (Fin D → ℂ) → ℝ} (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν)
    (h' : IsParam P U' γ') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    adensF m γ' ν' (q' (γ y)) * ((D.factorial : ℝ) * ν y) =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y := by
  have hτ : q' (γ y) ∈ U' := (adens_trans_fac h.2.2.1 hOP' hsc' hqγ' hy hyO).1
  have e1 := adens_density_compare h hν h'.1 h'.2.1 hν' hO' hq' hOP' hsc' hqγ' hy hyO
  have e2 := adens_maDensity_compare hsm h h'.2.1 hO' hq' hOP' hsc' hqγ' hy hyO
  have hpos : 0 < ν' (q' (γ y)) := hν'.2.1 _ hτ
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  rw [e1, e2]
  unfold adensF
  field_simp

/- English proof (translation)
Unfold `adensF`. Establish `hD : (0 : ℝ) < D.factorial` using `by exact_mod_cast Nat.factorial_pos D`. Conclude with `div_nonneg (adens_maDensity_nonneg hsp h hy) (mul_pos hD (hν.2.1 y hy)).le`.
-/
theorem adensF_nonneg {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)}
    (hsp : IsSemipositiveOn m (Int.castRingHom ℂ) P (pts P)) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) {y : Fin D → ℂ} (hy : y ∈ U) : 0 ≤ adensF m γ ν y := by
  unfold adensF
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  exact div_nonneg (adens_maDensity_nonneg hsp h hy) (mul_pos hD (hν.2.1 y hy)).le

/- English proof (translation)
Take `⟨hU, hγ, hpts, -⟩` from `h`. Establish `hD : (0 : ℝ) < D.factorial` using `by exact_mod_cast Nat.factorial_pos D`. Establish `hMA : ContinuousOn (maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w)))) U`. Use `adens_continuousOn_maDens _ hU fun _ => ?_` and prove the remaining obligations. Introduce `y hy`.

Conclude with `(adens_contDiffAt_logρ hsm (hγ y hy) (hpts y hy).1).contDiffWithinAt`. Conclude with `hMA.div (continuousOn_const.mul hν.1.continuousOn) fun y hy => (mul_pos hD (hν.2.1 y hy)).ne'`.
-/
theorem adensF_continuousOn {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    {μ : Measure (J → ℂ)} (hsm : IsSmoothMetric m) {U : Set (Fin D → ℂ)}
    {γ : (Fin D → ℂ) → J → ℂ} {ν : (Fin D → ℂ) → ℝ} (h : IsParam P U γ)
    (hν : IsDensityFor μ U γ ν) : ContinuousOn (adensF m γ ν) U := by
  obtain ⟨hU, hγ, hpts, -⟩ := h
  have hD : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  have hMA : ContinuousOn (maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w)))) U := by
    refine adens_continuousOn_maDens _ hU fun _ => ?_
    intro y hy
    exact (adens_contDiffAt_logρ hsm (hγ y hy) (hpts y hy).1).contDiffWithinAt
  exact hMA.div (continuousOn_const.mul hν.1.continuousOn) fun y hy =>
    (mul_pos hD (hν.2.1 y hy)).ne'

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
