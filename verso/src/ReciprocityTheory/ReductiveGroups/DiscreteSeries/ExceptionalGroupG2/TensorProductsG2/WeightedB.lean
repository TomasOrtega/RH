import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.WeightedA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `hinv : rreg ε (Formalism.MainNotions.S.umat g) (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) = b`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← (rreg_isURepOn ε).1.2 _ g.2 _ (g⁻¹).2]`. Use `show rreg ε (Formalism.MainNotions.S.umat (g * g⁻¹)) b = b`. Rewrite using `[mul_inv_cancel, show Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 from rfl, (rreg_isURepOn ε).1.1]`. Both sides reduce to the same expression.

Set `Lk : L2 ε →ₗᵢ[ℂ] L2 ε` to `⟨(rreg ε (Formalism.MainNotions.S.umat g)).toLinearMap, fun z => (rreg_isURepOn ε).2.1 _ g.2 z⟩`. Use `conv_lhs => rw [← hinv]`. Conclude with `Lk.inner_map_map a _`.
-/
theorem wd_rreg_adj (g : Formalism.REAL.UJ ε) (a b : L2 ε) :
    inner ℂ (rreg ε (Formalism.MainNotions.S.umat g) a) b = inner ℂ a (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) := by
  have hinv : rreg ε (Formalism.MainNotions.S.umat g) (rreg ε (Formalism.MainNotions.S.umat g⁻¹) b) = b := by
    rw [← ContinuousLinearMap.comp_apply, ← (rreg_isURepOn ε).1.2 _ g.2 _ (g⁻¹).2]
    show rreg ε (Formalism.MainNotions.S.umat (g * g⁻¹)) b = b
    rw [mul_inv_cancel, show Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 from rfl, (rreg_isURepOn ε).1.1]
    rfl
  let Lk : L2 ε →ₗᵢ[ℂ] L2 ε :=
    ⟨(rreg ε (Formalism.MainNotions.S.umat g)).toLinearMap, fun z => (rreg_isURepOn ε).2.1 _ g.2 z⟩
  conv_lhs => rw [← hinv]
  exact Lk.inner_map_map a _

/- English proof (translation)
Rewrite using `[arb_umat_inv, arbSharp_apply]`. Unfold `S7.hs Formalism.REAL.Jm`. Establish `e : ∀ i j, ‖(Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1) * (Formalism.MainNotions.S.umat g)ᴴ * Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1)) i j‖ = ‖Formalism.MainNotions.S.umat g j i‖`. Introduce `i j`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_mul, norm_star]`.

Apply the tactic sequence `have h1 : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp`. Rewrite using `[h1, h1, one_mul, mul_one]`. Simplify using `only [e]`. Conclude with `Finset.sum_comm`.
-/
theorem wd_hs_inv (g : Formalism.REAL.UJ ε) : S7.hs (Formalism.MainNotions.S.umat g⁻¹) = S7.hs (Formalism.MainNotions.S.umat g) := by
  rw [arb_umat_inv, arbSharp_apply]
  unfold S7.hs Formalism.REAL.Jm
  have e : ∀ i j, ‖(Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1) * (Formalism.MainNotions.S.umat g)ᴴ *
      Matrix.diagonal (fun a => if ε a = true then (1 : ℂ) else -1)) i j‖ = ‖Formalism.MainNotions.S.umat g j i‖ := by
    intro i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_mul, norm_star]
    have h1 : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    rw [h1, h1, one_mul, mul_one]
  simp only [e]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[wdF, mul_add]`.
-/
theorem wdF_add (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (f + f') = wdF ε f + wdF ε f' := by
  funext g; simp [wdF, mul_add]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [wdF, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wdF_smul (c : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : wdF ε (c • f) = c • wdF ε f := by
  funext g; simp only [wdF, Pi.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[wdF]`.
-/
theorem wdF_zero : wdF ε (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) = 0 := by
  funext g; simp [wdF]

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

/- English proof (translation)
Establish `hK` using `datumV_isKIrrHW hP hv₀`. Establish `: FiniteDimensional ℂ (datumV ε Ψ v₀)` using `hK.1`. Use `set W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) := (datumV ε Ψ v₀).map (wdCoef ε w) with hWdef`. Establish `hWf : FiniteDimensional ℂ W` using `inferInstance`. Establish `key` using `r0bG n ε W ((casVal lam : ℝ) : ℂ) (1 / 2) hWf (by norm_num) (by rintro f ⟨x, -, rfl⟩; exact wdCoef_smooth w x) (by`.

Introduce and unpack `f ⟨x, hx, rfl⟩ a b hab`. Conclude with `⟨wdCoef ε w (smE ε (rreg ε) a b x), ⟨_, hK.2.1 a b hab x hx, rfl⟩, fun g hg => wdCoef_eab w x a b ((mir_inUJ_iff ε g).1 hg)⟩)`. Use the proof step `(by`. Introduce and unpack `f ⟨x, hx, rfl⟩ g hg`. Establish `hg'` using `(mir_inUJ_iff ε g).1 hg`.

Establish `e1 : ∀ a b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (wdCoef ε w x)) g = wdCoef ε w (smE ε (rreg ε) a b (smE ε (rreg ε) b a x)) g`. Introduce `a b`. Rewrite using `[icx_eab_eq, icx_eabV_congr (fun g' hg'' => wdCoef_eab w x b a hg'') a b hg', ← icx_eab_eq]`. Conclude with `wdCoef_eab w _ a b hg'`. Establish `e2 : wdCoef ε w (casimir (smE ε (rreg ε)) x) g = ∑ a, ∑ b, wdCoef ε w (smE ε (rreg ε) a b (smE ε (rreg ε) b a x)) g`.

Unfold `casimir`. Simplify using `only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, Finset.sum_apply]`. Use `show ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (wdCoef ε w x)) g = _`. Simplify using `only [e1]`. Rewrite using `[← e2, datumV_casimir hP v₀ x hx, map_smul, Pi.smul_apply, smul_eq_mul])`.

Use the proof step `(by rintro f ⟨x, hx, rfl⟩; exact (wd_memLp_iff i (wdCoef_cont w (x : L2 ε))).1 (hw x hx))`. Set `Q : Submodule ℂ (smD ε (rreg ε))` to `{ carrier := {x | ∀ l, MemLp (wdF ε (wdCoef ε w (wdWord ε l x))) 2 (Formalism.REAL.muG ε)} add_mem' := by`. Introduce `x y hx hy l`. Simplify using `only [Set.mem_ofPred_eq, map_add, wdF_add] at *`. Conclude with `(hx l).add (hy l)`.

Use the proof step `zero_mem' := by`. Introduce `l`. Simplify using `only [map_zero, wdF_zero]`. Conclude with `MemLp.zero`. Use the proof step `smul_mem' := by`.

Introduce `c x hx l`. Simplify using `only [Set.mem_ofPred_eq, map_smul, wdF_smul] at *`. Conclude with `(hx l).const_smul c }`. Establish `hdat : datumV ε Ψ v₀ ≤ Q`. Introduce `x hx l`.

Take `⟨hs, hi, -⟩` from `key l [] (wdCoef ε w x) (wdCoef ε w x) ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩`. Establish `h1` using `(wd_memLp_iff i (Formalism.REAL.continuous_smooth_on_group_eval hs)).2 hi`. Establish `e : wdF ε (Formalism.REAL.Eword ε l (wdCoef ε w x)) = wdF ε (wdCoef ε w (wdWord ε l x))`. Use function extensionality and compare the values at `g`. Simplify using `only [wdF]`.

Rewrite using `[wdCoef_eword w x l _ g.2]`. Rewrite `h1` using `[e]`. Conclude with `h1`. Establish `hstab : ∀ a b, ∀ v ∈ Q, smE ε (rreg ε) a b v ∈ Q`. Introduce `a b v hv l`.

Use `show MemLp _ 2 _`. Rewrite using `[wdWord_append]`. Conclude with `hv _`. Establish `hle : genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) ≤ Q` using `sInf_le ⟨hdat, hstab⟩`. Introduce `v hv`.

Conclude with `hle hv []`.
-/
theorem wd_key (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) (i : Fin n) (w : L2 ε)
    (hw : ∀ x ∈ datumV ε Ψ v₀, MemLp (wdF ε (wdCoef ε w x)) 2 (Formalism.REAL.muG ε)) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), MemLp (wdF ε (wdCoef ε w v)) 2 (Formalism.REAL.muG ε) := by
  have hK := datumV_isKIrrHW hP hv₀
  have : FiniteDimensional ℂ (datumV ε Ψ v₀) := hK.1
  set W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) := (datumV ε Ψ v₀).map (wdCoef ε w) with hWdef
  have hWf : FiniteDimensional ℂ W := inferInstance
  have key := r0bG n ε W ((casVal lam : ℝ) : ℂ) (1 / 2) hWf (by norm_num)
    (by rintro f ⟨x, -, rfl⟩; exact wdCoef_smooth w x)
    (by
      rintro f ⟨x, hx, rfl⟩ a b hab
      exact ⟨wdCoef ε w (smE ε (rreg ε) a b x), ⟨_, hK.2.1 a b hab x hx, rfl⟩,
        fun g hg => wdCoef_eab w x a b ((mir_inUJ_iff ε g).1 hg)⟩)
    (by
      rintro f ⟨x, hx, rfl⟩ g hg
      have hg' := (mir_inUJ_iff ε g).1 hg
      have e1 : ∀ a b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (wdCoef ε w x)) g =
          wdCoef ε w (smE ε (rreg ε) a b (smE ε (rreg ε) b a x)) g := by
        intro a b
        rw [icx_eab_eq, icx_eabV_congr (fun g' hg'' => wdCoef_eab w x b a hg'') a b hg', ← icx_eab_eq]
        exact wdCoef_eab w _ a b hg'
      have e2 : wdCoef ε w (casimir (smE ε (rreg ε)) x) g =
          ∑ a, ∑ b, wdCoef ε w (smE ε (rreg ε) a b (smE ε (rreg ε) b a x)) g := by
        unfold casimir
        simp only [LinearMap.sum_apply, Module.End.mul_apply, map_sum, Finset.sum_apply]
      show ∑ a, ∑ b, Formalism.REAL.Eab ε a b (Formalism.REAL.Eab ε b a (wdCoef ε w x)) g = _
      simp only [e1]
      rw [← e2, datumV_casimir hP v₀ x hx, map_smul, Pi.smul_apply, smul_eq_mul])
    (by rintro f ⟨x, hx, rfl⟩; exact (wd_memLp_iff i (wdCoef_cont w (x : L2 ε))).1 (hw x hx))
  let Q : Submodule ℂ (smD ε (rreg ε)) :=
    { carrier := {x | ∀ l, MemLp (wdF ε (wdCoef ε w (wdWord ε l x))) 2 (Formalism.REAL.muG ε)}
      add_mem' := by
        intro x y hx hy l
        simp only [Set.mem_ofPred_eq, map_add, wdF_add] at *
        exact (hx l).add (hy l)
      zero_mem' := by
        intro l
        simp only [map_zero, wdF_zero]
        exact MemLp.zero
      smul_mem' := by
        intro c x hx l
        simp only [Set.mem_ofPred_eq, map_smul, wdF_smul] at *
        exact (hx l).const_smul c }
  have hdat : datumV ε Ψ v₀ ≤ Q := by
    intro x hx l
    obtain ⟨hs, hi, -⟩ := key l [] (wdCoef ε w x) (wdCoef ε w x) ⟨x, hx, rfl⟩ ⟨x, hx, rfl⟩
    have h1 := (wd_memLp_iff i (Formalism.REAL.continuous_smooth_on_group_eval hs)).2 hi
    have e : wdF ε (Formalism.REAL.Eword ε l (wdCoef ε w x)) = wdF ε (wdCoef ε w (wdWord ε l x)) := by
      funext g
      simp only [wdF]
      rw [wdCoef_eword w x l _ g.2]
    rw [e] at h1
    exact h1
  have hstab : ∀ a b, ∀ v ∈ Q, smE ε (rreg ε) a b v ∈ Q := by
    intro a b v hv l
    show MemLp _ 2 _
    rw [wdWord_append]
    exact hv _
  have hle : genSub (smE ε (rreg ε)) (datumV ε Ψ v₀) ≤ Q := sInf_le ⟨hdat, hstab⟩
  intro v hv
  exact hle hv []

/- English proof (translation)
Establish `hI` using `integrable_muG_of_haar ε (fun g => ‖Ψ g‖ ^ 2 * S7.hs g ^ ((2 : ℝ) / 2)) hΨw`. Establish `hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε)` using `(memLp_muG_of_haar ε Ψ 2 hP.2.2.2.2).1`. Establish `hm : AEStronglyMeasurable (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) (Formalism.REAL.muG ε)`. Unfold `wdF`. Conclude with `((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (wd_hs_cont.comp (continuous_umatA ε)))).aestronglyMeasurable).mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hΨm.norm)`.

Rewrite using `[memLp_two_iff_integrable_sq_norm hm]`. Use `hI.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[wd_norm_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, mul_comm]`.
-/
theorem wd_psi_memLp (hP : IsPsiFor ε lam T Ψ)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    MemLp (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) 2 (Formalism.REAL.muG ε) := by
  have hI := integrable_muG_of_haar ε (fun g => ‖Ψ g‖ ^ 2 * S7.hs g ^ ((2 : ℝ) / 2)) hΨw
  have hΨm : AEStronglyMeasurable (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) (Formalism.REAL.muG ε) :=
    (memLp_muG_of_haar ε Ψ 2 hP.2.2.2.2).1
  have hm : AEStronglyMeasurable (wdF ε (fun g => ((‖Ψ g‖ : ℝ) : ℂ))) (Formalism.REAL.muG ε) := by
    unfold wdF
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (wd_hs_cont.comp (continuous_umatA ε)))).aestronglyMeasurable).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hΨm.norm)
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [wd_norm_sq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, mul_comm]

/- English proof (translation)
Take `⟨u', hu'⟩` from `(mem_datumV_iff hP v₀ x').1 hx'`. Take `⟨u, hu⟩` from `(mem_datumV_iff hP v₀ x).1 hx`. Establish `hG` using `wd_psi_memLp hP hΨw`. Establish `hm : AEStronglyMeasurable (wdF ε (wdCoef ε (x' : L2 ε) x)) (Formalism.REAL.muG ε)`. Unfold `wdF`.

Conclude with `((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (wd_hs_cont.comp (continuous_umatA ε)))).mul (wdCoef_cont _ _)).aestronglyMeasurable`. Use `hG.of_le_mul (c := ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖u'‖ * ‖u‖) hm (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [wdF, wdCoef_apply, hu', hu]`. Establish `h3 : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2` using `by positivity`. Rewrite using `[formulaF hgap hP hv₀ g.2 u u']`.

Simplify using `only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h3]`. Establish `h1 : ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖ ≤ ‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖)` using `(norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((Ψ _).le_opNorm u) (norm_nonneg _))`. Establish `h2 : 0 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g))` using `Real.sqrt_nonneg _`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wd_datum_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (x' : smD ε (rreg ε)) (hx' : x' ∈ datumV ε Ψ v₀) (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (x' : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  obtain ⟨u', hu'⟩ := (mem_datumV_iff hP v₀ x').1 hx'
  obtain ⟨u, hu⟩ := (mem_datumV_iff hP v₀ x).1 hx
  have hG := wd_psi_memLp hP hΨw
  have hm : AEStronglyMeasurable (wdF ε (wdCoef ε (x' : L2 ε) x)) (Formalism.REAL.muG ε) := by
    unfold wdF
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (wd_hs_cont.comp (continuous_umatA ε)))).mul (wdCoef_cont _ _)).aestronglyMeasurable
  refine hG.of_le_mul (c := ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖u'‖ * ‖u‖) hm (Filter.Eventually.of_forall fun g => ?_)
  simp only [wdF, wdCoef_apply, hu', hu]
  have h3 : 0 ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 := by positivity
  rw [formulaF hgap hP hv₀ g.2 u u']
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg h3]
  have h1 : ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖ ≤ ‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ((Ψ _).le_opNorm u) (norm_nonneg _))
  have h2 : 0 ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) := Real.sqrt_nonneg _
  calc Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖inner ℂ u' (Ψ (Formalism.MainNotions.S.umat g) u)‖)
      ≤ Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) * (‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * (‖u'‖ * (‖Ψ (Formalism.MainNotions.S.umat g)‖ * ‖u‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) h2
    _ = _ := by ring

/- English proof (translation)
Establish `h` using `wd_key hP hv₀ i (x : L2 ε) (fun y hy => wd_datum_datum hgap hP hv₀ hΨw x hx y hy) w hw`. Establish `hinv` using `(h.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star`. Establish `e : star (wdF ε (wdCoef ε (x : L2 ε) w) ∘ Inv.inv) = wdF ε (wdCoef ε (w : L2 ε) x)`. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.star_apply, Function.comp_apply, wdF, wdCoef_apply, star_mul', RCLike.star_def, Complex.conj_ofReal]`.

Rewrite using `[wd_hs_inv, inner_conj_symm, wd_rreg_adj, inv_inv]`. Rewrite `hinv` using `[e]`. Conclude with `hinv`.
-/
theorem wd_gen_datum (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ)
    (i : Fin n) (w : smD ε (rreg ε)) (hw : w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀))
    (x : smD ε (rreg ε)) (hx : x ∈ datumV ε Ψ v₀) :
    MemLp (wdF ε (wdCoef ε (w : L2 ε) x)) 2 (Formalism.REAL.muG ε) := by
  have h := wd_key hP hv₀ i (x : L2 ε) (fun y hy => wd_datum_datum hgap hP hv₀ hΨw x hx y hy) w hw
  have hinv := (h.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  have e : star (wdF ε (wdCoef ε (x : L2 ε) w) ∘ Inv.inv) = wdF ε (wdCoef ε (w : L2 ε) x) := by
    funext g
    simp only [Pi.star_apply, Function.comp_apply, wdF, wdCoef_apply, star_mul', RCLike.star_def,
      Complex.conj_ofReal]
    rw [wd_hs_inv, inner_conj_symm, wd_rreg_adj, inv_inv]
  rw [e] at hinv
  exact hinv

end ReciprocityTheory.ChartRestriction.DS.G2
