import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EpsilonLeHalf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorus

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

/- English proof (translation)
Take `⟨hP, hGT, -⟩` from `hx`. Introduce `E _ _ _ X DF P I hI c hc σ x0 u hx0 hu n hn hun hc6`. Conclude with `ct_core hP hGT hA hS hI c hc σ x0 u hx0 hu n hn hun hc6`.
-/
theorem colTorus (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColTorusStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ x0 u hx0 hu n hn hun hc6
  exact ct_core hP hGT hA hS hI c hc σ x0 u hx0 hu n hn hun hc6

/- English proof (translation)
Take `⟨hP, hGT, -⟩` from `hx`. Introduce `E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI`. Conclude with `cab_core hP hGT hA hS hI c hc σ ξ hξ1 hξI`.
-/
theorem colAbel (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColAbelStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI c hc σ ξ _ hξ1 hξI
  exact cab_core hP hGT hA hS hI c hc σ ξ hξ1 hξI

/- English proof (translation)
Take `⟨hP, hGT, -⟩` from `hx`. Introduce `E _ _ _ X DF P I hI`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hM : 0 ≤ M1 (E` using `E) P.m := by`. Unfold `M1 PT.rd`.

Check the signs of the components of the expression. Establish `hu0 : IsU I (0 : Vsp X.dim) 0` using `⟨Submodule.zero_mem _, fun a _ => by simp [Hf]⟩`. Take `⟨s', hs', ζ, hζ, hd, hl⟩` from `ct_core hP hGT hA hS hI 0 (Nat.zero_le _) σ 0 0 (Submodule.zero_mem _) hu0 1 le_rfl (by norm_num) (fun y _ uy _ => by simpa using mul_nonneg hM (sq_nonneg ‖uy‖))`. Establish `h0` using `hd Fin.elim0 (fun k => k.elim0)`. Simplify using `only [d1, iteratedFDeriv_zero_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h0`.

Use `⟨s', hs', ?_, by simpa using hl⟩` and prove the remaining obligations. Establish `h1` using `norm_sub_norm_le ζ (s' 0)`. Rewrite `h1` using `[norm_sub_rev]`. Establish `h2` using `epsilon_le_half P`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem colEmpty (hx : Ext.All) (hA : PropAStatement) (hS : GSupStatement) : ColEmptyStatement := by
  obtain ⟨hP, hGT, -⟩ := hx
  intro E _ _ _ X DF P I hI
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hM : 0 ≤ M1 (E := E) P.m := by
    unfold M1 PT.rd
    positivity
  have hu0 : IsU I (0 : Vsp X.dim) 0 := ⟨Submodule.zero_mem _, fun a _ => by simp [Hf]⟩
  obtain ⟨s', hs', ζ, hζ, hd, hl⟩ := ct_core hP hGT hA hS hI 0 (Nat.zero_le _) σ 0 0
    (Submodule.zero_mem _) hu0 1 le_rfl (by norm_num)
    (fun y _ uy _ => by simpa using mul_nonneg hM (sq_nonneg ‖uy‖))
  have h0 := hd Fin.elim0 (fun k => k.elim0)
  simp only [d1, iteratedFDeriv_zero_apply, pow_zero, Finset.univ_eq_empty, Finset.prod_empty,
    mul_one] at h0
  refine ⟨s', hs', ?_, by simpa using hl⟩
  have h1 := norm_sub_norm_le ζ (s' 0)
  rw [norm_sub_rev] at h1
  have h2 := epsilon_le_half P
  linarith

end ReciprocityTheory.ChartRestriction.G.I2
