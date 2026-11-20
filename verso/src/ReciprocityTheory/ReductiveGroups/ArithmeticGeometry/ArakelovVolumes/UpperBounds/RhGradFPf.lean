import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set Matrix NumberField ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eΨ : Fin X.Ψ.card ≃ X.Ψ := X.Ψ.equivFin.symm

def Zmap (z : V (nd X)) : V (nD X.Ψ.card X.p0 (r - X.p0)) :=
  WithLp.toLp 2 fun j => ExF.Zt X z (eΨ X (finProdFinEquiv.symm j).1)
    (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).1 (finProdFinEquiv.symm (finProdFinEquiv.symm j).2).2

/- English proof (translation)
Use extensionality with `a b`. Express the relevant statement in the definitionally equal form `ExF.Zt X z (eΨ X (finProdFinEquiv.symm (finProdFinEquiv (k, finProdFinEquiv (a, b)))).1) _ _ = _`. Simplify using `only [Equiv.symm_apply_apply]`.
-/
theorem Zof_Zmap (z : V (nd X)) (k : Fin X.Ψ.card) : Zof (Zmap X z) k = ExF.Zt X z (eΨ X k) := by
  ext a b
  change ExF.Zt X z (eΨ X (finProdFinEquiv.symm (finProdFinEquiv (k, finProdFinEquiv (a, b)))).1) _ _ = _
  simp only [Equiv.symm_apply_apply]

/- English proof (translation)
Unfold `ExF.nM`. Simplify using `only [mat, Matrix.of_apply, nmat]`. Use `split_ifs`. Use `first`. Consider the case `exact ((contDiff_piLp _).mp contDiff_id) _`.

Consider the case `fun_prop`. Conclude with `contDiff_const`. Conclude with `contDiff_const`.
-/
private theorem contDiff_nM_apply (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun z : V (nd X) => ExF.nM X z τ a b := by
  unfold ExF.nM
  simp only [mat, Matrix.of_apply, nmat]
  split_ifs
  · first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  · exact contDiff_const
  · exact contDiff_const

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `i _`. Express the relevant statement in the definitionally equal form `nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1`. Simplify using `[nmat]`.

Introduce `i j hij`. Establish `hlt : i < j` using `OrderDual.toDual_lt_toDual.mp hij`. Rewrite `hlt` using `[Fin.lt_def]`. Express the relevant statement in the definitionally equal form `nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0`. Establish `h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i)`.

Rewrite using `[Fin.lt_def]`. Simplify using `only [Fin.coe_castLE]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j`. Introduce `h`.

Rewrite `h` using `[Fin.ext_iff]`. Simplify using `only [Fin.coe_castLE] at h`. Use linear arithmetic over natural numbers and integers. Simplify using `only [nmat, dif_neg h1, if_neg h2]`.
-/
private theorem det_n1_eq_one (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro i _
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le i) = 1
    simp [nmat]
  · intro i j hij
    have hlt : i < j := OrderDual.toDual_lt_toDual.mp hij
    rw [Fin.lt_def] at hlt
    change nmat X z τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j) = 0
    have h1 : ¬ (Fin.castLE X.p0_le j < Fin.castLE X.p0_le i) := by
      rw [Fin.lt_def]; simp only [Fin.coe_castLE]; omega
    have h2 : Fin.castLE X.p0_le i ≠ Fin.castLE X.p0_le j := by
      intro h; rw [Fin.ext_iff] at h; simp only [Fin.coe_castLE] at h; omega
    simp only [nmat, dif_neg h1, if_neg h2]

/- English proof (translation)
Rewrite using `[Matrix.inv_def, det_n1_eq_one, Ring.inverse_one, one_smul]`.
-/
private theorem inv_n1_eq_adjugate (z : V (nd X)) (τ : X.Ψ) : (ExF.n1 X z τ)⁻¹ = (ExF.n1 X z τ).adjugate := by
  rw [Matrix.inv_def, det_n1_eq_one, Ring.inverse_one, one_smul]

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Use `ContDiff.sum fun σ _ => contDiff_const.mul ?_` and prove the remaining obligations. Use `first`. Consider the case `exact contDiff_prod fun i _ => hM _ _`. Consider the case `fun_prop`.
-/
private theorem contDiff_det_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) : ContDiff ℂ ∞ fun z => (M z).det := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  first
  | exact contDiff_prod fun i _ => hM _ _
  | fun_prop

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Apply `contDiff_det_of_contDiff_entries` to reduce the goal to its premises. Introduce `i j`. Simplify using `only [Matrix.updateRow_apply]`. Use `split_ifs`.

Conclude with `contDiff_const`. Conclude with `hM i j`.
-/
private theorem contDiff_adjugate_apply_of_contDiff_entries {n : ℕ} (M : V (nd X) → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, ContDiff ℂ ∞ fun z => M z i j) (a b : Fin n) :
    ContDiff ℂ ∞ fun z => (M z).adjugate a b := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det_of_contDiff_entries
  intro i j
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact hM i j

/- English proof (translation)
Establish `hn1 : ∀ τ : X.Ψ, ∀ i j, ContDiff ℂ ∞ fun z : V (nd X) => ExF.n1 X z τ i j` using `fun τ i j => contDiff_nM_apply X τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)`. Establish `hW : ∀ τ : X.Ψ, ∀ b c, ContDiff ℂ ∞ fun z : V (nd X) => ExF.Wm X z τ b c` using `fun τ b c => contDiff_nM_apply X τ (ExF.qI X b) (Fin.castLE X.p0_le c)`. Use `(contDiff_piLp _).mpr fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ContDiff ℂ ∞ fun z : V (nd X) => ExF.Zt X z _ _ _`. Simplify using `only [ExF.Zt, Matrix.transpose_apply, inv_n1_eq_adjugate, Matrix.mul_apply]`.

Conclude with `ContDiff.sum fun c _ => (hW _ _ _).mul (contDiff_adjugate_apply_of_contDiff_entries X (fun z => ExF.n1 X z _) (hn1 _) _ _)`.
-/
theorem Zmap_contDiff : ContDiff ℂ ∞ (Zmap X) := by
  have hn1 : ∀ τ : X.Ψ, ∀ i j, ContDiff ℂ ∞ fun z : V (nd X) => ExF.n1 X z τ i j :=
    fun τ i j => contDiff_nM_apply X τ (Fin.castLE X.p0_le i) (Fin.castLE X.p0_le j)
  have hW : ∀ τ : X.Ψ, ∀ b c, ContDiff ℂ ∞ fun z : V (nd X) => ExF.Wm X z τ b c :=
    fun τ b c => contDiff_nM_apply X τ (ExF.qI X b) (Fin.castLE X.p0_le c)
  refine (contDiff_piLp _).mpr fun j => ?_
  change ContDiff ℂ ∞ fun z : V (nd X) => ExF.Zt X z _ _ _
  simp only [ExF.Zt, Matrix.transpose_apply, inv_n1_eq_adjugate, Matrix.mul_apply]
  exact ContDiff.sum fun c _ => (hW _ _ _).mul (contDiff_adjugate_apply_of_contDiff_entries X (fun z => ExF.n1 X z _) (hn1 _) _ _)

/- English proof (translation)
Rewrite using `[ExF.rhF_eq_sum X x0 ho, rh]`. Use `congr 1`. Rewrite using `[← (eΨ X).sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Zof_Zmap]`.

Establish `hpd` using `(ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)`. Rewrite using `[show (1 - ExF.Zt X z (eΨ X k) * (ExF.Zt X z (eΨ X k))ᴴ) = ExF.Am X z (eΨ X k) from rfl, ExF.norm_of_pos hpd.det_pos]`.
-/
theorem rh_Zmap (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    rh (Zmap X z) = rhF X x0 z := by
  rw [ExF.rhF_eq_sum X x0 ho, rh]
  congr 1
  rw [← (eΨ X).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Zof_Zmap]
  have hpd := (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)
  rw [show (1 - ExF.Zt X z (eΨ X k) * (ExF.Zt X z (eΨ X k))ᴴ) = ExF.Am X z (eΨ X k) from rfl,
    ExF.norm_of_pos hpd.det_pos]

/- English proof (translation)
Introduce `k`. Rewrite using `[Zof_Zmap]`. Conclude with `(ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)`.
-/
theorem Zmap_mem (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Zmap X z ∈ Dset X.Ψ.card X.p0 (r - X.p0) := by
  intro k
  rw [Zof_Zmap]
  exact (ExF.mem_OmF_iff X x0 ho z).1 hz (eΨ X k)

/- English proof (translation)
Establish `hZ : ∀ k a b, ContDiff ℝ 2 fun w : V (nD f p q) => Zof w k a b`. Introduce `k a b`. Simplify using `only [Zof, Matrix.of_apply]`. Use `first`. Consider the case `exact ((contDiff_piLp _).mp contDiff_id) _`.

Consider the case `fun_prop`. Establish `hM : ∀ k i j, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ : Matrix (Fin p) (Fin p) ℂ) i j`. Introduce `k i j`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]`. Use `contDiff_const.sub (ContDiff.sum fun l _ => (hZ k i l).mul ?_)` and prove the remaining obligations.

Establish `h` using `hZ k j l`. Use `first`. Consider the case `exact h.star`. Consider the case `exact Complex.conjCLE.contDiff.comp h`. Consider the case `fun_prop`.

Establish `hdet : ∀ k, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ).det`. Introduce `k`. Simplify using `only [Matrix.det_apply']`. Use `ContDiff.sum fun σ _ => contDiff_const.mul ?_` and prove the remaining obligations. Use `first`.

Consider the case `exact contDiff_prod fun i _ => hM k _ _`. Consider the case `fun_prop`. Establish `hpos : ∀ k, 0 < ((1 - Zof v k * (Zof v k)ᴴ).det).re`. Introduce `k`. Establish `h` using `(hv k).det_pos`.

Use `first`. Consider the case `exact (Complex.pos_iff.mp h).1`. Consider the case `simpa using (Complex.lt_def.mp h).1`. Establish `hlog : ∀ k, ContDiffAt ℝ 2 (fun w : V (nD f p q) => Real.log ((1 - Zof w k * (Zof w k)ᴴ).det.re)) v`. Introduce `k`.

Establish `hre : ContDiff ℝ 2 fun w : V (nD f p q) => ((1 - Zof w k * (Zof w k)ᴴ).det).re` using `Complex.reCLM.contDiff.comp (hdet k)`. Conclude with `(Real.contDiffAt_log.mpr (hpos k).ne').comp v hre.contDiffAt`. Establish `hsum : ContDiffAt ℝ 2 (fun w : V (nD f p q) => rh w) v`. Unfold `rh`. Conclude with `(ContDiffAt.sum fun k _ => hlog k).neg`.

Conclude with `Complex.ofRealCLM.contDiff.contDiffAt.comp v hsum`.
-/
theorem rh_contDiffAt {f p q : ℕ} {v : V (nD f p q)} (hv : v ∈ Dset f p q) :
    ContDiffAt ℝ 2 (fun w : V (nD f p q) => ((rh w : ℝ) : ℂ)) v := by
  have hZ : ∀ k a b, ContDiff ℝ 2 fun w : V (nD f p q) => Zof w k a b := by
    intro k a b
    simp only [Zof, Matrix.of_apply]
    first
    | exact ((contDiff_piLp _).mp contDiff_id) _
    | fun_prop
  have hM : ∀ k i j, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ : Matrix (Fin p) (Fin p) ℂ) i j := by
    intro k i j
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine contDiff_const.sub (ContDiff.sum fun l _ => (hZ k i l).mul ?_)
    have h := hZ k j l
    first
    | exact h.star
    | exact Complex.conjCLE.contDiff.comp h
    | fun_prop
  have hdet : ∀ k, ContDiff ℝ 2 fun w : V (nD f p q) => (1 - Zof w k * (Zof w k)ᴴ).det := by
    intro k
    simp only [Matrix.det_apply']
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
    | exact contDiff_prod fun i _ => hM k _ _
    | fun_prop
  have hpos : ∀ k, 0 < ((1 - Zof v k * (Zof v k)ᴴ).det).re := by
    intro k
    have h := (hv k).det_pos
    first
    | exact (Complex.pos_iff.mp h).1
    | simpa using (Complex.lt_def.mp h).1
  have hlog : ∀ k, ContDiffAt ℝ 2
      (fun w : V (nD f p q) => Real.log ((1 - Zof w k * (Zof w k)ᴴ).det.re)) v := by
    intro k
    have hre : ContDiff ℝ 2 fun w : V (nD f p q) => ((1 - Zof w k * (Zof w k)ᴴ).det).re :=
      Complex.reCLM.contDiff.comp (hdet k)
    exact (Real.contDiffAt_log.mpr (hpos k).ne').comp v hre.contDiffAt
  have hsum : ContDiffAt ℝ 2 (fun w : V (nD f p q) => rh w) v := by
    unfold rh
    exact (ContDiffAt.sum fun k _ => hlog k).neg
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp v hsum

end

/- English proof (translation)
Introduce `r X x0 ho z hz ξ`. Establish `hU` using `ExF.isOpen_OmF X x0`. Establish `hZ : ContDiff ℂ ∞ (Zmap X)` using `Zmap_contDiff X`. Establish `hZd : HasFDerivAt (Zmap X) (fderiv ℂ (Zmap X) z) z` using `(hZ.differentiable (by simp) z).hasFDerivAt`. Establish `hmem` using `Zmap_mem X x0 ho hz`.

Establish `hg` using `rh_contDiffAt hmem`. Establish `hev : (fun w : V (nd X) => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z] (fun w : V (nD X.Ψ.card X.p0 (r - X.p0)) => ((rh w : ℝ) : ℂ)) ∘ Zmap X` using `by filter_upwards [hU.mem_nhds hz] with w hw`. Simplify using `only [Function.comp_apply, rh_Zmap X x0 ho hw]`. Establish `h1 : ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j = ∑ a, wd _ a (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) * fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) a`. Rewrite using `[← gc_sum_wd_comp _ _ _ _ _ z (hg.differentiableAt (by norm_num)) hZd ξ]`.

Conclude with `Finset.sum_congr rfl fun j _ => by rw [wd_congr (j := j) hev]`. Establish `h2 : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ = leviV _ (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) (fun b => fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) b)`. Rewrite using `[Y.fc_leviV_congr (nd X) _ _ z hev]`. Conclude with `gc_leviV_comp _ _ _ _ Set.univ isOpen_univ z trivial (hZ.contDiffOn.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) hg ξ`. Rewrite using `[h1, h2]`.

Conclude with `RhGradStatement_holds _ _ _ _ hmem _`.
-/
theorem rhGradF_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : RhGradFStatement (E := E) := by
  intro r X x0 ho z hz ξ
  have hU := ExF.isOpen_OmF X x0
  have hZ : ContDiff ℂ ∞ (Zmap X) := Zmap_contDiff X
  have hZd : HasFDerivAt (Zmap X) (fderiv ℂ (Zmap X) z) z :=
    (hZ.differentiable (by simp) z).hasFDerivAt
  have hmem := Zmap_mem X x0 ho hz
  have hg := rh_contDiffAt hmem
  have hev : (fun w : V (nd X) => ((rhF X x0 w : ℝ) : ℂ)) =ᶠ[𝓝 z]
      (fun w : V (nD X.Ψ.card X.p0 (r - X.p0)) => ((rh w : ℝ) : ℂ)) ∘ Zmap X := by
    filter_upwards [hU.mem_nhds hz] with w hw
    simp only [Function.comp_apply, rh_Zmap X x0 ho hw]
  have h1 : ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j =
      ∑ a, wd _ a (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) *
        fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) a := by
    rw [← gc_sum_wd_comp _ _ _ _ _ z (hg.differentiableAt (by norm_num)) hZd ξ]
    exact Finset.sum_congr rfl fun j _ => by rw [wd_congr (j := j) hev]
  have h2 : leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ =
      leviV _ (fun w => ((rh w : ℝ) : ℂ)) (Zmap X z) (fun b => fderiv ℂ (Zmap X) z (WithLp.toLp 2 ξ) b) := by
    rw [Y.fc_leviV_congr (nd X) _ _ z hev]
    exact gc_leviV_comp _ _ _ _ Set.univ isOpen_univ z trivial (hZ.contDiffOn.of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) hg ξ
  rw [h1, h2]
  exact RhGradStatement_holds _ _ _ _ hmem _

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

/- English proof (translation)
The claim follows from `RGF.rhGradF_holds`.
-/
theorem RhGradFStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    RhGradFStatement (E := E) := RGF.rhGradF_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
