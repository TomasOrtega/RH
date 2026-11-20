import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_add_smul levi_zero continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh isPotential_ofFun)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

/- English proof (translation)
The claim follows from `WithTop.coe_le_coe.mpr le_top`.
-/
theorem two_le_top_gms : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

variable {e : ℕ} {W : Type} [TopologicalSpace W] {A : FinHolAtlas e W}

def formDiff (Om th : LocPot W) : LocPot W := Om + th.rsmul (-1)

/- English proof (translation)
The claim follows from `ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ hO (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ _ hth)`.
-/
theorem isPotential_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th) :
    IsPotential A (formDiff Om th) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd A _ _ hO (ReciprocityTheory.AnForm.M.isPotentialRsmul A _ _ hth)

/- English proof (translation)
Introduce `x j y hy w`. Establish `h1` using `(ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A Om hO x j ⟨hy.1, hy.2.1⟩).of_le two_le_top_gms`. Establish `h2` using `(ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A th hth x j ⟨hy.1, hy.2.2⟩).of_le two_le_top_gms`. Establish `hl` using `levi_add_smul (-1) h1 h2 w`. Establish `hle'` using `hle x j y ⟨hy.1, ⟨Set.mem_univ _, hy.2.2⟩, hy.2.1⟩ w`.

Establish `heq : (formDiff Om th).φ x ∘ (A.chart j).symm = fun z => (Om.φ x ∘ (A.chart j).symm) z + (-1) * (th.φ x ∘ (A.chart j).symm) z` using `rfl`. Rewrite using `[heq, hl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isPsh_formDiff {Om th : LocPot W} (hO : IsPotential A Om) (hth : IsPotential A th)
    (hle : LeviLe A Set.univ 1 th 1 Om) : IsPsh A (formDiff Om th) := by
  intro x j y hy w
  have h1 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A Om hO x j
    ⟨hy.1, hy.2.1⟩).of_le two_le_top_gms
  have h2 := (ReciprocityTheory.AnForm.M.contDiffAt_of_isPotential A th hth x j
    ⟨hy.1, hy.2.2⟩).of_le two_le_top_gms
  have hl := levi_add_smul (-1) h1 h2 w
  have hle' := hle x j y ⟨hy.1, ⟨Set.mem_univ _, hy.2.2⟩, hy.2.1⟩ w
  have heq : (formDiff Om th).φ x ∘ (A.chart j).symm =
      fun z => (Om.φ x ∘ (A.chart j).symm) z + (-1) * (th.φ x ∘ (A.chart j).symm) z := rfl
  rw [heq, hl]
  linarith

/- English proof (translation)
Use `show th.φ x y + (Om.φ x y + -1 * th.φ x y) = Om.φ x y`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_formDiff_φ (Om th : LocPot W) (x y : W) : (th + formDiff Om th).φ x y = Om.φ x y := by
  show th.φ x y + (Om.φ x y + -1 * th.φ x y) = Om.φ x y
  ring

/- English proof (translation)
Introduce `x j y hy w`. Establish `hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x)` using `(A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)`. Take `⟨F, hF⟩ : ∃ F, F = P.φ x ∘ (A.chart j).symm` from `⟨_, rfl⟩`. Establish `hFs : ContDiffOn ℝ 2 F ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x)`. Rewrite using `[hF]`.

Conclude with `(hP.1 x j).of_le two_le_top_gms`. Rewrite using `[← hF]`. Establish `hpair : ContinuousAt (fun p : (Fin e → ℂ) × (Fin e → ℂ) => levi F p.1 p.2) (y, w)` using `(continuousOn_levi hOo hFs).continuousAt (prod_mem_nhds (hOo.mem_nhds hy) Filter.univ_mem)`. Establish `hc : ContinuousAt (fun z => levi F z w) y` using `hpair.comp (f := fun z => (z, w)) (continuousAt_id.prodMk continuousAt_const)`. Assume the negation of the conclusion as `hneg`.

Rewrite `hneg` using `[not_le]`. Establish `hN : {z | levi F z w < 0} ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) ∈ 𝓝 y` using `Filter.inter_mem (hc.preimage_mem_nhds (Iio_mem_nhds hneg)) (hOo.mem_nhds hy)`. Take `⟨V, hVN, hVo, hyV⟩` from `mem_nhds_iff.1 hN`. Establish `hVt : V ⊆ (A.chart j).target` using `fun z hz => (hVN hz).2.1`. Establish `himg : IsOpen ((A.chart j).symm '' V)`.

Use `(A.chart j).symm.isOpen_image_source_inter hVo` as an intermediate fact. Rewrite `this` using `[OpenPartialHomeomorph.symm_source, Set.inter_eq_right.2 hVt]`. Then use the resulting hypothesis. Take `⟨p, ⟨z, hzV, rfl⟩, hpY⟩` from `hd.inter_open_nonempty _ himg ⟨_, y, hyV, rfl⟩`. Establish `h0` using `hn x j z ⟨(hVN hzV).2.1, hpY, (hVN hzV).2.2⟩ w`. Rewrite `h0` using `[← hF]`.

Conclude with `absurd (hVN hzV).1 (not_lt.2 h0)`.
-/
theorem isPsh_of_formNonneg_dense {P : LocPot W} {Yo : Set W} (hP : IsPotential A P)
    (hd : Dense Yo) (hn : FormNonneg A Yo P) : IsPsh A P := by
  intro x j y hy w
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (P.isOpen_U x)
  obtain ⟨F, hF⟩ : ∃ F, F = P.φ x ∘ (A.chart j).symm := ⟨_, rfl⟩
  have hFs : ContDiffOn ℝ 2 F ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) := by
    rw [hF]
    exact (hP.1 x j).of_le two_le_top_gms
  rw [← hF]
  have hpair : ContinuousAt (fun p : (Fin e → ℂ) × (Fin e → ℂ) => levi F p.1 p.2) (y, w) :=
    (continuousOn_levi hOo hFs).continuousAt (prod_mem_nhds (hOo.mem_nhds hy) Filter.univ_mem)
  have hc : ContinuousAt (fun z => levi F z w) y :=
    hpair.comp (f := fun z => (z, w)) (continuousAt_id.prodMk continuousAt_const)
  by_contra hneg
  rw [not_le] at hneg
  have hN : {z | levi F z w < 0} ∩
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) ∈ 𝓝 y :=
    Filter.inter_mem (hc.preimage_mem_nhds (Iio_mem_nhds hneg)) (hOo.mem_nhds hy)
  obtain ⟨V, hVN, hVo, hyV⟩ := mem_nhds_iff.1 hN
  have hVt : V ⊆ (A.chart j).target := fun z hz => (hVN hz).2.1
  have himg : IsOpen ((A.chart j).symm '' V) := by
    have := (A.chart j).symm.isOpen_image_source_inter hVo
    rwa [OpenPartialHomeomorph.symm_source, Set.inter_eq_right.2 hVt] at this
  obtain ⟨p, ⟨z, hzV, rfl⟩, hpY⟩ := hd.inter_open_nonempty _ himg ⟨_, y, hyV, rfl⟩
  have h0 := hn x j z ⟨(hVN hzV).2.1, hpY, (hVN hzV).2.2⟩ w
  rw [← hF] at h0
  exact absurd (hVN hzV).1 (not_lt.2 h0)

/- English proof (translation)
Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using h0`. Simplify using `using h j`.
-/
theorem forall_cons_of {n : ℕ} {p : LocPot W → Prop} {P : LocPot W} {Φ : Fin n → LocPot W}
    (h0 : p P) (h : ∀ i, p (Φ i)) : ∀ i, p ((Fin.cons P Φ : Fin (n + 1) → LocPot W) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using h0
  · simpa using h j

namespace UIData

variable {D : ℕ} (S : UIData D W)

/- English proof (translation)
The claim follows from `ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form b t ht hℓ).1.th_pot (isPotential_ofFun S.A _ (S.form b t ht hℓ).2)`.
-/
theorem T_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPotential S.A (S.T t b) :=
  ReciprocityTheory.AnForm.M.isPotentialAdd S.A _ _ (S.form b t ht hℓ).1.th_pot
    (isPotential_ofFun S.A _ (S.form b t ht hℓ).2)

/- English proof (translation)
Establish `h` using `interior_eq_empty_iff_dense_compl.1 S.bd_interior`. Rewrite `h` using `[compl_compl]`. Then use the resulting hypothesis.
-/
theorem dense_Yo : Dense S.Yo := by
  have h := interior_eq_empty_iff_dense_compl.1 S.bd_interior
  rwa [compl_compl] at h

/- English proof (translation)
The claim follows from `isPsh_of_formNonneg_dense (S.T_isPotential ht hℓ b) S.dense_Yo (S.form b t ht hℓ).1.nonneg`.
-/
theorem T_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (b : Fin (D + 1)) :
    IsPsh S.A (S.T t b) :=
  isPsh_of_formNonneg_dense (S.T_isPotential ht hℓ b) S.dense_Yo (S.form b t ht hℓ).1.nonneg

/- English proof (translation)
Unfold `rest restForms`. Use `split_ifs`. Conclude with `S.T_isPotential ht hℓ _`. Conclude with `S.Om.isPot`.
-/
theorem rest_isPotential {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPotential S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPotential ht hℓ _
  · exact S.Om.isPot

/- English proof (translation)
Unfold `rest restForms`. Use `split_ifs`. Conclude with `S.T_isPsh ht hℓ _`. Conclude with `S.Om.isPsh`.
-/
theorem rest_isPsh {t : ℝ} (ht : 0 < t) (hℓ : S.ell₀ ≤ ell t) (a : ℕ) (i : Fin D) :
    IsPsh S.A (S.rest a t i) := by
  unfold rest restForms
  split_ifs
  · exact S.T_isPsh ht hℓ _
  · exact S.Om.isPsh

end UIData

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[Fin.cycleRange_symm_zero]`. Simplify using `only [Function.comp_apply, Fin.cons_succ, Fin.cycleRange_symm_succ]`. Distinguish the cases in `hj : (j : ℕ) < a`.

Rewrite using `[Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hj)]`. Simplify using `only [mixedForms, restForms, Fin.val_castSucc, hj, if_true]`. Rewrite using `[if_pos (by omega)]`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]`. Simplify using `only [mixedForms, restForms, Fin.val_succ, hj, if_false]`.

Rewrite using `[if_neg (by omega)]`.
-/
theorem mixedForms_cycle {D : ℕ} (Om : LocPot W) (T : Fin (D + 1) → LocPot W) (a : ℕ)
    (ha : a < D + 1) (b : ℕ) (hb : b = a ∨ b = a + 1) :
    mixedForms Om T b ∘ (Fin.cycleRange (⟨a, ha⟩ : Fin (D + 1))).symm =
      Fin.cons (mixedForms Om T b ⟨a, ha⟩) (restForms Om T a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.cycleRange_symm_zero]
  · simp only [Function.comp_apply, Fin.cons_succ, Fin.cycleRange_symm_succ]
    by_cases hj : (j : ℕ) < a
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hj)]
      simp only [mixedForms, restForms, Fin.val_castSucc, hj, if_true]
      rw [if_pos (by omega)]
    · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simp; omega)]
      simp only [mixedForms, restForms, Fin.val_succ, hj, if_false]
      rw [if_neg (by omega)]

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
